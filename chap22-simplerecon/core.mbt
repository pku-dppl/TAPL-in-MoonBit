///|
fn is_numerical(self : Term) -> Bool {
  match self {
    Zero(_) => true
    Succ(_, t1) => t1.is_numerical()
    _ => false
  }
}

///|
fn is_val(self : Term) -> Bool {
  match self {
    True(_) => true
    False(_) => true
    Abs(_) => true
    _ => self.is_numerical()
  }
}

///|
type! NoRuleApplies

///|
fn eval1(self : Term, ctx : Context) -> Term!NoRuleApplies {
  match self {
    True(_) => raise NoRuleApplies
    False(_) => raise NoRuleApplies
    If(info, t1, t2, t3) =>
      if t1.is_val() {
        match t1 {
          True(_) => t2
          False(_) => t3
          _ => raise NoRuleApplies
        }
      } else {
        let t1_prime = t1.eval1!(ctx)
        If(info, t1_prime, t2, t3)
      }
    Zero(_) => raise NoRuleApplies
    Succ(info, t1) =>
      if t1.is_val() {
        raise NoRuleApplies
      } else {
        let t1_prime = t1.eval1!(ctx)
        Succ(info, t1_prime)
      }
    Pred(info, t1) =>
      if t1.is_val() {
        match t1 {
          Zero(_) => Zero(UNKNOWN)
          Succ(_, t11) =>
            if t11.is_numerical() {
              t11
            } else {
              raise NoRuleApplies
            }
          _ => raise NoRuleApplies
        }
      } else {
        let t1_prime = t1.eval1!(ctx)
        Pred(info, t1_prime)
      }
    IsZero(info, t1) =>
      if t1.is_val() {
        match t1 {
          Zero(_) => True(UNKNOWN)
          Succ(_, t11) =>
            if t11.is_numerical() {
              False(UNKNOWN)
            } else {
              raise NoRuleApplies
            }
          _ => raise NoRuleApplies
        }
      } else {
        let t1_prime = t1.eval1!(ctx)
        IsZero(info, t1_prime)
      }
    Var(_, x, _) =>
      match ctx.get_binding(x) {
        TmAbb(t, _) => t
        _ => raise NoRuleApplies
      }
    Abs(_) => raise NoRuleApplies
    App(info, t1, t2) =>
      if t1.is_val() {
        if t2.is_val() {
          match t1 {
            Abs(_, _, _, t12) => t12.subst_top(t2)
            _ => raise NoRuleApplies
          }
        } else {
          let t2_prime = t2.eval1!(ctx)
          App(info, t1, t2_prime)
        }
      } else {
        let t1_prime = t1.eval1!(ctx)
        App(info, t1_prime, t2)
      }
  }
}

///|
fn eval(self : Term, ctx : Context) -> Term {
  loop self {
    t =>
      try {
        continue t.eval1!(ctx)
      } catch {
        NoRuleApplies => break t
      }
  }
}

///|
struct UVarGen {
  mut cur : Int
}

///|
fn UVarGen::new() -> UVarGen {
  { cur: 0 }
}

///|
fn UVarGen::next(self : UVarGen) -> String {
  let uvar = "?X\{self.cur}"
  self.cur += 1
  uvar
}

///|
type Constr @deque.T[(Type, Type)]

///|
impl Show for Constr with output(self, logger) {
  logger.write_string("{")
  for i, p in self._ {
    if i > 0 {
      logger.write_string(", ")
    }
    p.0.output(false, logger)
    logger.write_string("=")
    p.1.output(false, logger)
  }
  logger.write_string("}")
}

///|
fn Constr::new() -> Constr {
  @deque.new()
}

///|
fn Constr::push_back(self : Constr, p : (Type, Type)) -> Unit {
  self._.push_back(p)
}

///|
fn Constr::push_front(self : Constr, p : (Type, Type)) -> Unit {
  self._.push_front(p)
}

///|
fn Constr::pop_front(self : Constr) -> (Type, Type)? {
  self._.pop_front()
}

///|
fn Constr::append(self : Constr, other : Constr) -> Unit {
  for p in other._ {
    self.push_back(p)
  }
}

///|
fn recon_type!(
  self : Term,
  ctx : Context,
  uvar_gen : UVarGen,
  constr : Constr
) -> Type {
  match self {
    True(_) => Bool
    False(_) => Bool
    If(_, t1, t2, t3) => {
      let ty1 = t1.recon_type!(ctx, uvar_gen, constr)
      let ty2 = t2.recon_type!(ctx, uvar_gen, constr)
      let ty3 = t3.recon_type!(ctx, uvar_gen, constr)
      constr.push_back((ty1, Bool))
      constr.push_back((ty2, ty3))
      ty3
    }
    Zero(_) => Nat
    Succ(_, t1) => {
      let ty1 = t1.recon_type!(ctx, uvar_gen, constr)
      constr.push_back((ty1, Nat))
      Nat
    }
    Pred(_, t1) => {
      let ty1 = t1.recon_type!(ctx, uvar_gen, constr)
      constr.push_back((ty1, Nat))
      Nat
    }
    IsZero(_, t1) => {
      let ty1 = t1.recon_type!(ctx, uvar_gen, constr)
      constr.push_back((ty1, Nat))
      Bool
    }
    Var(_, x, _) => ctx.get_type(x)
    Abs(_, x, None, t2) => {
      let tyx = Id(uvar_gen.next())
      let ctx1 = ctx.add_binding(x, Var(tyx))
      let ty2 = t2.recon_type!(ctx1, uvar_gen, constr)
      Arr(tyx, ty2)
    }
    Abs(_, x, Some(ty1), t2) => {
      let ctx1 = ctx.add_binding(x, Var(ty1))
      let ty2 = t2.recon_type!(ctx1, uvar_gen, constr)
      Arr(ty1, ty2)
    }
    App(_, t1, t2) => {
      let ty1 = t1.recon_type!(ctx, uvar_gen, constr)
      let ty2 = t2.recon_type!(ctx, uvar_gen, constr)
      let tyx = Id(uvar_gen.next())
      constr.push_back((ty1, Arr(ty2, tyx)))
      tyx
    }
  }
}

///|
fn Type::has_free_var(self : Type, x : String) -> Bool {
  match self {
    Bool => false
    Nat => false
    Arr(ty1, ty2) => ty1.has_free_var(x) || ty2.has_free_var(x)
    Id(y) => x == y
  }
}

///|
fn Type::subst(self : Type, x : String, s : Type) -> Type {
  match self {
    Bool => Bool
    Nat => Nat
    Arr(ty1, ty2) => Arr(ty1.subst(x, s), ty2.subst(x, s))
    Id(y) => if x == y { s } else { Id(y) }
  }
}

///|
fn Type::subst_constr(self : Type, constr : Constr) -> Type {
  let mut ty = self
  for p in constr._ {
    match p {
      (Id(x), ty2) => ty = ty.subst(x, ty2)
      _ => panic()
    }
  }
  ty
}

///|
fn Constr::subst(self : Constr, x : String, s : Type) -> Unit {
  for i, p in self._ {
    self._[i] = (p.0.subst(x, s), p.1.subst(x, s))
  }
}

///|
fn Constr::unify!(self : Constr, msg : String, info : Info) -> Unit {
  let sol = Constr::new()
  loop () {
    _ =>
      match self.pop_front() {
        None => {
          self.append(sol)
          break
        }
        Some(p) =>
          match p {
            (ty1, Id(x)) =>
              if ty1 == Id(x) {
                continue ()
              } else if ty1.has_free_var(x) {
                error_info!("\{msg}: circular constraints", info~)
              } else {
                self.subst(x, ty1)
                sol.push_back((Id(x), ty1))
                continue ()
              }
            (Id(x), ty2) =>
              if ty2 == Id(x) {
                continue ()
              } else if ty2.has_free_var(x) {
                error_info!("\{msg}: circular constraints", info~)
              } else {
                self.subst(x, ty2)
                sol.push_back((Id(x), ty2))
                continue ()
              }
            (Bool, Bool) => continue ()
            (Nat, Nat) => continue ()
            (Arr(ty11, ty12), Arr(ty21, ty22)) => {
              self.push_front((ty11, ty21))
              self.push_front((ty12, ty22))
              continue ()
            }
            _ => error_info!("unsolvable constraints", info~)
          }
      }
  }
}

///|
fn Binding::eval(self : Binding, ctx : Context) -> Binding {
  match self {
    Name => Name
    TmAbb(t, ty_opt) => {
      let t_prime = t.eval(ctx)
      TmAbb(t_prime, ty_opt)
    }
    Var(ty) => Var(ty)
  }
}

///|
fn Binding::recon_type!(
  self : Binding,
  ctx : Context,
  uvar_gen : UVarGen,
  constr : Constr,
  info : Info
) -> Binding {
  match self {
    Name => Name
    TmAbb(t, None) => {
      let ty = t.recon_type!(ctx, uvar_gen, constr)
      constr.unify!("could not simplify constraints", info)
      TmAbb(t, Some(ty.subst_constr(constr)))
    }
    TmAbb(t, Some(ann_ty)) => {
      let ty = t.recon_type!(ctx, uvar_gen, constr)
      constr.push_back((ty, ann_ty))
      constr.unify!("could not simplify constraints", info)
      TmAbb(t, Some(ann_ty))
    }
    Var(ty) => Var(ty)
  }
}
