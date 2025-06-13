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
    Unit(_) => true
    Record(_, lts) => lts.all(fn(lt) { lt.1.is_val() })
    Tag(_, _, t1, _) => t1.is_val()
    String(_) => true
    Double(_) => true
    _ => self.is_numerical()
  }
}

///|
suberror NoRuleApplies

///|
fn eval1(self : Term, ctx : Context) -> Term raise NoRuleApplies {
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
        let t1_prime = t1.eval1(ctx)
        If(info, t1_prime, t2, t3)
      }
    Zero(_) => raise NoRuleApplies
    Succ(info, t1) =>
      if t1.is_val() {
        raise NoRuleApplies
      } else {
        let t1_prime = t1.eval1(ctx)
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
        let t1_prime = t1.eval1(ctx)
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
        let t1_prime = t1.eval1(ctx)
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
          let t2_prime = t2.eval1(ctx)
          App(info, t1, t2_prime)
        }
      } else {
        let t1_prime = t1.eval1(ctx)
        App(info, t1_prime, t2)
      }
    Unit(_) => raise NoRuleApplies
    Ascribe(info, t1, ty1) =>
      if t1.is_val() {
        t1
      } else {
        let t1_prime = t1.eval1(ctx)
        Ascribe(info, t1_prime, ty1)
      }
    Let(_) => ...
    Record(info, lts) =>
      loop (lts, @immut/list.Nil) {
        (Nil, _) => raise NoRuleApplies
        (Cons((l, t), rest), acc) =>
          if t.is_val() {
            continue (rest, Cons((l, t), acc))
          } else {
            let t_prime = t.eval1(ctx)
            break Record(info, acc.rev_concat(Cons((l, t_prime), rest)))
          }
      }
    Proj(info, t1, l) =>
      if t1.is_val() {
        match t1 {
          Record(_, lts) =>
            match lts.lookup(l) {
              None => raise NoRuleApplies
              Some(t) => t
            }
          _ => raise NoRuleApplies
        }
      } else {
        let t1_prime = t1.eval1(ctx)
        Proj(info, t1_prime, l)
      }
    Tag(info, l, t1, ty) =>
      if t1.is_val() {
        raise NoRuleApplies
      } else {
        let t1_prime = t1.eval1(ctx)
        Tag(info, l, t1_prime, ty)
      }
    Case(info, t1, cases) =>
      if t1.is_val() {
        match t1 {
          Tag(_, l, t11, _) =>
            match cases.lookup(l) {
              None => raise NoRuleApplies
              Some((_, t)) => t.subst_top(t11)
            }
          _ => raise NoRuleApplies
        }
      } else {
        let t1_prime = t1.eval1(ctx)
        Case(info, t1_prime, cases)
      }
    String(_) => raise NoRuleApplies
    Double(_) => raise NoRuleApplies
    Timesdouble(info, t1, t2) =>
      if t1.is_val() {
        if t2.is_val() {
          match (t1, t2) {
            (Double(_, d1), Double(_, d2)) => Double(UNKNOWN, d1 * d2)
            _ => raise NoRuleApplies
          }
        } else {
          let t2_prime = t2.eval1(ctx)
          Timesdouble(info, t1, t2_prime)
        }
      } else {
        let t1_prime = t1.eval1(ctx)
        Timesdouble(info, t1_prime, t2)
      }
    Fix(info, t1) =>
      if t1.is_val() {
        match t1 {
          Abs(_, _, _, t12) => t12.subst_top(self)
          _ => raise NoRuleApplies
        }
      } else {
        let t1_prime = t1.eval1(ctx)
        Fix(info, t1_prime)
      }
  }
}

///|
fn eval(self : Term, ctx : Context) -> Term {
  loop self {
    t =>
      try {
        continue t.eval1(ctx)
      } catch {
        NoRuleApplies => break t
      }
  }
}

///|
fn Type::compute(self : Type, ctx : Context) -> Type raise NoRuleApplies {
  match self {
    Bool => raise NoRuleApplies
    Nat => raise NoRuleApplies
    Arr(_) => raise NoRuleApplies
    Var(x, _) =>
      match ctx.get_binding(x) {
        TyAbb(ty) => ty
        TyVar => raise NoRuleApplies
        _ => panic()
      }
    Id(_) => raise NoRuleApplies
    Unit => raise NoRuleApplies
    Record(_) => raise NoRuleApplies
    Variant(_) => raise NoRuleApplies
    String => raise NoRuleApplies
    Double => raise NoRuleApplies
  }
}

///|
fn Type::simplify(self : Type, ctx : Context) -> Type {
  loop self {
    ty =>
      try {
        continue ty.compute(ctx)
      } catch {
        NoRuleApplies => break ty
      }
  }
}

///|
fn Type::equiv(self : Type, other : Type, ctx : Context) -> Bool {
  let ty1 = self.simplify(ctx)
  let ty2 = other.simplify(ctx)
  match (ty1, ty2) {
    (Bool, Bool) => true
    (Nat, Nat) => true
    (Arr(ty11, ty12), Arr(ty21, ty22)) =>
      ty21.equiv(ty11, ctx) && ty12.equiv(ty22, ctx)
    (Var(x1, _), Var(x2, _)) => x1 == x2
    (Id(b1), Id(b2)) => b1 == b2
    (Unit, Unit) => true
    (Record(ltys1), Record(ltys2)) =>
      ltys1
      .zip(ltys2)
      .map_or(false, fn(l) {
        l.all(fn(p) { p.0.0 == p.1.0 && p.0.1.equiv(p.1.1, ctx) })
      })
    (Variant(ltys1), Variant(ltys2)) =>
      ltys1
      .zip(ltys2)
      .map_or(false, fn(l) {
        l.all(fn(p) { p.0.0 == p.1.0 && p.0.1.equiv(p.1.1, ctx) })
      })
    (String, String) => true
    (Double, Double) => true
    _ => false
  }
}

///|
fn derive_type(self : Term, ctx : Context) -> Type raise {
  match self {
    True(_) => Bool
    False(_) => Bool
    If(info, t1, t2, t3) =>
      if t1.derive_type(ctx).equiv(Bool, ctx) {
        let ty2 = t2.derive_type(ctx)
        let ty3 = t3.derive_type(ctx)
        if ty2.equiv(ty3, ctx) {
          ty2
        } else {
          error_info("arms of conditional have different types", info~)
        }
      } else {
        error_info("guard of conditional not a boolean", info~)
      }
    Zero(_) => Nat
    Succ(info, t1) =>
      if t1.derive_type(ctx).equiv(Nat, ctx) {
        Nat
      } else {
        error_info("argument of succ is not a number", info~)
      }
    Pred(info, t1) =>
      if t1.derive_type(ctx).equiv(Nat, ctx) {
        Nat
      } else {
        error_info("argument of pred is not a number", info~)
      }
    IsZero(info, t1) =>
      if t1.derive_type(ctx).equiv(Nat, ctx) {
        Bool
      } else {
        error_info("argument of iszero is not a number", info~)
      }
    Var(_, x, _) => ctx.get_type(x)
    Abs(_, x, ty1, t2) => {
      let ctx1 = ctx.add_binding(x, Var(ty1))
      let ty2 = t2.derive_type(ctx1).shift(-1)
      Arr(ty1, ty2)
    }
    App(info, t1, t2) => {
      let ty1 = t1.derive_type(ctx)
      let ty2 = t2.derive_type(ctx)
      match ty1.simplify(ctx) {
        Arr(ty11, ty12) =>
          if ty2.equiv(ty11, ctx) {
            ty12
          } else {
            error_info("parameter type mismatch", info~)
          }
        _ => error_info("arrow type expected", info~)
      }
    }
    Unit(_) => Unit
    Ascribe(info, t1, ty2) =>
      if t1.derive_type(ctx).equiv(ty2, ctx) {
        ty2
      } else {
        error_info("body of as-term does not have the expected type", info~)
      }
    Let(_) => ...
    Record(info, lts) =>
      loop (lts, @immut/list.Nil) {
        (Nil, acc) => break Record(acc.rev())
        (Cons((l, t), rest), acc) =>
          if acc.lookup(l).is_empty() {
            continue (rest, Cons((l, t.derive_type(ctx)), acc))
          } else {
            error_info("duplicate label \{l} is not allowed", info~)
          }
      }
    Proj(info, t1, l) =>
      match t1.derive_type(ctx).simplify(ctx) {
        Record(ltys) =>
          match ltys.lookup(l) {
            None => error_info("label \{l} not found", info~)
            Some(ty) => ty
          }
        _ => error_info("record type expected", info~)
      }
    Tag(info, l, t1, ty) =>
      match ty.simplify(ctx) {
        Variant(ltys) =>
          match ltys.lookup(l) {
            None => error_info("label \{l} not found", info~)
            Some(ann_ty) =>
              if t1.derive_type(ctx).equiv(ann_ty, ctx) {
                ty
              } else {
                error_info("variant does not have the expected type", info~)
              }
          }
        _ => error_info("annotation is not a variant type", info~)
      }
    Case(info, t1, cases) =>
      match t1.derive_type(ctx).simplify(ctx) {
        Variant(ltys) => {
          for case in cases {
            if ltys.lookup(case.0).is_empty() {
              error_info("label \{case.0} not in type", info~)
            }
          }
          let case_tys = loop (cases, @immut/list.Nil) {
            (Nil, acc) => break acc.rev()
            (Cons((l, (x, t)), rest), acc) => {
              let ty = ltys.lookup(l).unwrap()
              let ctx1 = ctx.add_binding(x, Var(ty))
              continue (rest, Cons(t.derive_type(ctx1).shift(-1), acc))
            }
          }
          let ty1 = case_tys.unsafe_head()
          for ty in case_tys.tail() {
            if not(ty.equiv(ty1, ctx)) {
              error_info("cases do not have the same type", info~)
            }
          }
          ty1
        }
        _ => error_info("variant type expected", info~)
      }
    String(_) => String
    Double(_) => Double
    Timesdouble(info, t1, t2) =>
      if t1.derive_type(ctx).equiv(Double, ctx) &&
        t2.derive_type(ctx).equiv(Double, ctx) {
        Double
      } else {
        error_info("argument of timesdouble is not a decimal number", info~)
      }
    Fix(info, t1) =>
      match t1.derive_type(ctx).simplify(ctx) {
        Arr(t11, t12) =>
          if t12.equiv(t11, ctx) {
            t12
          } else {
            error_info("result of body not compatible with domain", info~)
          }
        _ => error_info("arrow type expected", info~)
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
    TyAbb(ty) => TyAbb(ty)
    TyVar => TyVar
  }
}

///|
fn Binding::derive_type(
  self : Binding,
  ctx : Context,
  info : Info
) -> Binding raise {
  match self {
    Name => Name
    TmAbb(t, None) => {
      let ty = t.derive_type(ctx)
      TmAbb(t, Some(ty))
    }
    TmAbb(t, Some(ty)) =>
      if t.derive_type(ctx).equiv(ty, ctx) {
        TmAbb(t, Some(ty))
      } else {
        error_info("type of binding does not match declared type", info~)
      }
    Var(ty) => Var(ty)
    TyAbb(ty) => TyAbb(ty)
    TyVar => TyVar
  }
}
