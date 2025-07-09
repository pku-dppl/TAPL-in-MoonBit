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
    Record(_, lts) => lts.all(fn(lt) { lt.1.is_val() })
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
fn Type::subtype_of(self : Type, other : Type) -> Bool {
  if self == other {
    true
  } else {
    match (self, other) {
      (_, Top) => true
      (Arr(ty11, ty12), Arr(ty21, ty22)) =>
        ty21.subtype_of(ty11) && ty12.subtype_of(ty22)
      (Record(ltys1), Record(ltys2)) =>
        ltys2.all(fn(lt) {
          match ltys1.lookup(lt.0) {
            None => false
            Some(t1) => t1.subtype_of(lt.1)
          }
        })
      _ => false
    }
  }
}

///|
fn Type::join(self : Type, other : Type) -> Type {
  if self.subtype_of(other) {
    other
  } else if other.subtype_of(self) {
    self
  } else {
    match (self, other) {
      (Arr(ty11, ty12), Arr(ty21, ty22)) =>
        Arr(ty11.meet(ty21), ty12.join(ty22)) catch {
          NoRuleApplies => Top
        }
      (Record(ltys1), Record(ltys2)) => {
        let labels1 = ltys1.map(fn(lty) { lty.0 })
        let labels2 = ltys2.map(fn(lty) { lty.0 })
        let common_labels = labels1.filter(fn(l) { labels2.contains(l) })
        let common_ltys = common_labels.map(fn(l) {
          let ty1 = ltys1.lookup(l).unwrap()
          let ty2 = ltys2.lookup(l).unwrap()
          (l, ty1.join(ty2))
        })
        Record(common_ltys)
      }
      _ => Top
    }
  }
}

///|
fn Type::meet(self : Type, other : Type) -> Type raise NoRuleApplies {
  if self.subtype_of(other) {
    self
  } else if other.subtype_of(self) {
    other
  } else {
    match (self, other) {
      (Arr(ty11, ty12), Arr(ty21, ty22)) =>
        Arr(ty11.join(ty21), ty12.meet(ty22))
      (Record(ltys1), Record(ltys2)) => {
        let labels1 = ltys1.map(fn(lty) { lty.0 })
        let labels2 = ltys2.map(fn(lty) { lty.0 })
        let all_labels = labels1.concat(
          labels2.filter(fn(l) { not(labels1.contains(l)) }),
        )
        let all_ltys = loop (all_labels, @immut/list.Nil) {
          (Nil, acc) => break acc.rev()
          (Cons(l, rest), acc) => {
            let ty = match (ltys1.lookup(l), ltys2.lookup(l)) {
              (Some(ty1), Some(ty2)) => ty1.meet(ty2)
              (Some(ty1), None) => ty1
              (None, Some(ty2)) => ty2
              (None, None) => panic()
            }
            continue (rest, Cons((l, ty), acc))
          }
        }
        Record(all_ltys)
      }
      _ => raise NoRuleApplies
    }
  }
}

///|
fn derive_type(self : Term, ctx : Context) -> Type raise {
  match self {
    True(_) => Bool
    False(_) => Bool
    If(info, t1, t2, t3) =>
      if t1.derive_type(ctx).subtype_of(Bool) {
        let ty2 = t2.derive_type(ctx)
        let ty3 = t3.derive_type(ctx)
        ty2.join(ty3)
      } else {
        error_info("guard of conditional not a boolean", info~)
      }
    Zero(_) => Nat
    Succ(info, t1) =>
      if t1.derive_type(ctx).subtype_of(Nat) {
        Nat
      } else {
        error_info("argument of succ is not a number", info~)
      }
    Pred(info, t1) =>
      if t1.derive_type(ctx).subtype_of(Nat) {
        Nat
      } else {
        error_info("argument of pred is not a number", info~)
      }
    IsZero(info, t1) =>
      if t1.derive_type(ctx).subtype_of(Nat) {
        Bool
      } else {
        error_info("argument of iszero is not a number", info~)
      }
    Var(_, x, _) => ctx.get_type(x)
    Abs(_, x, ty1, t2) => {
      let ctx1 = ctx.add_binding(x, Var(ty1))
      let ty2 = t2.derive_type(ctx1)
      Arr(ty1, ty2)
    }
    App(info, t1, t2) => {
      let ty1 = t1.derive_type(ctx)
      let ty2 = t2.derive_type(ctx)
      match ty1 {
        Arr(ty11, ty12) =>
          if ty2.subtype_of(ty11) {
            ty12
          } else {
            error_info("parameter type mismatch", info~)
          }
        _ => error_info("arrow type expected", info~)
      }
    }
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
      match t1.derive_type(ctx) {
        Record(ltys) =>
          match ltys.lookup(l) {
            None => error_info("label \{l} not found", info~)
            Some(ty) => ty
          }
        _ => error_info("record type expected", info~)
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
      if t.derive_type(ctx).subtype_of(ty) {
        TmAbb(t, Some(ty))
      } else {
        error_info("type of binding does not match declared type", info~)
      }
    Var(ty) => Var(ty)
  }
}
