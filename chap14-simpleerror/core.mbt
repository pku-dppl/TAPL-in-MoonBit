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
fn is_error(self : Term) -> Bool {
  match self {
    Error(_) => true
    _ => false
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
      if t1.is_error() {
        t1
      } else if t1.is_val() {
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
      if t1.is_error() {
        t1
      } else if t1.is_val() {
        raise NoRuleApplies
      } else {
        let t1_prime = t1.eval1!(ctx)
        Succ(info, t1_prime)
      }
    Pred(info, t1) =>
      if t1.is_error() {
        t1
      } else if t1.is_val() {
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
      if t1.is_error() {
        t1
      } else if t1.is_val() {
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
      if t1.is_error() {
        t1
      } else if t1.is_val() {
        if t2.is_error() {
          t2
        } else if t2.is_val() {
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
    Error(_) => raise NoRuleApplies
    Try(info, t1, t2) =>
      if t1.is_error() {
        t2
      } else if t1.is_val() {
        t1
      } else {
        let t1_prime = t1.eval1!(ctx)
        Try(info, t1_prime, t2)
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
fn derive_type!(self : Term, ctx : Context) -> Type {
  match self {
    True(_) => Bool
    False(_) => Bool
    If(_, t1, t2, t3) => {
      t1.check_type!(ctx, Bool)
      let ty2 = t2.derive_type!(ctx)
      t3.check_type!(ctx, ty2)
      ty2
    }
    Zero(_) => Nat
    Succ(_, t1) => {
      t1.check_type!(ctx, Nat)
      Nat
    }
    Pred(_, t1) => {
      t1.check_type!(ctx, Nat)
      Nat
    }
    IsZero(_, t1) => {
      t1.check_type!(ctx, Nat)
      Bool
    }
    Var(_, x, _) => ctx.get_type(x)
    Abs(_, x, ty1, t2) => {
      let ctx1 = ctx.add_binding(x, Var(ty1))
      let ty2 = t2.derive_type!(ctx1)
      Arr(ty1, ty2)
    }
    App(info, t1, t2) => {
      let ty1 = t1.derive_type!(ctx)
      match ty1 {
        Arr(ty11, ty12) => {
          t2.check_type!(ctx, ty11)
          ty12
        }
        _ => error_info!("arrow type expected", info~)
      }
    }
    Error(info) =>
      error_info!("error must appear in a position with known type", info~)
    Try(_, t1, t2) => {
      let ty2 = t2.derive_type!(ctx)
      t1.check_type!(ctx, ty2)
      ty2
    }
  }
}

///|
fn check_type!(self : Term, ctx : Context, expect : Type) -> Unit {
  fn report!(expect : Type, ty : Type, info) {
    if ty != expect {
      error_info!("expect \{expect}, but get \{ty}", info~)
    }
  }

  match self {
    True(info) => report!(expect, Bool, info)
    False(info) => report!(expect, Bool, info)
    If(_, t1, t2, t3) => {
      t1.check_type!(ctx, Bool)
      t2.check_type!(ctx, expect)
      t3.check_type!(ctx, expect)
    }
    Zero(info) => report!(expect, Nat, info)
    Succ(info, t1) => {
      t1.check_type!(ctx, Nat)
      report!(expect, Nat, info)
    }
    Pred(info, t1) => {
      t1.check_type!(ctx, Nat)
      report!(expect, Nat, info)
    }
    IsZero(info, t1) => {
      t1.check_type!(ctx, Nat)
      report!(expect, Bool, info)
    }
    Var(info, x, _) => {
      let ty = ctx.get_type(x)
      report!(expect, ty, info)
    }
    Abs(info, x, ty1, t2) =>
      match expect {
        Arr(ty1_expect, ty2_expect) => {
          report!(ty1_expect, ty1, info)
          t2.check_type!(ctx.add_binding(x, Var(ty1)), ty2_expect)
        }
        _ => error_info!("expect \{expect}, but get an arrow type", info~)
      }
    App(_, t1, t2) => {
      let ty2 = t2.derive_type!(ctx)
      t1.check_type!(ctx, Arr(ty2, expect))
    }
    Error(_) => ()
    Try(_, t1, t2) => {
      t1.check_type!(ctx, expect)
      t2.check_type!(ctx, expect)
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
fn Binding::derive_type!(self : Binding, ctx : Context, info : Info) -> Binding {
  match self {
    Name => Name
    TmAbb(t, None) => {
      let ty = t.derive_type!(ctx)
      TmAbb(t, Some(ty))
    }
    TmAbb(t, Some(ty)) =>
      if t.derive_type!(ctx) == ty {
        TmAbb(t, Some(ty))
      } else {
        error_info!("type of binding does not match declared type", info~)
      }
    Var(ty) => Var(ty)
  }
}
