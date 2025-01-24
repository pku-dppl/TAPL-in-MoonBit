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
        TmAbb(t) => t
        _ => raise NoRuleApplies
      }
    Abs(_) => raise NoRuleApplies
    App(info, t1, t2) =>
      if t1.is_val() {
        if t2.is_val() {
          match t1 {
            Abs(_, _, t12) => t12.subst_top(t2)
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
fn Binding::eval(self : Binding, ctx : Context) -> Binding {
  match self {
    Name => Name
    TmAbb(t) => {
      let t_prime = t.eval(ctx)
      TmAbb(t_prime)
    }
  }
}
