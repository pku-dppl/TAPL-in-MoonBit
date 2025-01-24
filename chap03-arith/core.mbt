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
    _ => self.is_numerical()
  }
}

///|
type! NoRuleApplies

///|
fn eval1(self : Term) -> Term!NoRuleApplies {
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
        let t1_prime = t1.eval1!()
        If(info, t1_prime, t2, t3)
      }
    Zero(_) => raise NoRuleApplies
    Succ(info, t1) =>
      if t1.is_val() {
        raise NoRuleApplies
      } else {
        let t1_prime = t1.eval1!()
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
        let t1_prime = t1.eval1!()
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
        let t1_prime = t1.eval1!()
        IsZero(info, t1_prime)
      }
  }
}

///|
fn eval(self : Term) -> Term {
  loop self {
    t =>
      try {
        continue t.eval1!()
      } catch {
        NoRuleApplies => break t
      }
  }
}
