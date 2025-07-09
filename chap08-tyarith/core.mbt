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
suberror NoRuleApplies

///|
fn eval1(self : Term) -> Term raise NoRuleApplies {
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
        let t1_prime = t1.eval1()
        If(info, t1_prime, t2, t3)
      }
    Zero(_) => raise NoRuleApplies
    Succ(info, t1) =>
      if t1.is_val() {
        raise NoRuleApplies
      } else {
        let t1_prime = t1.eval1()
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
        let t1_prime = t1.eval1()
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
        let t1_prime = t1.eval1()
        IsZero(info, t1_prime)
      }
  }
}

///|
fn eval(self : Term) -> Term {
  loop self {
    t =>
      try {
        continue t.eval1()
      } catch {
        NoRuleApplies => break t
      }
  }
}

///|
fn derive_type(self : Term) -> Type raise {
  match self {
    True(_) => Bool
    False(_) => Bool
    If(info, t1, t2, t3) =>
      if t1.derive_type() == Bool {
        let ty2 = t2.derive_type()
        let ty3 = t3.derive_type()
        if ty2 == ty3 {
          ty2
        } else {
          error_info("arms of conditional have different types", info~)
        }
      } else {
        error_info("guard of conditional not a boolean", info~)
      }
    Zero(_) => Nat
    Succ(info, t1) =>
      if t1.derive_type() == Nat {
        Nat
      } else {
        error_info("argument of succ is not a number", info~)
      }
    Pred(info, t1) =>
      if t1.derive_type() == Nat {
        Nat
      } else {
        error_info("argument of pred is not a number", info~)
      }
    IsZero(info, t1) =>
      if t1.derive_type() == Nat {
        Bool
      } else {
        error_info("argument of iszero is not a number", info~)
      }
  }
}
