///|
enum Term {
  True(Info)
  False(Info)
  If(Info, Term, Term, Term)
  Zero(Info)
  Succ(Info, Term)
  Pred(Info, Term)
  IsZero(Info, Term)
}

///|
enum Command {
  Import(String)
  Eval(Info, Term)
}

///|
fn Term::to_string(self : Term) -> String {
  let logger = StringBuilder::new()
  self.output(logger)
  logger.to_string()
}

///|
fn Term::output(self : Term, logger : &Logger) -> Unit {
  match self {
    If(_, t1, t2, t3) => {
      logger.write_string("if ")
      t1.output(logger)
      logger.write_string(" then ")
      t2.output(logger)
      logger.write_string(" else")
      t3.output(logger)
    }
    _ => self.output_app(logger)
  }
}

///|
fn Term::output_app(self : Term, logger : &Logger) -> Unit {
  match self {
    Pred(_, t1) => {
      logger.write_string("pred ")
      t1.output_atom(logger)
    }
    IsZero(_, t1) => {
      logger.write_string("iszero ")
      t1.output_atom(logger)
    }
    _ => self.output_atom(logger)
  }
}

///|
fn Term::output_atom(self : Term, logger : &Logger) -> Unit {
  match self {
    True(_) => logger.write_string("true")
    False(_) => logger.write_string("false")
    Zero(_) => logger.write_string("0")
    Succ(_, t1) =>
      loop (t1, 1) {
        (Zero(_), n) => {
          logger.write_string("\{n}")
          break
        }
        (Succ(_, s), n) => continue (s, n + 1)
        _ => {
          logger.write_string("(succ ")
          t1.output_atom(logger)
          logger.write_string(")")
        }
      }
    _ => {
      logger.write_string("(")
      self.output(logger)
      logger.write_string(")")
    }
  }
}
