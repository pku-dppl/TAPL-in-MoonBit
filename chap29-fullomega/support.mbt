///|
struct Pos {
  fname : String
  lnum : Int
  bol : Int
  cnum : Int
}

///|
impl Show for Pos with output(self, logger) {
  logger.write_string("\{self.fname}:\{self.lnum}:\{self.cnum - self.bol + 1}")
}

///|
enum Info {
  FI(Pos, Pos)
  UNKNOWN
}

///|
impl Show for Info with output(self, logger) {
  match self {
    FI(start, end) => logger.write_string(" [\{start}--\{end}]")
    UNKNOWN => ()
  }
}

///|
type! ErrorWithInfo (String, Info)

///|
fn error_info![T](msg : String, info~ : Info = UNKNOWN) -> T {
  raise ErrorWithInfo((msg, info))
}

///|
typealias ParseToplevel = (Context) -> (@immut/list.T[Command], Context)!Error

///|
typealias ParseCommand = (Context) -> (Command, Context)!Error

///|
typealias ParseBinder = (Context) -> Binding!Error

///|
typealias ParseTerm = (Context) -> Term!Error

///|
typealias ParseCases = (Context) -> @immut/list.T[(String, (String, Term))]!Error

///|
typealias ParseCase = (Context) -> (String, (String, Term))!Error

///|
typealias ParseLabelTerms = (Context, Int) -> @immut/list.T[(String, Term)]!Error

///|
typealias ParseLabelTerm = (Context, Int) -> (String, Term)!Error

///|
typealias ParseType = (Context) -> Type!Error

///|
typealias ParseLabelTypes = (Context, Int) -> @immut/list.T[(String, Type)]!Error

///|
typealias ParseLabelType = (Context, Int) -> (String, Type)!Error

///|
typealias ParseKind = (Context) -> Kind
