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
suberror ErrorWithInfo (String, Info)

///|
fn[T] error_info(msg : String, info~ : Info = UNKNOWN) -> T raise {
  raise ErrorWithInfo((msg, info))
}

///|
typealias (Context) -> (@list.List[Command], Context) raise Error as ParseToplevel

///|
typealias (Context) -> (Command, Context) raise Error as ParseCommand

///|
typealias (Context) -> Binding raise Error as ParseBinder

///|
typealias (Context) -> Term raise Error as ParseTerm

///|
typealias (Context) -> @list.List[(String, (String, Term))] raise Error as ParseCases

///|
typealias (Context) -> (String, (String, Term)) raise Error as ParseCase

///|
typealias (Context, Int) -> @list.List[(String, Term)] raise Error as ParseLabelTerms

///|
typealias (Context, Int) -> (String, Term) raise Error as ParseLabelTerm

///|
typealias (Context) -> Type raise Error as ParseType

///|
typealias (Context, Int) -> @list.List[(String, Type)] raise Error as ParseLabelTypes

///|
typealias (Context, Int) -> (String, Type) raise Error as ParseLabelType
