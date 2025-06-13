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
typealias (Context) -> (@immut/list.T[Command], Context) raise Error as ParseToplevel

///|
typealias (Context) -> (Command, Context) raise Error as ParseCommand

///|
typealias (Context) -> Binding raise Error as ParseBinder

///|
typealias (Context) -> Term raise Error as ParseTerm
