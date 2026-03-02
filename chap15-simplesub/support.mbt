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
suberror ErrorWithInfo {
  ErrorWithInfo((String, Info))
}

///|
fn[T] error_info(msg : String, info? : Info = UNKNOWN) -> T raise {
  raise ErrorWithInfo((msg, info))
}

///|
type ParseToplevel = (Context) -> (@list.List[Command], Context) raise Error

///|
type ParseCommand = (Context) -> (Command, Context) raise Error

///|
type ParseBinder = (Context) -> Binding raise Error

///|
type ParseTerm = (Context) -> Term raise Error

///|
type ParseLabelTerms = (Context, Int) -> @list.List[(String, Term)] raise Error

///|
type ParseLabelTerm = (Context, Int) -> (String, Term) raise Error

///|
type ParseType = (Context) -> Type

///|
type ParseLabelTypes = (Context, Int) -> @list.List[(String, Type)]

///|
type ParseLabelType = (Context, Int) -> (String, Type)
