/* Examples for testing */

true;
if false then true else false;

42;
succ (pred 0);
iszero (pred (succ (succ 0)));

x : Bool;
x;

lambda x:Bool. x;
(lambda x:Bool->Bool. if x false then true else false)
  (lambda x:Bool. if x then false else true);

id = lambda x:Bool. x;
id (id ((lambda z:Bool. id z) true));

CBool = Nat->Nat->Nat;

tru = (lambda t:Nat. lambda f:Nat. t) as CBool;
fls = (lambda t:Nat. lambda f:Nat. f) as CBool;

test = lambda l:CBool. lambda m:Nat. lambda n:Nat. l m n;
test tru 33 44;

CPair = CBool->Nat;

pair = lambda f:Nat. lambda s:Nat. (lambda b:CBool. b f s) as CPair;
fst = lambda p:CPair. p tru;
snd = lambda p:CPair. p fls;
fst (pair 33 44);

CNat = (Nat->Nat)->Nat->Nat;

c0 = (lambda s:Nat->Nat. lambda z:Nat. z) as CNat;
c1 = (lambda s:Nat->Nat. lambda z:Nat. s z) as CNat;
c2 = (lambda s:Nat->Nat. lambda z:Nat. s (s z)) as CNat;
c3 = (lambda s:Nat->Nat. lambda z:Nat. s (s (s z))) as CNat;

scc = lambda n:CNat. (lambda s:Nat->Nat. lambda z:Nat. s (n s z)) as CNat;
scc c1;

plus = lambda m:CNat. lambda n:CNat. (lambda s:Nat->Nat. lambda z:Nat. m s (n s z)) as CNat;
plus c2 c2;

realnat = lambda m:CNat. m (lambda x:Nat. succ x) 0;
realnat c3;
realnat (plus c2 c2);

lambda x:A. x;
lambda x:B. x;
lambda f:A->A. lambda x:A. f(f(x));

unit;
(unit; 42);

UU = Unit->Unit;
(lambda f:UU. f unit) (lambda x:Unit. x);
(lambda f:Unit->Unit. f) as UU->UU;

{pred 4, if true then false else false};
{pred 4, if true then false else false}.1;

(lambda x:{Nat, Nat}. x.2) {pred 4, pred 5};

{partno=55, cost=30};
{cost=30, partno=55};

PhysicalAddr = {firstlast:String, addr:String};
VirtualAddr = {name:String, email:String};

pa = {firstlast="AC", addr="EG"};
va = {name="AC", email="AC@edu"};

Addr = <physical:PhysicalAddr, virtual:VirtualAddr>;
a = <physical=pa> as Addr;

getName = lambda a:Addr.
  case a of
    <physical=x> ==> x.firstlast
  | <virtual=y> ==> y.name;

equal = fix (lambda eq:Nat->Nat->Bool. lambda x:Nat. lambda y:Nat.
    if iszero(x) then
      if iszero(y) then true
      else false
    else
      if iszero(y) then false
      else eq (pred x) (pred y)
  );

OptionNat = <none:Unit, some:Nat>;
Table = Nat->OptionNat;
emptyTable = lambda n:Nat. <none=unit> as OptionNat;
extendTable =
  lambda t:Table. lambda m:Nat. lambda v:Nat.
    (lambda n:Nat.
      if equal n m then <some=v> as OptionNat
      else t n) as Table;

Weekday = <monday:Unit, tuesday:Unit, wednesday:Unit, thursday:Unit, friday:Unit>;
nextBusinessDay = lambda w:Weekday.
  case w of <monday=x> ==> <tuesday=unit> as Weekday
          | <tuesday=x> ==> <wednesday=unit> as Weekday
          | <wednesday=x> ==> <thursday=unit> as Weekday
          | <thursday=x> ==> <friday=unit> as Weekday
          | <friday=x> ==> <monday=unit> as Weekday;

nextBusinessDay (<monday=unit> as Weekday);
nextBusinessDay (<friday=unit> as Weekday);

DollarAmount = <dollars:Double>;
EuroAmount = <euros:Double>;

dollars2euros =
  lambda d:DollarAmount.
    case d of <dollars=x> ==> <euros=timesdouble x 1.1325> as EuroAmount;
euros2dollars =
  lambda e:EuroAmount.
    case e of <euros=x> ==> <dollars=timesdouble x 0.883> as DollarAmount;

mybankbalance = <dollars=39.50> as DollarAmount;
euros2dollars (dollars2euros mybankbalance);

ff =
  lambda ie:Nat->Bool.
    lambda x:Nat.
      if iszero x then true
      else if iszero (pred x) then false
      else ie (pred (pred x));
iseven = fix ff;
iseven 7;

ff =
  lambda ieio:{iseven:Nat->Bool, isodd:Nat->Bool}.
    {iseven = lambda x:Nat. if iszero x then true else ieio.isodd (pred x),
     isodd = lambda x:Nat. if iszero x then false else ieio.iseven (pred x)};
r = fix ff;
iseven = r.iseven;
iseven 7;

diverge = lambda _:Unit. fix (lambda x:T. x);

lambda X. lambda x:X. x;
(lambda X. lambda x:X. x) [All X. X->X.];

{*All Y.Y, lambda x:(All Y.Y). x} as {Some X, X->X};

{*Nat, {c=0, f=lambda x:Nat. succ x}} as {Some X, {c:X, f:X->Nat}};
{X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}} as {Some X, {c:X, f:X->Nat}};
ops.f ops.c;

id = lambda X. lambda x:X. x;
id [Nat.];
id [Nat.] 0;

double = lambda X. lambda f:X->X. lambda a:X. f (f a);

doubleNat = double [Nat.];
doubleNatArrowNat = double [Nat->Nat.];

double [Nat.] (lambda x:Nat. succ(succ(x))) 3;

selfApp = lambda x:All X.X->X. x [All X.X->X.] x;

quadruple = lambda X. double [X->X.] (double [X.]);

CBool = All X. X->X->X;
tru = lambda X. lambda t:X. lambda f:X. t;
fls = lambda X. lambda t:X. lambda f:X. f;

not = lambda b:CBool. lambda X. lambda t:X. lambda f:X. b [X.] f t;

CNat = All X. (X->X) -> X -> X;
c0 = lambda X. lambda s:X->X. lambda z:X. z;
c1 = lambda X. lambda s:X->X. lambda z:X. s z;
c2 = lambda X. lambda s:X->X. lambda z:X. s (s z);

csucc = lambda n:CNat. lambda X. lambda s:X->X. lambda z:X. s (n [X.] s z);
cplus = lambda m:CNat. lambda n:CNat. m [CNat.] csucc n;

cnat2nat = lambda n:CNat. n [Nat.] (lambda x:Nat. succ(x)) 0;
cnat2nat (cplus (csucc c0) (csucc (csucc c0)));

ctimes = lambda m:CNat. lambda n:CNat. lambda X. lambda s:X->X. n [X.] (m [X.] s);
cexp = lambda m:CNat. lambda n:CNat. lambda X. n [X->X.] (m [X.]);
cnat2nat (ctimes c2 (csucc c2));
cnat2nat (cexp c2 (csucc c2));

PairNat = All X. (CNat->CNat->X)->X;

counterADT =
  {*Nat, {new = 1,
          get = lambda i:Nat. i,
          _inc = lambda i:Nat. succ(i)}}
as
  {Some Counter, {new:Counter, get:Counter->Nat, _inc:Counter->Counter}};

let {Counter,counter} = counterADT
in counter.get (counter._inc counter.new);

Counter = {Some X, {state:X, methods:{get:X->Nat, _inc:X->X}}};
c = {*Nat, {state=5, methods={get=lambda x:Nat. x, _inc=lambda x:Nat. succ(x)}}} as Counter;
let {X,body}=c in body.methods.get(body.state);

sendget = lambda c:Counter. let {X,body}=c in body.methods.get(body.state);
sendinc = lambda c:Counter. let {X,body}=c in {*X, {state=body.methods._inc(body.state), methods=body.methods}} as Counter;
