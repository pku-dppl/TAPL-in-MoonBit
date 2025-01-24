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

tru = lambda t:Nat. lambda f:Nat. t;
fls = lambda t:Nat. lambda f:Nat. f;

test = lambda l:Nat->Nat->Nat. lambda m:Nat. lambda n:Nat. l m n;
test tru 33 44;

pair = lambda f:Nat. lambda s:Nat. lambda b:Nat->Nat->Nat. b f s;
fst = lambda p:(Nat->Nat->Nat)->Nat. p tru;
snd = lambda p:(Nat->Nat->Nat)->Nat. p fls;
fst (pair 33 44);

c0 = lambda s:Nat->Nat. lambda z:Nat. z;
c1 = lambda s:Nat->Nat. lambda z:Nat. s z;
c2 = lambda s:Nat->Nat. lambda z:Nat. s (s z);
c3 = lambda s:Nat->Nat. lambda z:Nat. s (s (s z));

scc = lambda n:(Nat->Nat)->Nat->Nat. lambda s:Nat->Nat. lambda z:Nat. s (n s z);
scc c1;

plus = lambda m:(Nat->Nat)->Nat->Nat. lambda n:(Nat->Nat)->Nat->Nat. lambda s:Nat->Nat. lambda z:Nat. m s (n s z);
plus c2 c2;

realnat = lambda m:(Nat->Nat)->Nat->Nat. m (lambda x:Nat. succ x) 0;
realnat c3;
realnat (plus c2 c2);

{pred 4, if true then false else false};
{pred 4, if true then false else false}.1;

(lambda x:{Nat, Nat}. x.2) {pred 4, pred 5};

t1 = {partno=55, cost=30};
t2 = {cost=30, partno=55};
ft = lambda x:{partno:Nat, cost:Nat}. x.cost;
ft(t1);
ft(t2);
ft({cost=123, partno=124, abc=125});

{x=true, y=false};
{x=true, y=false}.x;
{true, false};
{true, false}.1;

if true then {x=true,y=false,a=false} else {y=false,x={},b=false};

lambda x:Top. x;
  (lambda x:Top. x) (lambda x:Top. x);
(lambda x:Top->Top. x) (lambda x:Top. x);

(lambda r:{x:Top->Top}. r.x r.x)
  {x=lambda z:Top.z, y=lambda z:Top.z};
