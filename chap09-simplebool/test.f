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
