"""Exact SymPy checks for the retained two-pair reset construction, Section 7."""
import sympy as S
x=S.symbols('x');lo=S.Rational(78295,1000000);hi=S.Rational(78296,1000000)
e=S.Rational(12281660,12608823);b=S.Rational(2,5);u=b/10;tau=S.Rational(1,5)
w=b-x-S.Rational(219,29)*x*b;X2=(2+e)*x;D=(3+u)*(1+w)
L2=S.factor((3*X2+6*w-u-S.Rational(29,26)*u*w)/D);Y2=e*x/(1-x)
P=31906921688093*x*x-21898290083611*x+1518934471518
F=S.factor((1-tau)*L2-tau-Y2)
assert S.cancel(F-P/(31143792810*(x-1)*(583*x-203)))==0
assert P.subs(x,lo)>0>P.subs(x,hi)
S0=(1-x)*(1-b);A=2*x*(1-b)+(1-x)*b/2+5*x*b
L1=S.factor((3*A-9*S0*tau+6*w-3*u-S.Rational(45,26)*u*w)/(D-3*S0*(1-tau)))
Y1=(1-tau)*L1-3*tau;X1=A+S0*Y1
Tmax=101/x-2/b-99-S.Rational(219,29)
def bern(p):
 y=S.symbols('y');p=S.Poly(S.expand(p.subs(x,lo+(hi-lo)*y)),y);n=p.degree()
 return [S.factor(sum(p.nth(i)*S.binomial(k,i)/S.binomial(n,i) for i in range(k+1))) for k in range(n+1)]
def pos(f,name):
 p,q=S.fraction(S.cancel(f))
 if q.subs(x,lo)<0:p,q=-p,-q
 bp,bq=bern(p),bern(q)
 assert min(bp)>0,(name,'numerator');assert min(bq)>0,(name,'denominator')
 print('PASS',name,'degrees',len(bp)-1,len(bq)-1)
for name,f in [('minusPprime',-S.diff(P,x)),('x',x),('oneMinusX',1-x),('w',w),('L2',L2),('Y2',Y2),('L1',L1),('X1',X1),('reset2',L2-(2+e/2)*w),('reset1',L1-w/2),('wash10',10*(1-tau)*Y2-3*tau),('joint1',1-7*x),('Tmax1178',Tmax-1178)]:pos(f,name)
for name,f,l,h in [("w",w,S.Rational(85,1000),S.Rational(86,1000)),("L1",L1,S.Rational(35,100),S.Rational(36,100)),("L2",L2,S.Rational(35,100),S.Rational(36,100)),("X1",X1,S.Rational(25,100),S.Rational(27,100)),("Y2",Y2,S.Rational(8,100),S.Rational(9,100))]:
 pos(f-l,name+" lower");pos(h-f,name+" upper")
print("PASS unique bracket and all retained rational interval bounds")
