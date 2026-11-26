"""Exact upper-cone certificate for every real premium M>=11.
Requires SymPy only. No sampled data, floating arithmetic or external files.
"""
import sympy as s
from itertools import product
from math import comb
h,A,T,u,U=s.symbols('h A T u U')
M=1/h;a=h*A;t=h*T;c=U*u*t
S=5*(t+c+t*c)/((1+t)*(1+c))
v=((M-1)*a-5*c-5*a*c)/((1+a)*(1+c))
w=((M-1)*t-5*a-5*a*t)/((1+a)*(1+t))
K=M*M+4*M+24+U*(7*M+6)+5*U*w-5*v
R=(M+6)*S+M*w+6*v
E=(4+7*U)*R*K+5*U*R*R-S*K*K
n,d=s.fraction(s.factor(E))
assert d==h**3*(1+A*h)**2*(1+T*h)**3*(1+T*U*h*u)**3
rn,rd=s.fraction(s.factor(R))
assert s.expand(rn-(A*h*(1-6*h)+T+24*A*T*h**3+6*A*T*h**2
 +4*T*T*U*h*h*u+T*T*U*h*u+5*T*U*h*u+30*T*h*h+4*T*h))==0
assert rd==h*(1+A*h)*(1+T*h)*(1+T*U*h*u)
# The scalar-root upper-bound comparison is algebraic, not numerical.
b,SS,V,W,MM,UU=s.symbols('b SS V W MM UU')
KK=MM*MM+4*MM+24+UU*(7*MM+6)+5*UU*W-5*V
RR=(MM+6)*SS+MM*W+6*V
Fnum=(MM-5*UU*b)*(MM*b-W)-(6*UU*b+V)*(6+5*b)
assert s.expand(Fnum-(b*KK-RR)-(MM+6)*(SS-(4+7*UU)*b-5*UU*b*b))==0

def bernstein(poly,variables):
 p=s.Poly(poly,*variables);degrees=p.degree_list();values=dict(p.terms())
 for i,dd in enumerate(degrees):
  new={}
  rest=[range(dj+1) if j!=i else [0] for j,dj in enumerate(degrees)]
  for ix in product(*rest):
   coeff=[]
   for m in range(dd+1):
    idx=list(ix);idx[i]=m
    coeff.append(values.get(tuple(idx),s.Integer(0))/comb(dd,m))
   for k in range(dd+1):
    idx=list(ix);idx[i]=k
    new[tuple(idx)]=sum(coeff[m]*comb(k,m) for m in range(k+1))
  values=new
 return degrees,values

for mode in (0,1):
 # mode0: 11<=M<=14, U=1; mode1: 14<=M<infinity, U=1/2+7/M.
 expr=n.subs(U,1 if mode==0 else s.Rational(1,2)+7*h)
 expr=s.expand(expr.subs({h:s.Rational(1,14)+s.Rational(3,154)*h
                         if mode==0 else h/14,
                         T:T},simultaneous=True))
 degrees,values=bernstein(expr,(h,A,T,u))
 assert degrees==((11,2,6,3) if mode==0 else (16,2,6,3))
 assert len(values)==(1008 if mode==0 else 1428)
 assert all(vv>=0 for vv in values.values())
 # These indices guarantee strict positivity whenever M is finite and t>0,
 # including all endpoints of A,T,u and the finite-M parameter interval.
 assert all(vv>0 for ix,vv in values.items() if ix[2]>0 and (mode==0 or ix[0]>0))
 assert sum(int(bool(vv==0)) for vv in values.values())==(48 if mode==0 else 94)
 print('PASS upper-cone mode',mode,'degrees',degrees,'coefficients',len(values),flush=True)
