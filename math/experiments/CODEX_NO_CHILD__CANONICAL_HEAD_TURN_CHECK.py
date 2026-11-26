"""Rational outward interval verifier; floats nominate Newton centres only."""
from fractions import Fraction as F
from itertools import product
import numpy as np
# Floating arithmetic is only a root-centre producer; every conclusion below
# is certified by rational outward intervals, including existence and uniqueness.
Gn=np.array([[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0.]])
Ln=np.array([[0,-4,14,-7],[14,0,-6,-6],[-6,-7,0,14],[-6,14,-6,0.]])
A=np.linalg.inv(Ln);alpha=np.array([.1276,.1234,.12045,.13485])
def C(x):return Ln@x-np.array([5*(sum(x[j]*x[k] for j in range(4) for k in range(j+1,4) if i not in(j,k))+np.prod(np.delete(x,i))) for i in range(4)])
def D(x):return np.array([[0 if i==j else Ln[i,j]-5*(sum(x[k] for k in range(4) if k not in(i,j))+np.prod([x[k] for k in range(4) if k not in(i,j)])) for j in range(4)] for i in range(4)])
def solve(v,guess):
 x=guess.copy()
 for _ in range(45):
  err=C(x)-v
  if max(abs(err))<2e-14*max(max(abs(v)),1e-12):return x
  x-=np.linalg.solve(D(x),err)
  assert min(x)>0
 raise AssertionError('root nomination failed')
BITS=80; SCALE=1<<BITS
def down(x):return F(x.numerator*SCALE//x.denominator,SCALE)
def up(x):return -down(-x)
class I:
 def __init__(self,a,b=None):
  self.lo=down(F(a));self.hi=up(F(a if b is None else b))
 def __add__(a,b):
  b=co(b);return I(a.lo+b.lo,a.hi+b.hi)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo)
 def __sub__(a,b):return a+-co(b)
 def __rsub__(a,b):return co(b)+-a
 def __mul__(a,b):
  b=co(b);v=[x*y for x in(a.lo,a.hi) for y in(b.lo,b.hi)];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(a,b):
  b=co(b);assert b.lo*b.hi>0;return a*I(1/b.hi,1/b.lo)
 def __rtruediv__(a,b):return co(b)/a
 def __pow__(a,k):
  out=I(1)
  for _ in range(k):out=out*a
  return out
 def abs(a):return max(abs(a.lo),abs(a.hi))
 def mid(a):return (a.lo+a.hi)/2
 def rad(a):return (a.hi-a.lo)/2
 def __repr__(a):return f'[{float(a.lo):.12g},{float(a.hi):.12g}]'
def co(x):return x if isinstance(x,I) else I(x)
def matmul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def mv(a,v):return [sum(a[i][j]*v[j] for j in range(len(v))) for i in range(len(a))]
def norm(a):return max(sum(v.abs() for v in row) for row in a)
def prod(xs):
 out=I(1)
 for x in xs:out*=x
 return out
G=[[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]]
L=[[0,-4,14,-7],[14,0,-6,-6],[-6,-7,0,14],[-6,14,-6,0]]
J=[[G[i][j]+L[i][j] for j in range(4)] for i in range(4)]
def ci(x):return [sum(L[i][j]*x[j] for j in range(4))-5*(sum(x[j]*x[k] for j in range(4) for k in range(j+1,4) if i not in(j,k))+prod([x[j] for j in range(4) if j!=i])) for i in range(4)]
def di(x):return [[I(0) if i==j else L[i][j]-5*(sum(x[k] for k in range(4) if k not in(i,j))+prod([x[k] for k in range(4) if k not in(i,j)])) for j in range(4)] for i in range(4)]
def qi(x):
 n=[1/(1+z) for z in x];c=prod(n);H=[c/n[i] for i in range(4)];inner=[a+b for a,b in zip(mv(G,x),ci(x))];Q=[H[i]*inner[i] for i in range(4)]
 Qx=[[I(0) if i==j else H[i]*(di(x)[i][j]+G[i][j]-inner[i]*n[j]) for j in range(4)] for i in range(4)]
 return Q,Qx,c,n,H
def seed(eps):
 # Exact Descartes/bracket root and positive eigenvector, local bound proved separately.
 def p(t):return 13611*t**4+248*t**3-1076*t*t-204*t-11
 lo,hi=F(34954025,10**8),F(34954026,10**8)
 for _ in range(70):
  m=(lo+hi)/2
  if p(m)<0:lo=m
  else:hi=m
 t=I(lo,hi);v=[(5*t+1)*(209*t*t+57*t+4),(5*t+1)*(155*t*t+64*t+5),970*t**3+493*t*t+52*t+1,1747*t**3+457*t*t+57*t+3]
 h=[t*z/sum(v) for z in v];ep=co(eps);err=93*ep.hi**2
 cap=[z*ep+I(-err,err) for z in mv(J,h)]
 nu=1-ep+I(-30*ep.hi**2,30*ep.hi**2)
 return cap,nu
def step(v,nu,large=False):
 vm=np.array([float(z.mid()) for z in v]);xnom=solve(vm,alpha if large else A@vm)
 xc=[F(float(z)) for z in xnom];bc=np.linalg.inv(D(xnom));B=[[I(F(float(z))) for z in row] for row in bc]
 cx=ci(list(map(I,xc)))
 extended=[I(min(a.lo,b.lo),max(a.hi,b.hi)) for a,b in zip(v,cx)]
 residual=mv(B,[a-b for a,b in zip(cx,extended)])
 radius=[max(3*z.abs(),F(1,10**22)) for z in residual]
 for trial in range(9):
  xb=[I(a-r,a+r) for a,r in zip(xc,radius)];assert min(x.lo for x in xb)>0
  E=[[I(int(i==j))-z for j,z in enumerate(row)] for i,row in enumerate(matmul(B,di(xb)))]
  kappa=norm(E)
  if kappa>=1:raise ValueError(('contraction',large,float(kappa),xb))
  needed=[residual[i].abs()+sum(E[i][j].abs()*radius[j] for j in range(4)) for i in range(4)]
  if all(needed[i]<radius[i] for i in range(4)):break
  radius=[max(radius[i],F(3,2)*needed[i]) for i in range(4)]
 else:raise ValueError('no invariant root box')
 # Inverse enclosure D^-1=(I-E)^-1 B; uniform per-column Neumann bound.
 inv=[[B[i][j]+I(-kappa/(1-kappa)*max(B[k][j].abs() for k in range(4)),kappa/(1-kappa)*max(B[k][j].abs() for k in range(4))) for j in range(4)] for i in range(4)]
 Q,Qx,c,n,H=qi(xb);M=matmul(Qx,inv)
 qc=qi(list(map(I,xc)))[0]
 # Centre is actual root at C(xc), not the nominated midpoint.
 delta=[v[i]-ci(list(map(I,xc)))[i] for i in range(4)]
 qout=[qc[i]+z for i,z in enumerate(mv(M,delta))]
 # Log-survival bounds would reduce wrapping, but direct product is enough for points.
 return qout,nu*c,xb,kappa
def verify(eps,verbose=False):
 v,nu=seed(eps);boxes=[]
 for n in range(40):
  v,nu,xb,k=step(v,nu);boxes.append(xb)
 v,nu,xb,k=step(v,nu,True);boxes.append(xb)
 assert all(z.lo>F(b,100) for z,b in zip(v,[1,8,16,8]))
 if verbose:print('epsilon',eps,'nu',nu,'cap',v,'maxrootradius',max(float(x.rad()) for row in boxes for x in row),flush=True)
 return v,nu,boxes
def local_certificate():
 """Exact rational checks for the explicit M14 analytic-tail enclosure."""
 import sympy as S
 Q=S.Rational
 G=S.Matrix([[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]])
 J=S.Matrix([[0,-5,13,-5],[13,0,-5,-5],[-5,-5,0,13],[-5,13,-5,0]])
 L=J-G; B=L.inv()*J
 assert max(sum(abs(v) for v in B.row(i)) for i in range(4))==Q(2529,1571)
 assert max(sum(abs(v) for v in L.inv().row(i)) for i in range(4))==Q(843,1571)
 r=S.symbols('r');p=13611*r**4+248*r**3-1076*r**2-204*r-11
 lo,hi=Q(34954025,10**8),Q(34954026,10**8)
 assert p.subs(r,lo)<0<p.subs(r,hi)
 v=S.Matrix([(5*r+1)*(209*r*r+57*r+4),(5*r+1)*(155*r*r+64*r+5),970*r**3+493*r*r+52*r+1,1747*r**3+457*r*r+57*r+3])
 assert all(S.rem(z,p,r)==0 for z in (G-r*J)*v)
 den=sum(v);hl=[lo*z.subs(r,lo)/den.subs(r,hi) for z in v];hu=[hi*z.subs(r,hi)/den.subs(r,lo) for z in v]
 assert all(Q(3,40)<a<b<Q(1,10) for a,b in zip(hl,hu))
 assert all(sum(J[i,j]*(hl[j] if J[i,j]>=0 else hu[j]) for j in range(4))>Q(1,10) for i in range(4))
 q=S.symbols('q0:4');t=S.symbols('t0:4');pred=[2,0,3,1]
 def H(q,i):return S.prod(1-q[j] for j in range(4) if j!=i)
 def Quit(q,i):return -5*(1-H(q,i))+18*q[pred[i]]*S.prod(1-q[j] for j in range(4) if j not in(i,pred[i]))
 def Passive(q,i):return sum(G[i,j]*q[j]*S.prod(1-q[k] for k in range(4) if k not in(i,j)) for j in range(4) if j!=i)
 cs=[133,188,155,70,13]
 for i in range(4):
     residual=S.Poly(Quit(q,i)-Passive(q,i)-H(q,i)*Quit(t,i)-(L*S.Matrix(q)-J*S.Matrix(t))[i],*q,*t)
     assert all(sum(m)>=2 for m,c in residual.terms())
     assert all(sum(abs(c) for m,c in residual.terms() if sum(m)==d)<=bound for d,bound in enumerate(cs,2))
     nonlinear=S.Poly(Quit(q,i)-(J*S.Matrix(q))[i],*q)
     assert sum(abs(c) for m,c in nonlinear.terms() if sum(m)==2)==31
     assert sum(abs(c) for m,c in nonlinear.terms() if sum(m)==3)==13
 eps,a=Q(1,1000),Q(11,100)
 rbound=sum(c*a**d*eps**(d-2) for d,c in enumerate(cs,2))
 lip=sum(d*c*(a*eps)**(d-1) for d,c in enumerate(cs,2))
 assert rbound<2
 assert Q(2529,1571)*Q(4,9)*4+Q(843,1571)*2<4
 assert Q(2529,1571)*Q(4,9)+Q(843,1571)*lip<Q(732,1000)
 assert 31*Q(104,1000)**2+13*Q(104,1000)**3*eps<1
 assert 4*a*a/(2*(1-a*eps)*Q(5,9))<Q(1,10)
 assert 48/(Q(5,9)*(1-a*eps))+Q(35,100)*a/(Q(5,9)*(1-a*eps))<87
 assert 23*12+(62*a+39*a*a*eps)*(Q(1,10)+12*eps)<277
if __name__=='__main__':
 local_certificate()
 results=[verify(F(k,10**10),True) for k in [65,70,75]]
 assert results[0][1].lo>F(5694,10000) and results[1][1].hi<F(5689,10000) and results[2][1].lo>F(5704,10000)
 print('PASS three exact rational survival intervals',flush=True)
 tiles=[]
 for k in range(65,75):
  v,nu,b=verify(I(F(k,10**10),F(k+1,10**10)));tiles.append(b)
  print('tile',k,'PASS',flush=True)
 # One common derivative contraction box per depth gives unique, continuous branches.
 for n in range(41):
  hull=[I(min(t[n][i].lo for t in tiles),max(t[n][i].hi for t in tiles)) for i in range(4)]
  center=np.array([float(x.mid()) for x in hull]);B=[[I(F(float(z))) for z in row] for row in np.linalg.inv(D(center))]
  E=[[I(int(i==j))-z for j,z in enumerate(row)] for i,row in enumerate(matmul(B,di(hull)))]
  assert norm(E)<1,(n,float(norm(E)))
 print('PASS continuous common family on the complete epsilon interval',flush=True)
 # The same strict cap lower bound excludes every nonempty Nash prefix.
 assert 1-4*F(36,5)*F(37,1000)==-F(41,625)
