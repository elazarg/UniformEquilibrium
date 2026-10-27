"""M14 return certificate. Exact rational outward intervals verify every claim.
NumPy only nominates Newton centers; SymPy verifies fixed rational identities.
No external files or numerical tolerance can make an inclusion test pass.
"""
from fractions import Fraction as F
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
import numpy as np
import sympy as sp
L=[[0,-4,-7],[14,0,-6],[-6,14,0]]
J=[[0,-5,-5],[13,0,-5],[-5,13,0]]
G=[[0,-1,2],[-1,0,1],[1,-1,0]]
Ln=np.array(L,dtype=float)
T=[[1000,876,-550],[398,-774,-1000],[89,-1000,960]]
Ti=[[F(z.p,z.q) for z in row] for row in sp.Matrix(T).inv().tolist()]
Tn=np.array(T,dtype=float);Tin=np.linalg.inv(Tn)
def ci(x):
 return [sum(L[i][j]*x[j] for j in range(3))-5*prod([x[j] for j in range(3) if j!=i]) for i in range(3)]
def di(x):
 return [[I(0) if i==j else L[i][j]-5*x[3-i-j] for j in range(3)] for i in range(3)]
def cn(x):return Ln@x-np.array([5*np.prod(np.delete(x,i)) for i in range(3)])
def dn(x):return np.array([[0 if i==j else L[i][j]-5*x[3-i-j] for j in range(3)] for i in range(3)])
def nominate(v):
 x=np.linalg.solve(Ln,v)
 for k in range(40):
  e=cn(x)-v
  if max(abs(e))<1e-13*max(max(abs(v)),1e-12):return x
  x-=np.linalg.solve(dn(x),e)
 raise AssertionError('nomination failed')
def qi(x):
 H=[prod([1/(1+x[j]) for j in range(3) if j!=i]) for i in range(3)]
 inner=[sum(J[i][j]*x[j] for j in range(3))-5*prod([x[j] for j in range(3) if j!=i]) for i in range(3)]
 Q=[H[i]*inner[i] for i in range(3)]
 Qx=[[I(0) if i==j else H[i]*(J[i][j]-5*x[3-i-j]-inner[i]/(1+x[j])) for j in range(3)] for i in range(3)]
 return Q,Qx
def step(z,bp):
 vo=mv(T,z);vm=np.array([float(x.mid()) for x in vo]);xn=nominate(vm)
 xc=[F(float(x)) for x in xn];B=[[I(F(float(v))) for v in row] for row in np.linalg.inv(dn(xn))]
 cx=ci(list(map(I,xc)));zc=mv(Ti,cx)
 zext=[I(min(z[i].lo,zc[i].lo),max(z[i].hi,zc[i].hi)) for i in range(3)]
 vext=mv(T,zext)
 residual=mv(B,[cx[i]-vext[i] for i in range(3)])
 rad=[max(2*r.abs(),F(1,10**21)) for r in residual]
 for k in range(10):
  xb=[I(x-r,x+r) for x,r in zip(xc,rad)]
  assert min(a.lo for a in xb)>0 and max(a.hi for a in xb)<F(1,10),('positive small root',xb)
  E=[[I(int(i==j))-v for j,v in enumerate(row)] for i,row in enumerate(matmul(B,di(xb)))]
  kap=norm(E);assert kap<1,('Newton contraction',float(kap))
  need=[residual[i].abs()+sum(E[i][j].abs()*rad[j] for j in range(3)) for i in range(3)]
  if all(need[i]<rad[i] for i in range(3)):break
  rad=[max(rad[i],F(3,2)*need[i]) for i in range(3)]
 else:raise AssertionError('selfmap failed')
 inv=[[B[i][j]+I(-kap/(1-kap)*max(B[k][j].abs() for k in range(3)),kap/(1-kap)*max(B[k][j].abs() for k in range(3))) for j in range(3)] for i in range(3)]
 Q,Qx=qi(xb);Qc=qi(list(map(I,xc)))[0]
 Zc=mv(Ti,Qc);Dz=matmul(matmul(matmul(Ti,Qx),inv),T)
 delta=[z[i]-zc[i] for i in range(3)]
 zn=[Zc[i]+v for i,v in enumerate(mv(Dz,delta))]
 # Pivot is quiet. Its full prescribed/cap value uses the same root cap.
 H=prod([1/(1+x) for x in xb]);a=xb[0]+2*xb[1]-xb[2]
 C2=-6*xb[0]-7*xb[1]+14*xb[2]-5*(xb[0]*xb[1]+xb[0]*xb[2]+xb[1]*xb[2]+prod(xb))
 assert bp.lo>C2.hi,('quiet pivot',bp,C2)
 bmid=bp.mid();hc=prod([1/(1+I(x)) for x in xc]);ac=I(xc[0])+2*I(xc[1])-I(xc[2])
 bcenter=hc*(ac+bmid)
 ep_x=[[H*(g-(a+bp)/(1+x)) for g,x in zip([1,2,-1],xb)]]
 ep_z=matmul(matmul(ep_x,inv),T)[0]
 bn=bcenter+sum(ep_z[i]*delta[i] for i in range(3))+H*(bp-bmid)
 return zn,bn,xb
def verify(lo,hi,n=305):
 t=I(lo/(18+133*lo),hi/(18+133*hi))
 bp=104*t;z=[sum(Ti[i][j]*v for j,v in enumerate([-25,0,65]))*t for i in range(3)]
 maxkap=0
 for k in range(n):
  z,bp,x=step(z,bp)
  if k in [0,49,99,199,304] and hi-lo>F(1,100):print(k,bp,x,flush=True)
 assert x[1].hi<F(1,100000),(lo,hi,x)
 assert x[0].lo>F(3,5)*x[1].hi and x[0].hi<F(9,10)*x[1].lo,('cone0',x)
 assert x[2].lo>F(2,5)*x[1].hi and x[2].hi<F(4,5)*x[1].lo,('cone3',x)
 err=640*x[1].hi
 assert bp.lo-err>F(849,1000) and bp.hi+err<F(861,1000),(lo,hi,bp,float(err))
 return I(bp.lo-err,bp.hi+err)
def prefix_certificate():
 s=sp;b=s.symbols('b',positive=True);c=b/(1+6*b)
 G=s.Matrix([[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]])
 L=s.Matrix([[0,-4,14,-7],[14,0,-6,-6],[-6,-7,0,14],[-6,14,-6,0]])
 state=s.Matrix([0,0,b,0]);surv=s.Integer(1)
 for j,p in [(3,b/(1+b)),(2,2*b/(1+3*b)),(0,3*b/(1+6*b))]:
  assert state[j]==0
  state=((1-p)*state+p*G[:,j]).applyfunc(s.factor);surv=s.factor(surv*(1-p))
 assert state==s.Matrix([0,0,3*c,5*c]) and s.factor(surv-1/(1+6*b))==0
 ystar=10*c/9;astar=ystar/(1+ystar)
 assert s.Rational(4,5)**6<s.Rational(9,28)
 for k in range(8):
  a=-state[0];odds=s.Rational(4,5)**6*ystar if k==0 else a/4
  assert s.factor(state[1])==0
  gaps=[s.factor(state[i]-L[i,1]*odds) for i in (0,2,3)]
  if k==0:
   assert s.factor(gaps[2]-c*(5-s.Rational(140,9)*s.Rational(4,5)**6))==0
  else:
   assert gaps[0]==0
   assert s.factor(gaps[2]-(s.Rational(9,2)+5*c)*(astar-a))==0
   if k<7:assert s.factor(a/(1-a)-ystar*s.Rational(4,5)**(7-k))==0
   else:assert s.factor(a-astar)==0
  state=((state+odds*G[:,1])/(1+odds)).applyfunc(s.factor);surv=s.factor(surv/(1+odds))
 lam=b/(18+133*b)
 assert (state-lam*s.Matrix([-25,0,104,65])).applyfunc(s.factor)==s.zeros(4,1)
 assert s.factor(surv-18/(18+133*b))==0
 assert lam.subs(b,s.Rational(4,5))==s.Rational(2,311)
 assert lam.subs(b,s.Rational(9,10))==s.Rational(1,153)
 assert surv.subs(b,s.Rational(4,5))==s.Rational(45,311)
 print('PASS exact singleton-flow and eight-atom prefix identities.',flush=True)
def tail_certificate():
 s=sp;Q=s.Rational;Lm=s.Matrix(L);Jm=s.Matrix(J);B=Lm.inv()*Jm
 assert max(sum(abs(a) for a in Lm.inv().row(i)) for i in range(3))==Q(69,379)
 assert max(sum(abs(a) for a in B.row(i)) for i in range(3))<Q(26,25)
 assert max(sum(abs(a) for a in Jm.row(i)) for i in range(3))==18
 t=Q(1,100000)
 assert Q(26,25)+12*t<2 and Q(69,379)*(42+20)<12
 assert Q(69,379)*20*t<1
 for r in [Q(3,5),Q(9,10)]:
  for u in [Q(2,5),Q(4,5)]:
   w=B*s.Matrix([r,1,u])
   assert min(w)>12*t and w[1]+12*t<Q(99,100)
   assert w[0]-Q(3,5)*w[1]>12*Q(8,5)*t
   assert Q(9,10)*w[1]-w[0]>12*Q(19,10)*t
   assert w[2]-Q(2,5)*w[1]>12*Q(7,5)*t
   assert Q(4,5)*w[1]-w[2]>12*Q(9,5)*t
 assert Q(32,5)/(1-Q(99,100))==640
 assert 14*Q(4,5)*t<Q(7,10)
 print('PASS analytic positive-cone contraction and uniform pivot-tail remainder.',flush=True)
if __name__=='__main__':
 prefix_certificate();tail_certificate()
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--tiles',type=int,default=10);a=p.parse_args()
 for k in range(a.tiles):
  lo=F(4,5)+F(k,10*a.tiles);hi=F(4,5)+F(k+1,10*a.tiles)
  out=verify(lo,hi);print('PASS tile',k,'input',float(lo),float(hi),'return',out,flush=True)
