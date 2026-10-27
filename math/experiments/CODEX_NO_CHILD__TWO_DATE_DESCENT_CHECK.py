"""Exact M14 two-date descent certificates, using outward dyadic intervals.
No floating arithmetic. Pair case uses the global first-alpha inequality;
triple case uses the semantic-source bound r=m/2<=11/312.
Unresolved boxes or arithmetic-domain failures cannot produce PASS.
"""
from fractions import Fraction as Q
from math import isqrt
BITS=80;UNIT=1<<BITS
class I:
 def __init__(self,a,b=None,raw=False):
  if raw:self.lo,self.hi=a,b;return
  a=Q(a);b=a if b is None else Q(b)
  self.lo=a.numerator*UNIT//a.denominator
  self.hi=-((-b.numerator*UNIT)//b.denominator)
 def __add__(a,b):
  b=b if isinstance(b,I) else I(b);return I(a.lo+b.lo,a.hi+b.hi,True)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo,True)
 def __sub__(a,b):return a+-I.coerce(b)
 def __rsub__(a,b):return I.coerce(b)+-a
 @staticmethod
 def coerce(a):return a if isinstance(a,I) else I(a)
 def __mul__(a,b):
  b=I.coerce(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
  return I(min(v)//UNIT,-((-max(v))//UNIT),True)
 __rmul__=__mul__
 def __truediv__(a,b):
  b=I.coerce(b)
  if b.lo<=0<=b.hi:raise ZeroDivisionError
  vals=[(x*UNIT,y) for x in(a.lo,a.hi) for y in(b.lo,b.hi)]
  return I(min(x//y for x,y in vals),max(-((-x)//y) for x,y in vals),True)
 def __rtruediv__(a,b):return I.coerce(b)/a
 def sqrt(a):
  assert a.lo>=0
  lo=isqrt(a.lo*UNIT);hi=isqrt(a.hi*UNIT)
  return I(lo,hi+(hi*hi<a.hi*UNIT),True)
 def __pow__(a,k):
  assert k>=0
  out=I(1)
  for _ in range(k):out=out*a
  return out
 def __repr__(a):return str((Q(a.lo,UNIT),Q(a.hi,UNIT)))
def prod(xs):
 out=I(1)
 for x in xs:out=out*x
 return out
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def solve(A,b):
 a=[list(row)+[rhs] for row,rhs in zip(A,b)]
 for j in range(4):
  kk=next((i for i in range(j,4) if a[i][j].lo>0 or a[i][j].hi<0),None)
  if kk is None:raise ZeroDivisionError
  a[j],a[kk]=a[kk],a[j];v=a[j][j];a[j]=[x/v for x in a[j]]
  for i in range(4):
   if i==j:continue
   v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[j])]
 return [a[i][4] for i in range(4)]
G=[[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]]
L=[[0,-4,14,-7],[14,0,-6,-6],[-6,-7,0,14],[-6,14,-6,0]]
pred=[2,0,3,1];k=[I(Q(v,205)) for v in[21,52,92,49]]
def last_root(lo,hi):
 z=I(lo,hi);ell=5*(1+z);h=14-5*z;cc=6+5*z;kk=6*z
 d=h*h-ell*kk;e=20*ell;a=cc*cc-ell*kk;b=20*kk
 A2=ell*(5*z*z+70*z+104)
 A1=(4+5*z)*a+ell*b+(7+5*z)*d+14*z*e
 A0=z*(70*z*z+2980*z-2264)
 disc=A1*A1+4*A2*A0
 y=-2*A0/(A1+disc.sqrt())
 x=[(kk+cc*y)/(h-ell*y),(a*y+b)/(d-e*y),z,y]
 n=[1/(1+v) for v in x];nu=prod(n)
 g=-dot(L[2],x)+5*(x[0]*x[1]+x[0]*x[3]+x[1]*x[3]+x[0]*x[1]*x[3])
 H=[prod(n[j] for j in range(4) if j!=i) for i in range(4)]
 B=[H[i]*dot(G[i],x) for i in range(4)]
 return x,n,nu,g,H,B

def pair_derivatives(lo,hi):
 x,n,nu,g,H,B=last_root(lo,hi);z=x[2]
 D=[]
 for i in range(4):
  row=[]
  for j in range(4):
   others=[x[v] for v in range(4) if v not in(i,j)]
   row.append(I(0) if i==j else L[i][j]-5*(sum(others)+prod(others)))
  D.append(row)
 u=solve(D,k);nd=dot(n,u)
 Bp=[]
 for i in range(4):
  deriv=[I(0) if j==i else 13*H[i]*n[j] if j==pred[i] else -(5+18*x[pred[i]])*H[i]*n[j] for j in range(4)]
  Bp.append(dot(deriv,u))
 Bp[2]=Bp[2]-g*H[2]*sum(n[i]*u[i] for i in[0,1,3])
 df=nu*g*(u[2]-z*nd);nf=-nu*(1+nd);debt=nu*z*g
 zz=B[0]/14;aa=(B[1]+6*zz)/(14-5*zz)
 zp=Bp[0]/14;ap=(Bp[1]+(6+5*aa)*zp)/(14-5*zz)
 q=zz/(1+zz);alpha=aa/(1+aa);qp=zp/(1+zz)**2;ap=ap/(1+aa)**2
 DA=-ap*(q*B[2]+(1-q)*debt)+(1-alpha)*(qp*(B[2]-debt)+q*Bp[2]+(1-q)*df)+6*(qp*alpha+q*ap)
 DB=-ap*(1-q)*nu+(1-alpha)*(-qp*nu+(1-q)*nf)
 R=(6*q-q*B[2]-(1-q)*debt)/((1-q)*nu)
 return DA,DB,DA+R*DB
def triple_derivatives(lo,hi,blo,bhi):
 x,n,nu,g,H,B=last_root(lo,hi);Z=x[2];b=I(blo,bhi)
 z=(B[0]+4*b)/(14-5*b);a=(B[1]+6*z)/(14-5*z)
 zp=(4+5*z)/(14-5*b);ap=(6+5*a)*zp/(14-5*z)
 k=nu*(Z*g+Q(11,312));t=B[2]+6*a+7*b+5*a*b
 num=k+z*t;numprime=zp*t+z*(6*ap+7+5*ap*b+5*a)
 logprime=ap/(1+a)+1/(1+b)+zp/(1+z)
 objective_numprime=numprime-num*logprime
 quietprime=14-6*ap-6*zp-5*(ap*b+a+ap*z+a*zp+z+b*zp+ap*b*z+a*z+a*b*zp)
 return [objective_numprime,quietprime,logprime,I(Q(1,50))-B[0],I(Q(1,10))-B[1],(1+a)*(1+b)*(1+z)]
for name,lo,hi,index in [('low',Q(3,25),Q(13,100),2),('high',Q(129,1000),Q(19,125),0)]:
 stack=[(lo,hi,0)];nodes=leaves=0;maxdepth=0;worst=None
 while stack:
  lo,hi,depth=stack.pop();nodes+=1;maxdepth=max(maxdepth,depth)
  try:
   vals=pair_derivatives(lo,hi)
   accepted=vals[1].hi<0 and vals[index].hi<0
  except (ZeroDivisionError,AssertionError):accepted=False
  if accepted:
   leaves+=1;worst=max(worst,vals[index].hi) if worst is not None else vals[index].hi;continue
  assert depth<22 and nodes<100000,('UNRESOLVED',name,lo,hi,depth)
  mid=(lo+hi)/2;stack.extend([(mid,hi,depth+1),(lo,mid,depth+1)])
 print('PASS',name,'nodes',nodes,'leaves',leaves,'maxdepth',maxdepth,'negative_upper_bound',Q(worst,UNIT),flush=True)

stack=[(Q(3,25),Q(19,125),Q(0),Q(3,200),0,0)]
nodes=leaves=0;maxdepth=0;worst=None
while stack:
 lo,hi,blo,bhi,dz,db=stack.pop();nodes+=1;maxdepth=max(maxdepth,dz+db)
 try:
  vals=triple_derivatives(lo,hi,blo,bhi);accepted=all(v.lo>0 for v in vals)
 except (ZeroDivisionError,AssertionError):accepted=False
 if accepted:
  leaves+=1;worst=min(worst,vals[0].lo) if worst is not None else vals[0].lo;continue
 assert dz+db<24 and nodes<100000,('UNRESOLVED',lo,hi,blo,bhi,dz,db)
 if dz<=db:
  mid=(lo+hi)/2;stack.extend([(mid,hi,blo,bhi,dz+1,db),(lo,mid,blo,bhi,dz+1,db)])
 else:
  mid=(blo+bhi)/2;stack.extend([(lo,hi,mid,bhi,dz,db+1),(lo,hi,blo,mid,dz,db+1)])
print('PASS first012 derivative, quiet3 preservation, coefficient bounds:',nodes,'nodes',leaves,'leaves','max total depth',maxdepth,'positive lower bound',Q(worst,UNIT))
