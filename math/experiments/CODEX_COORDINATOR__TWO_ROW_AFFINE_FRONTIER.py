"""Exact affine stationary frontier for the two-row complex-spectrum family.
Proves delta in [0,38/25], epsilon in [737/1000+3delta/50,2].
Python3 plus SymPy, NumPy, SciPy. No external data files.
Floats only propose rational candidates. Every acceptance uses exact rational
coefficients or outward dyadic integer intervals.
"""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt
import time
BITS=256;D=1<<BITS
class Iv:
 def __init__(self,lo,hi=None,raw=False):
  if raw:self.lo,self.hi=lo,hi;return
  x=F(lo);self.lo=x.numerator*D//x.denominator;self.hi=-((-x.numerator*D)//x.denominator)
 @classmethod
 def box(cls,c,r):
  a=cls(F(c)-F(r));b=cls(F(c)+F(r));return cls(a.lo,b.hi,True)
 def __add__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);return Iv(self.lo+o.lo,self.hi+o.hi,True)
 __radd__=__add__
 def __neg__(self):return Iv(-self.hi,-self.lo,True)
 def __sub__(self,o):return self+-iv(o)
 def __rsub__(self,o):return iv(o)+-self
 def __mul__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);xs=[a*b for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(xs)//D,-((-max(xs))//D),True)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=iv(o);assert not o.lo<=0<=o.hi,('zero denominator',o.lo,o.hi)
  pairs=[(a*D,b)for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(a//b for a,b in pairs),max(-((-a)//b)for a,b in pairs),True)
 def __rtruediv__(self,o):return iv(o)/self
 def sqrt(self):
  assert self.lo>0
  a=isqrt(self.lo*D);b=isqrt(self.hi*D)
  return Iv(a,b+(b*b<self.hi*D),True)
 def absupper(self):return max(-self.lo,self.hi)
 def lower(self):return float(F(self.lo,D))
 def upper(self):return float(F(self.hi,D))
 def __repr__(self):return str((self.lower(),self.upper()))
def iv(x):return x if isinstance(x,Iv)else Iv(x)
class Jet:
 def __init__(self,v,d=None):self.v=iv(v);self.d=[Iv(0)]*5 if d is None else d
 def __add__(self,o):
  o=jet(o);return Jet(self.v+o.v,[a+b for a,b in zip(self.d,o.d)])
 __radd__=__add__
 def __neg__(self):return Jet(-self.v,[-x for x in self.d])
 def __sub__(self,o):return self+-jet(o)
 def __rsub__(self,o):return jet(o)+-self
 def __mul__(self,o):
  o=jet(o);return Jet(self.v*o.v,[a*o.v+self.v*b for a,b in zip(self.d,o.d)])
 __rmul__=__mul__
 def __truediv__(self,o):
  o=jet(o);v=self.v/o.v
  return Jet(v,[(a-v*b)/o.v for a,b in zip(self.d,o.d)])
 def __rtruediv__(self,o):return jet(o)/self
 def sqrt(self):
  v=self.v.sqrt();return Jet(v,[a/(2*v)for a in self.d])
def jet(x):return x if isinstance(x,Jet)else Jet(x)

A=[[F(x)for x in row]for row in[[0,1,-6,'-.01'],[1,0,'-1.5','-.4'],[0,'-.6',0,1],['-.07','-.04',1,0]]]
J=[[F(x)for x in row]for row in[[0,'.01','5.4','.001'],['.01',0,'.15','.36'],[0,'.54',0,'.01'],['.063','.004','.01',0]]]
Z={}
for i in range(4):
 Z[i,1<<i]=F(0)
 for j in range(4):
  if i!=j:Z[i,1<<j]=A[i][j]+J[i][j];Z[i,(1<<i)|(1<<j)]=J[i][j]
for pair,sg in zip(combinations(range(4),2),(1,-1,1,1,-1,-1)):
 mask=sum(1<<j for j in pair);outside=[i for i in range(4)if i not in pair]
 for n,i in enumerate(outside):
  delta=sg*(-1 if n else 1);Z[i,mask]=F(max(0,-delta));Z[i,mask|(1<<i)]=F(max(0,delta))
for i in range(4):Z[i,15^(1<<i)]=F(1);Z[i,15]=F(0)
assert len(Z)==60


import sys
m=sys.modules[__name__]
R=F
I=range(3)

def fields(v,x,delta):
 q=[v[0],v[1],x,v[2]];out=[]
 for a in range(4):
  opp=[i for i in range(4)if i!=a];H=m.Jet(1);P=m.Jet(0);Q=m.Jet(0)
  for i in opp:H*=1-q[i]
  for mask in range(16):
   if mask>>a&1:continue
   w=m.Jet(1)
   for i in opp:w*=q[i]if mask>>i&1 else 1-q[i]
   pv=m.Z.get((a,mask),R(0));qv=m.Z[a,mask|(1<<a)]
   if a==2 and mask==1:pv=-R(9,10)*delta;qv=delta/10
   # epsilon=0 base, rather than original epsilon=1/25.
   if a==3 and mask==2:pv=0;qv=0
   if mask:P+=w*pv
   Q+=w*qv
  out.append((1-H)*Q-P)
 return out

def solve(a,b):
 rows=[list(v)+[w]for v,w in zip(a,b)]
 for j in I:
  k=next(k for k in range(j,3)if rows[k][j]);rows[j],rows[k]=rows[k],rows[j]
  t=rows[j][j];rows[j]=[u/t for u in rows[j]]
  for k in I:
   if k==j:continue
   t=rows[k][j];rows[k]=[u-t*v for u,v in zip(rows[k],rows[j])]
 return [row[-1]for row in rows]

def ev(c,x,d):
 return fields([m.Jet(v,[m.Iv(int(i==j))for j in range(5)])for i,v in enumerate(c)],m.Jet(x,[m.Iv(0)]*3+[m.Iv(1),m.Iv(0)]),m.Jet(d,[m.Iv(0)]*4+[m.Iv(1)]))
def roundrat(v):return R((v.numerator*10**24)//v.denominator,10**24)
# Floating solves propose rational candidates only; interval tests establish every claim.
import numpy as np
from scipy.optimize import root
import sympy as sy
_p0,_p1,_xx,_yy,_dd,_ee=sy.symbols('p0 p1 x y D E')
_qq=[_p0,_p1,_xx,_yy]
_zz={key:sy.Rational(value.numerator,value.denominator)for key,value in Z.items()}
_zz[2,1]=-sy.Rational(9,10)*_dd;_zz[2,5]=_dd/10
_zz[3,2]=-sy.Rational(9,10)*_ee;_zz[3,10]=_ee/10
_sf=[]
for _i in range(4):
 _op=[_j for _j in range(4)if _j!=_i]
 _H=sy.prod(1-_qq[_j]for _j in _op);_P=sy.Rational(0);_Q=sy.Rational(0)
 for _mask in range(16):
  if _mask>>_i&1:continue
  _weight=sy.prod(_qq[_j]if _mask>>_j&1 else 1-_qq[_j]for _j in _op)
  _P+=_weight*_zz.get((_i,_mask),sy.Rational(0))
  _Q+=_weight*_zz[_i,_mask|(1<<_i)]
 _sf.append(sy.expand((1-_H)*_Q-_P))
_ctx={'F':_sf,'p0':_p0,'p1':_p1,'x':_xx,'y':_yy,'D':_dd,'E':_ee}

_sf=_ctx['F'];_p0=_ctx['p0'];_p1=_ctx['p1'];_xx=_ctx['x'];_yy=_ctx['y'];_dd=_ctx['D'];_ee=_ctx['E']
_recovered=sy.Matrix(_sf[:3]).subs(_ee,0).subs(_xx,_xx-sy.Rational(3,100)*_dd)
_nf=sy.lambdify((_p0,_p1,_yy,_xx,_dd),_recovered,'numpy')
_nj=sy.lambdify((_p0,_p1,_yy,_xx,_dd),_recovered.jacobian([_p0,_p1,_yy]),'numpy')
# Exact Horner evaluation of the literal stationary polynomials.
def _horner(expr,variables):
 if not variables:
  a=sy.Rational(expr);return 'R(%d,%d)'%(a.p,a.q)
 var=variables[0];poly=sy.Poly(expr,var);out=None
 for coefficient in poly.all_coeffs():
  ss=_horner(coefficient,variables[1:])
  if out is None:out=ss
  else:out='('+out+'*'+str(var)+'+'+ss+')'
 return out
_horner_functions=[]
for _expr in _sf:
 _code=_horner(_expr.subs(_ee,0),[_p0,_p1,_xx,_yy,_dd])
 _horner_functions.append(eval('lambda p0,p1,x,y,D: '+_code,{'R':R}))
_fields_literal=fields
def fields(v,x,delta):
 return [ff(v[0],v[1],x-R(3,100)*delta,v[2],delta)for ff in _horner_functions]

def candidate(x,d,seed):
 so=root(lambda v:np.array(_nf(*v,float(x),float(d))).ravel(),[float(v)for v in seed],jac=lambda v:_nj(*v,float(x),float(d)),tol=1e-11)
 c=[R(str(v))for v in so.x]
 mid=lambda v:R(v.lo+v.hi,2*m.D)
 ff=ev(c,x,d);jj=[[mid(ff[a].d[j])for j in I]for a in I]
 cols=[solve(jj,[R(int(i==j))for i in I])for j in I]
 B=[[cols[j][i]for j in I]for i in I]
 S=[solve(jj,[-mid(ff[a].d[3+k])for a in I])for k in range(2)]
 S=[[roundrat(v)for v in col]for col in S]
 return c,S,B

class Poly2:
 def __init__(self,v):self.c={k:R(a)for k,a in v.items()if a}if isinstance(v,dict)else({(0,0):R(v)}if v else{})
 def __add__(self,o):
  o=o if isinstance(o,Poly2)else Poly2(o);d=self.c.copy()
  for k,v in o.c.items():d[k]=d.get(k,R(0))+v
  return Poly2(d)
 __radd__=__add__
 def __neg__(self):return Poly2({k:-v for k,v in self.c.items()})
 def __sub__(self,o):return self+-o
 def __rsub__(self,o):return -self+o
 def __mul__(self,o):
  o=o if isinstance(o,Poly2)else Poly2(o);d={}
  for (i,j),a in self.c.items():
   for (k,l),b in o.c.items():d[i+k,j+l]=d.get((i+k,j+l),R(0))+a*b
  return Poly2(d)
 __rmul__=__mul__
 def absbound(self):return sum(abs(v)for v in self.c.values())

def verify(l,u,dl,du,prev=None,radius=R(1,200)):
 xm=(l+u)/2;hx=(u-l)/2;dm=(dl+du)/2;hd=(du-dl)/2
 assert 0<l-R(3,100)*du<=u-R(3,100)*dl<1
 seed=[R('.14'),R('.2'),R('.1')+dm/10]if prev is None else[prev['c'][i]+prev['S'][0][i]*(xm-prev['xm'])for i in I]
 c,S,Br=candidate(xm,dm,seed);B=[[m.Iv(t)for t in row]for row in Br];weights=[R(1,10)+abs(S[0][i])+abs(S[1][i])for i in I];r=[radius*w/max(weights)for w in weights]
 v=[m.Jet(m.Iv.box(c[i],r[i]+abs(S[0][i])*hx+abs(S[1][i])*hd),[m.Iv(int(i==j))for j in range(5)])for i in I]
 for a in v:assert 0<a.v.lo<a.v.hi<m.D,('proper',float(l),float(dl),c)
 ff=fields(v,m.Jet(m.Iv.box(xm,hx),[m.Iv(0)]*3+[m.Iv(1),m.Iv(0)]),m.Jet(m.Iv.box(dm,hd),[m.Iv(0)]*4+[m.Iv(1)]))
 K=[[m.Iv(int(i==j))-sum((B[i][k]*ff[k].d[j]for k in I),m.Iv(0))for j in I]for i in I]
 pc=[Poly2({(0,0):c[i],(1,0):S[0][i]*hx,(0,1):S[1][i]*hd})for i in I]
 pf=fields(pc,Poly2({(0,0):xm,(1,0):hx}),Poly2({(0,0):dm,(0,1):hd}))
 RR=[sum((-Br[i][k]*pf[k]for k in I),Poly2(0)).absbound()for i in I]
 MM=[sum(R(K[i][j].absupper(),m.D)*r[j]for j in I)for i in I]
 lip=max(MM[i]/r[i]for i in I)
 assert lip<R(1,2),('lip',float(l),float(dl),float(lip))
 assert all(RR[i]+MM[i]/4<r[i]/4 for i in I),('inner',float(l),float(dl),[float((RR[i]+MM[i]/4)/r[i])for i in I])
 if prev:
  gap=[abs(c[i]+S[0][i]*(l-xm)-prev['c'][i]-prev['S'][0][i]*(l-prev['xm']))+abs(S[1][i]-prev['S'][1][i])*hd+prev['r'][i]/4 for i in I]
  assert all(gap[i]<r[i]for i in I),('seam',float(l),float(dl))
 return dict(c=c,S=S,B=B,r=r,xm=xm,dm=dm,hx=hx,hd=hd,dl=dl,du=du,l=l,u=u,lip=lip)

def epsilon_at(cell,x):
 v=[m.Jet(m.Iv.box(cell['c'][i]+cell['S'][0][i]*(x-cell['xm']),cell['r'][i]/4+abs(cell['S'][1][i])*cell['hd']))for i in I]
 f=fields(v,m.Jet(x),m.Jet(m.Iv.box(cell['dm'],cell['hd'])))[3].v
 qx=m.Iv(x)-R(3,100)*m.Iv.box(cell['dm'],cell['hd'])
 H=(1-v[0].v)*(1-v[1].v)*(1-qx)
 coef=(1-H/10)*v[1].v*(1-v[0].v)*(1-qx)
 assert coef.lo>0
 return -f/coef

def refined_left(first):
 dl=first['dl'];du=first['du'];worst=R(0);count=0
 while dl<du:
  end=min(du,dl+R(1,500));tiny=verify(R(11,100),R(11,100),dl,end,None,R(1,100000))
  dm=tiny['dm'];hd=tiny['hd']
  for i in I:
   parent=first['c'][i]+first['S'][0][i]*(R(11,100)-first['xm'])+first['S'][1][i]*(dm-first['dm'])
   gap=abs(tiny['c'][i]-parent)+abs(tiny['S'][1][i]-first['S'][1][i])*hd+tiny['r'][i]/4
   assert gap<first['r'][i],('endpoint_identification',float(dl))
  el=epsilon_at(tiny,R(11,100));target=R(737,1000)+R(3,50)*dl
  assert R(el.hi,m.D)<target,('sharp_left',float(dl),el,float(target))
  worst=max(worst,R(el.hi,m.D)-R(3,50)*dl);dl=end;count+=1
 return worst,count

if __name__=='__main__':
 start=time.time();count=0;finecount=0;dl=R(0);top=R(38,25);worst=R(0);maxleft=R(-10);minright=R(100)
 while dl<top:
  dd=R(1,50)if dl<R(1)else(R(1,100)if dl<R(7,5)else R(1,500))
  du=min(top,dl+dd);l=R(11,100);prev=None;first=None;slabcount=0
  while l<R(2,5):
   dx=R(1,200);passed=False
   while not passed:
    u=min(R(2,5),l+dx)
    for radius in [R(1,100),R(1,200),R(1,400),R(1,800),R(1,1600),R(1,3200)]:
     try:
      cell=verify(l,u,dl,du,prev,radius);passed=True;break
     except AssertionError:pass
    if not passed:
     dx/=2
     assert dx>=R(1,102400),('excessive refinement',float(l),float(dl))
   prev=cell;first=first or cell;l=u;count+=1;slabcount+=1;worst=max(worst,cell['lip'])
  el,nn=refined_left(first);finecount+=nn;er=epsilon_at(prev,R(2,5))
  assert er.lo>2*m.D,('right_eps',float(dl),er)
  maxleft=max(maxleft,el);minright=min(minright,R(er.lo,m.D))
  print('PASS_SLAB',float(dl),float(du),'cells',slabcount,count,'eps_offset_upper',float(el),'right',er,'seconds',time.time()-start,flush=True)
  dl=du
 print('PASS_ALL',count,'endpointcells',finecount,'maxlip',float(worst),'epsilon_offset_upper',float(maxleft),'right_lower',float(minright),'seconds',time.time()-start)
