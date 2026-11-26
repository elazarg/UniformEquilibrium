"""Low-delta exact graph continuation pilots; inherited complete-history kernel.
Target delta [.002,.12] below the stationary frontier.
A completed full-cover run is required; partial/pilot runs prove only their cells.
Standard library only. Floats propose; all acceptance uses exact intervals.
"""
if not __debug__:raise RuntimeError('Assertions are required; do not use -O.')
import sys,time
from fractions import Fraction as F
from itertools import combinations
from math import isqrt
import time
BITS=512;D=1<<BITS
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
 def __init__(self,v,d=None):self.v=iv(v);self.d=[Iv(0)]*6 if d is None else d
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


I=range(4);N=6

def float_inverse(a):
 n=len(a);v=[list(row)+[float(i==j)for j in range(n)]for i,row in enumerate(a)]
 for k in range(n):
  j=max(range(k,n),key=lambda j:abs(v[j][k]));v[k],v[j]=v[j],v[k]
  piv=v[k][k];assert abs(piv)>1e-16;v[k]=[x/piv for x in v[k]]
  for i in range(n):
   if i!=k:
    fac=v[i][k];v[i]=[x-fac*y for x,y in zip(v[i],v[k])]
 return[row[n:]for row in v]

def float_gap_jac(q,b,d,e):
 return gaps(q,b,d,e),qjac(q,b,d,e)

def float_newton(S,q,b,d,e):
 q=q[:]
 for _ in range(12):
  g,A=float_gap_jac(q,b,d,e);C=float_inverse([[A[i][j]for j in S]for i in S])
  err=mv(C,[g[i]for i in S])
  for i,x in zip(S,err):q[i]-=x
  if max(abs(x)for x in err)<1e-14:break
 assert max(abs(gaps(q,b,d,e)[i])for i in S)<1e-10
 return q,C

def float_triple(b,S,d,e):
 i,j,k=S;aa=[[float(x)for x in row]for row in A];aa[2][0]=-d;aa[3][1]=-e;z=rewards(d,e)
 def cf(a,u,v):
  dd=float(z[a,(1<<a)|(1<<u)|(1<<v)]-z[a,(1<<u)|(1<<v)])
  return-b[a],b[a]-aa[a][u],b[a]-aa[a][v],dd+aa[a][u]+aa[a][v]-b[a]
 ci,ai,bi,di=cf(i,j,k);cj,aj,bj,dj=cf(j,i,k);ck,ak,bk,dk=cf(k,i,j)
 nx=[-cj,-bj];dx=[aj,dj];ny=[-ci,-bi];dy=[ai,di]
 def mul2(a,b):return[a[0]*b[0],a[0]*b[1]+a[1]*b[0],a[1]*b[1]]
 terms=[mul2(dx,dy),mul2(nx,dy),mul2(ny,dx),mul2(nx,ny)]
 cc=[sum(t[l]*x for t,x in zip(terms,[ck,ak,bk,dk]))for l in range(3)]
 from math import sqrt
 zz=(-cc[1]+sqrt(cc[1]*cc[1]-4*cc[2]*cc[0]))/(2*cc[2]);q=[0.]*4
 q[i]=(nx[0]+nx[1]*zz)/(dx[0]+dx[1]*zz);q[j]=(ny[0]+ny[1]*zz)/(dy[0]+dy[1]*zz);q[k]=zz
 return q

mid=lambda x:F(x.lo+x.hi,2*D)
mag=lambda x:F(x.absupper(),D)

def hull(a,b):return Iv(min(a.lo,b.lo),max(a.hi,b.hi),True)
def around(a,r):return Iv(a.lo-Iv(r).hi,a.hi+Iv(r).hi,True)
def mm(a,b):return[[sum(x*y for x,y in zip(row,col))for col in zip(*b)]for row in a]
def mv(a,b):return[sum(x*y for x,y in zip(row,b))for row in a]
def eye(n):return[[Iv(int(i==j))for j in range(n)]for i in range(n)]
def inv_pre(a,c):
 n=len(a);v=[r+s for r,s in zip(mm(c,a),[[Iv(x)for x in r]for r in c])]
 for k in range(n):
  piv=v[k][k];assert piv.lo>0;v[k]=[x/piv for x in v[k]]
  for i in range(n):
   if i!=k:
    fac=v[i][k];v[i]=[x-fac*y for x,y in zip(v[i],v[k])]
 return[r[n:]for r in v]

def rewards(delta,eps):
 z=dict(Z);z[2,1]=-F(9,10)*delta;z[2,5]=delta/10;z[3,2]=-F(9,10)*eps;z[3,10]=eps/10
 return z

def raw_evaluate(q,b,delta,eps):
 z=rewards(delta,eps);pp=[];qq=[];hh=[];gg=[]
 for i in I:
  opp=[j for j in I if j!=i];P=0;Q=0;H=1
  for j in opp:H*=1-q[j]
  for mask0 in range(8):
   mask=0;w=1
   for k,j in enumerate(opp):
    if mask0>>k&1:mask|=1<<j;w*=q[j]
    else:w*=1-q[j]
   if mask:P+=w*z[i,mask]
   Q+=w*z[i,mask|(1<<i)]
  pp.append(P);qq.append(Q);hh.append(H);gg.append(Q-P-H*b[i])
 return pp,qq,hh,gg

C_193_100=F(193,100)
C_1_10=F(1,10)
C_1_100=F(1,100)
C_1_1000=F(1,1000)
C_23_50=F(23,50)
C_27_5=F(27,5)
C_27_50=F(27,50)
C_2_5=F(2,5)
C_3_2=F(3,2)
C_3_20=F(3,20)
C_3_5=F(3,5)
C_4411_1000=F(4411,1000)
C_49_100=F(49,100)
C_501_100=F(501,100)
C_63_100=F(63,100)
C_63_1000=F(63,1000)
C_7_100=F(7,100)
C_7_5=F(7,5)
C_8_5=F(8,5)
C_927_1000=F(927,1000)
C_9_20=F(9,20)
C_9_25=F(9,25)
C_m107_100=F(-107,100)
C_m11_10=F(-11,10)
C_m11_1000=F(-11,1000)
C_m12_5=F(-12,5)
C_m1_100=F(-1,100)
C_m29_20=F(-29,20)
C_m37_25=F(-37,25)
C_m3_2=F(-3,2)
C_m441_100=F(-441,100)
C_m4_25=F(-4,25)
C_m5401_1000=F(-5401,1000)
C_m63_1000=F(-63,1000)
C_m701_100=F(-701,100)
C_m927_1000=F(-927,1000)
C_m93_100=F(-93,100)
C_m9_10=F(-9,10)

def evaluate(q,b,delta,eps):
 q0,q1,q2,q3=q
 t0=(C_1_100 * q3)
 t1=(C_1_10 * delta)
 t2=(C_1_10 * eps)
 t3=(1 + (-q1))
 t4=(1 + (-q2))
 t5=(1 + (-q3))
 t6=(t4 * t5)
 t7=(1 + (-q0))
 t8=(t3 * t7)
 Q0=((C_1_1000 * q3) + (q1 * (C_1_100 + (C_m11_1000 * q3) + (q2 * (C_m441_100 + (C_4411_1000 * q3))))) + (q2 * (C_27_5 + (C_m5401_1000 * q3))))
 D0=(t0 + (q1 * (-1 + (-t0) + (q2 * (-4 + (C_501_100 * q3))))) + (q2 * (6 + (C_m701_100 * q3))))
 Q1=((C_1_100 * q0) + (q2 * (C_3_20 + (C_m4_25 * q0) + (q3 * (C_49_100 + (C_m37_25 * q0))))) + (q3 * (C_9_25 + (C_63_100 * q0))))
 D1=((-q0) + (q2 * (C_3_2 + (C_m3_2 * q0) + (q3 * (C_m9_10 + (C_m11_10 * q0))))) + (q3 * (C_2_5 + (C_8_5 * q0))))
 Q2=(t0 + (q0 * (t1 + (q1 * (C_23_50 + (-t1) + (q3 * (C_m29_20 + t1)))) + (q3 * (C_m1_100 + (-t1))))) + (q1 * (C_27_50 + (C_9_20 * q3))))
 D2=((-q3) + (q0 * (delta + (q1 * (C_2_5 + (-delta) + (q3 * (C_m12_5 + delta)))) + (-delta * q3))) + (q1 * (C_3_5 + (C_7_5 * q3))))
 Q3=((C_1_100 * q2) + (q0 * (C_63_1000 + (C_927_1000 * q2))) + (q1 * (t2 + (q0 * (C_m63_1000 + (-t2) + (q2 * (C_m927_1000 + t2)))) + (q2 * (C_m1_100 + (-t2))))))
 D3=((-q2) + (q0 * (C_7_100 + (C_193_100 * q2))) + (q1 * (eps + (q0 * (C_m107_100 + (-eps) + (q2 * (C_m93_100 + eps)))) + (-eps * q2))))
 H0=(t3 * t6)
 H1=(t6 * t7)
 H2=(t5 * t8)
 H3=(t4 * t8)
 Q=[Q0,Q1,Q2,Q3]; DD=[D0,D1,D2,D3]; H=[H0,H1,H2,H3]
 g=[v-h*x for v,h,x in zip(DD,H,b)]
 return [v-w for v,w in zip(Q,DD)],Q,H,g



def gaps(q,b,delta,eps):
 q0,q1,q2,q3=q
 t0=(1 + (-q1))
 t1=(1 + (-q2))
 t2=(1 + (-q3))
 t3=(t1 * t2)
 t4=(1 + (-q0))
 t5=(t0 * t4)
 D0=((-q1) + (q2 * (6 + (-4 * q1) + (q3 * (C_m701_100 + (C_501_100 * q1))))) + (q3 * (C_1_100 + (C_m1_100 * q1))))
 H0=(t0 * t3)
 D1=((-q0) + (q2 * (C_3_2 + (C_m3_2 * q0) + (q3 * (C_m9_10 + (C_m11_10 * q0))))) + (q3 * (C_2_5 + (C_8_5 * q0))))
 H1=(t3 * t4)
 D2=((-q3) + (q0 * (delta + (q1 * (C_2_5 + (-delta) + (q3 * (C_m12_5 + delta)))) + (-delta * q3))) + (q1 * (C_3_5 + (C_7_5 * q3))))
 H2=(t2 * t5)
 D3=((-q2) + (q0 * (C_7_100 + (C_193_100 * q2))) + (q1 * (eps + (q0 * (C_m107_100 + (-eps) + (q2 * (C_m93_100 + eps)))) + (-eps * q2))))
 H3=(t1 * t5)
 return [D0-H0*b[0],D1-H1*b[1],D2-H2*b[2],D3-H3*b[3]]


def qjac(q,b,d,e):
 # Explicit hazard derivative of gaps(). Diagonals vanish because g_i is
 # independent of q_i. The cap contribution is b_i prod_(k!=i,j)(1-q_k).
 q0,q1,q2,q3=q
 h0,h1,h2,h3=1-q0,1-q1,1-q2,1-q3
 s01=h2*h3;s02=h1*h3;s03=h1*h2
 s12=h0*h3;s13=h0*h2;s23=h0*h1
 z=0*q0
 a01=-1+q2*(-4+C_501_100*q3)+C_m1_100*q3+b[0]*s01
 a02=6-4*q1+q3*(C_m701_100+C_501_100*q1)+b[0]*s02
 a03=C_1_100+C_m1_100*q1+q2*(C_m701_100+C_501_100*q1)+b[0]*s03
 a10=-1+q2*(C_m3_2+C_m11_10*q3)+C_8_5*q3+b[1]*s01
 a12=C_3_2+C_m3_2*q0+q3*(C_m9_10+C_m11_10*q0)+b[1]*s12
 a13=C_2_5+C_8_5*q0+q2*(C_m9_10+C_m11_10*q0)+b[1]*s13
 t2=C_2_5-d+q3*(C_m12_5+d)
 a20=d+q1*t2-d*q3+b[2]*s02
 a21=C_3_5+C_7_5*q3+q0*t2+b[2]*s12
 a23=-1+q0*(-d+q1*(C_m12_5+d))+C_7_5*q1+b[2]*s23
 t3=C_m107_100-e+q2*(C_m93_100+e)
 a30=C_7_100+C_193_100*q2+q1*t3+b[3]*s03
 a31=e+q0*t3-e*q2+b[3]*s13
 a32=-1+C_193_100*q0+q1*(-e+q0*(C_m93_100+e))+b[3]*s23
 return [[z,a01,a02,a03],[a10,z,a12,a13],[a20,a21,z,a23],[a30,a31,a32,z]]

def proposal(S,b,d,e,seed,fixed):
 bb=[float(mid(x))for x in b];dd=float(mid(d));ee=float(mid(e));q=[float(mid(x))for x in fixed]
 for i in S:q[i]=float(seed[i])
 q,C=float_newton(S,q,bb,dd,ee)
 return[F(str(x))for x in q],[[F(str(x))for x in row]for row in C]

def rootbox(S,b,d,e,seed,fixed=None,must=None,graph=None):
 S=list(S);fixed=[Iv(0)]*4 if fixed is None else fixed
 qhat,C=proposal(S,b,d,e,seed,fixed)
 bm=[Iv(mid(x))for x in b];dm=Iv(mid(d));em=Iv(mid(e))
 for _ in range(4):
  qp0=[Iv(x)if i in S else Iv(mid(fixed[i]))for i,x in enumerate(qhat)]
  correction=mv(C,[mid(gaps(qp0,bm,dm,em)[i])for i in S])
  for i,x in zip(S,correction):
   z=qhat[i]-x;qhat[i]=F(z.numerator*10**60//z.denominator,10**60)
 qp=[Iv(x)if i in S else fixed[i]for i,x in enumerate(qhat)]
 resid=mv(C,[gaps(qp,b,d,e)[i]for i in S])
 if graph is not None:
  bg,dg,eg,bp,dp,ep,widths=graph
  # qhat is constant in the six ORIGINAL latent variables. Independent fixed
  # bridge hazards remain intervals at the point anchor AND in derivatives.
  gj=gaps([Jet(x)for x in qp],bg,dg,eg)
  rhoj=mv(C,[gj[i]for i in S])
  gp=gaps(qp,[x.v for x in bp],dp.v,ep.v)
  rhop=mv(C,[gp[i]for i in S])
  rg=[around(a,sum(mag(v)*w for v,w in zip(z.d,widths)))for a,z in zip(rhop,rhoj)]
  resid=[Iv(max(a.lo,z.lo),min(a.hi,z.hi),True)for a,z in zip(resid,rg)]
  assert all(z.lo<=z.hi for z in resid), 'empty graph residual intersection'
 rr=[2*mag(x)+F(1,10**55)for x in resid]
 if must:
  for k,i in enumerate(S):rr[k]=max(rr[k],mag(must[i]-qhat[i])*F(11,10))
 for attempt in range(20):
  qb=qp[:]
  for i,r in zip(S,rr):qb[i]=Iv.box(qhat[i],r)
  G=qjac(qb,b,d,e);A=[[G[i][j]for j in S]for i in S];M=[[Iv(int(i==j))-x for j,x in enumerate(row)]for i,row in enumerate(mm(C,A))]
  lip=max(sum(mag(x)*r for x,r in zip(row,rr))/rr[i]for i,row in enumerate(M))
  if lip<F(9,10) and all(mag(z)+sum(mag(a)*r for a,r in zip(row,rr))<r0 for z,row,r0 in zip(resid,M,rr)):
   qs=qb[:]
   for k,i in enumerate(S):qs[i]=Iv(qhat[i])-resid[k]+sum(a*Iv.box(0,r)for a,r in zip(M[k],rr))
   for i in S:
    qs[i]=Iv(max(qs[i].lo,qb[i].lo),min(qs[i].hi,qb[i].hi),True)
    assert qs[i].lo<=qs[i].hi,('empty Newton image intersection',i)
   Gs=qjac(qs,b,d,e);As=[[Gs[i][j]for j in S]for i in S]
   return(qb if must is not None else qs),Gs,inv_pre(As,C),float(lip)
  rr=[max(old,F(5,4)*(mag(z)+sum(mag(a)*r for a,r in zip(row,rr))))for old,z,row in zip(rr,resid,M)]
  if lip>F(9,10):break
 raise AssertionError(('stage Newton failed',S,float(lip),[float(x)for x in rr]))


def branch(S,b,d,e,seed,fixed=None,graph=None):
 context=None if graph is None else (b,d,e,*graph)
 qb,G,inverse,lip=rootbox(S,[x.v for x in b],d.v,e.v,seed,fixed,graph=context)
 bl=[Jet(x.v,[Iv(int(i==j))for j in range(6)])for i,x in enumerate(b)]
 dl=Jet(d.v,[Iv(0)]*4+[Iv(1),Iv(0)]);el=Jet(e.v,[Iv(0)]*5+[Iv(1)])
 direct=gaps([Jet(x)for x in qb],bl,dl,el)
 deriv=mm(inverse,[[-x for x in direct[i].d]for i in S]);qj=[Jet(x)for x in qb]
 for i,der in zip(S,deriv):qj[i]=Jet(qb[i],der)
 P,Q,H,g=evaluate(qj,bl,dl,el);out=[Q[i]if i in S else Q[i]-g[i]for i in I]
 inputs=[x.d for x in b]+[d.d,e.d];od=mm([x.d for x in out],inputs);gd=mm([x.d for x in g],inputs)
 return[Jet(x.v,z)for x,z in zip(out,od)],qb,[Jet(x.v,z)for x,z in zip(g,gd)],G,lip

def center(d,e,h,n,p,prefer_pair=True):
 word=[[0,1,3]]*h+[[0,1,2]]*n+[[0,2,3]]*p
 c=[.0041188900253,.0001243482175,.0000419077556,.3690086159]
 for it in range(10):
  rows=[]
  for S in word:
   S=S[:];q=float_triple(c,S,d,e);P,Q,H,g=evaluate(q,c,d,e)
   if S==[0,1,3]and prefer_pair:
    pair=[c[3]/(c[3]+.07),0.,0.,c[0]/(c[0]+.01)]
    pp,qq,hh,gg=evaluate(pair,c,d,e)
    if gg[1]<=0 and gg[2]<=0:S=[0,3];q=pair;P,Q,H,g=pp,qq,hh,gg
   if S==[0,1,2]and g[3]>0:
    q,_=float_newton([0,1,2,3],q,c,d,e);S=[0,1,2,3];P,Q,H,g=evaluate(q,c,d,e)
   b=[Q[i]if i in S else Q[i]-g[i]for i in I];rows.append((q,g,S,c,b));c=b
 return c,rows
def alternatives(b,bp,d,e,dp,ep,seed,S,optional,widths):
 graph=(bp,dp,ep,widths)
 oq,qq,gq,Gq,lq=branch(S,b,d,e,seed,graph=graph);op,qp,gp,_,_=branch(S,bp,dp,ep,seed)
 assert all(y.lo<=x.lo and x.hi<=y.hi for x,y in zip(qp,qq)), 'quiet graph anchor linkage'
 for i in I:
  rg=around(gp[i].v,sum(mag(z)*w for z,w in zip(gq[i].d,widths)))
  gq[i].v=Iv(max(gq[i].v.lo,rg.lo),min(gq[i].v.hi,rg.hi),True)
  assert gq[i].v.lo<=gq[i].v.hi
 if not optional or gq[3].v.hi<0:
  assert all(qq[i].lo>0 and qq[i].hi<D for i in S),('quiet physical',S,qq)
  assert all(gq[i].v.hi<0 for i in I if i not in S),('quiet gaps',S,[gq[i].v for i in I if i not in S])
  modes=[(oq,op,qq,qp,'q')]
 else:
  of,qf,gf,Gf,lf=branch([0,1,2,3],b,d,e,seed,graph=graph);ofp,qfp,_,_,_=branch([0,1,2,3],bp,dp,ep,seed)
  assert qf[3].hi<D,('full optional upper',qf)
  if gq[3].v.lo>0 and qf[3].lo>0:
   assert all(qf[i].lo>0 and qf[i].hi<D for i in S),('strict full physical',qf)
   modes=[(of,ofp,qf,qfp,'f')]
  else:
   assert all(min(qq[i].lo,qf[i].lo)>0 and max(qq[i].hi,qf[i].hi)<D for i in S),('seam persistent physical',qq,qf)
   y=hull(Iv(0),qf[3]);fixed=[Iv(0)]*3+[y]
   bridge,Gb,ib,lb=rootbox(S,[x.v for x in b],d.v,e.v,seed,fixed,[hull(x,y)for x,y in zip(qq,qf)],graph=(b,d,e,*graph))
   assert all(bridge[i].lo<=qf[i].lo and qf[i].hi<=bridge[i].hi for i in S)
   schur=Gb[3][3]-sum(Gb[3][i]*x for i,x in zip(S,mv(ib,[Gb[i][3]for i in S])))
   assert schur.hi<0,('bad Schur',schur)
   modes=[(oq,op,qq,qp,'q'),(of,ofp,qf,qfp,'f')]
 for _,_,q,qp,_ in modes:assert all(y.lo<=x.lo and x.hi<=y.hi for x,y in zip(qp,q))
 return modes

def union(boxes):
 return[Iv(min(row[i].lo for row in boxes),max(row[i].hi for row in boxes),True)for i in I]

def common_link(parents,children,d,e,seed,S,optional,dp,ep,widths):
 """Uniqueness on convex hulls, using existence already certified historywise.
 Every incoming history's QUIET chart is included, even if full is selected.
 At mixed selected modes, full uniqueness includes quiet tubes to identify seams.
 """
 if len(parents)==1 and len(children)==1:return(0,0)
 bb=union([[x.v for x in b]for b,bp,word in parents])
 quiet=[]
 for b,bp,word in parents:
  choices=[rec[2]for rec in children if rec[5]==word and rec[4]=='q']
  quiet.append(choices[0]if choices else branch(S,b,d,e,seed,graph=(bp,dp,ep,widths))[1])
 groups={tuple(S):quiet}
 full=[rec[2]for rec in children if rec[4]=='f']
 if full:
  mixed=any(rec[4]=='q'for rec in children)
  groups[(0,1,2,3)]=full+quiet if mixed else full
 maxlip=0
 for support,boxes in groups.items():
  qh=union(boxes);G=qjac(qh,bb,d.v,e.v)
  A=[[G[i][j]for j in support]for i in support]
  C=[[F(str(x))for x in row]for row in float_inverse([[float(mid(x))for x in row]for row in A])]
  E=[[Iv(int(i==j))-z for j,z in enumerate(row)]for i,row in enumerate(mm(C,A))]
  lip=max(sum(mag(z)for z in row)for row in E)
  assert lip<F(1),('common uniqueness',support,float(lip))
  maxlip=max(maxlip,float(lip))
 return(len(groups),maxlip)

def audit_horner():
 # All expressions are visibly multiaffine in q,b,delta,epsilon. The full
 # hazard/parameter vertex grid and b=0 plus four coordinate directions
 # therefore prove equality of the two exact polynomial evaluators.
 from itertools import product
 for q in product((F(0),F(1)),repeat=4):
  for d,e in product((F(0),F(1)),repeat=2):
   for k in range(5):
    b=[F(int(i==k))for i in I]
    old=raw_evaluate(q,b,d,e);new=evaluate(q,b,d,e)
    assert old==new
    assert old[3]==gaps(q,b,d,e)
    jac=qjac(q,b,d,e)
    for j in I:
     qlo=list(q);qhi=list(q);qlo[j]=F(0);qhi[j]=F(1)
     glo=raw_evaluate(qlo,b,d,e)[3];ghi=raw_evaluate(qhi,b,d,e)[3]
     assert [jac[i][j]for i in I]==[y-x for x,y in zip(glo,ghi)]
 print('PASS exact raw-table/Horner and hazard-Jacobian polynomial identities',flush=True)


H0=2;N0=8;P0=24
WORD=[[0,1,3]]*2+[[0,1,2]]*8+[[0,2,3]]*P0
BASE=[F(1,10**5),F(1,10**4),F(1,10**6),F(1,10**5)]

_CANDIDATE_KEY=None
_CANDIDATE_VALUE=None
def candidate(dc,ec):
 global _CANDIDATE_KEY,_CANDIDATE_VALUE
 key=(H0,N0,P0,dc,ec)
 if key==_CANDIDATE_KEY:return _CANDIDATE_VALUE
 c,rows=center(float(dc),float(ec),H0,N0,P0,False);v=[]
 assert all(row[2]==S or(S==[0,1,2]and row[2]==[0,1,2,3])for row,S in zip(rows,WORD))
 for k in range(2):
  us=[]
  for sg in(-1,1):
   dd=float(dc)+sg*1e-7*(k==0);ee=float(ec)+sg*1e-7*(k==1)
   us.append(center(dd,ee,H0,N0,P0,False)[0])
  v.append([F(str((y-x)/2e-7))for x,y in zip(*us)])
 _CANDIDATE_KEY=key
 _CANDIDATE_VALUE=([F(str(x))for x in c],list(zip(*v)),[row[0]for row in rows])
 return _CANDIDATE_VALUE

def verify(dl,du,el,eu,r=BASE,verbose=True):
 dc=(dl+du)/2;ec=(el+eu)/2;hd=(du-dl)/2;he=(eu-el)/2;c,v,seeds=candidate(dc,ec);widths=r+[hd,he]
 b=[Jet(Iv.box(c[i],r[i]+abs(v[i][0])*hd+abs(v[i][1])*he),[Iv(int(i==j))for j in I]+[Iv(x)for x in v[i]])for i in I]
 bp=[Jet(x)for x in c];d=Jet(Iv.box(dc,hd),[Iv(0)]*4+[Iv(1),Iv(0)]);e=Jet(Iv.box(ec,he),[Iv(0)]*5+[Iv(1)])
 dp=Jet(dc);ep=Jet(ec);paths=[(b,bp,'')];selected={''};minq=D;links=0;maxlinklip=0
 for phase,S in enumerate(WORD):
  optional=S==[0,1,2];records=[];next_selected=set()
  for b,bp,history in paths:
   try:modes=alternatives(b,bp,d,e,dp,ep,seeds[phase],S,optional,widths)
   except Exception as ex:raise AssertionError(('branch failure',phase,history,str(ex)))from ex
   if history in selected:
    possible={z[4]for z in modes}
    if len(possible)>1:
     _,_,gp,_,_=branch(S,bp,dp,ep,seeds[phase])
     if gp[3].v.hi<0:possible={'q'}
     elif gp[3].v.lo>0:possible={'f'}
    next_selected.update(history+mode for mode in possible)
   for out,op,q,qp,mode in modes:records.append((out,op,q,qp,mode,history,I if mode=='f'else S))
  nl,ll=common_link(paths,records,d,e,seeds[phase],S,optional,dp,ep,widths);links+=nl;maxlinklip=max(maxlinklip,ll)
  new=[]
  for out,op,q,qp,mode,history,support in records:
   # Three persistent owners remain physical, including on signed full extensions.
   assert min(q[i].lo for i in S)*10**7>D
   minq=min(minq,*(q[i].lo for i in S))
   for i in I:
    rad=sum(mag(out[i].d[j])*r[j]for j in I)+mag(out[i].d[4])*hd+mag(out[i].d[5])*he
    rg=around(op[i].v,rad);out[i].v=Iv(max(out[i].v.lo,rg.lo),min(out[i].v.hi,rg.hi),True)
    assert out[i].v.lo<=out[i].v.hi
   new.append((out,op,history+mode))
  paths=new;selected=next_selected;assert selected;assert len(paths)<=16
  if verbose and(phase in(2,3,4,9,17,33)or len(records)>1 and phase<12):print('PHASE',phase,'histories',len(paths),'links',links,'link lip',maxlinklip,flush=True)
 # Only the actual selected centre return anchors the final glued return.
 # Unselected histories retain their own anchors in every preceding stage.
 cap=[];param=[]
 for b,bp,history in paths:
  cap.append([sum(mag(x)*r[j]for j,x in enumerate(row.d[:4]))for row in b])
  param.append([mag(b[i].d[4]-v[i][0])*hd+mag(b[i].d[5]-v[i][1])*he for i in I])
 central=[max(mag(bp[i].v-c[i])for b,bp,h in paths if h in selected)for i in I]
 L=[max(z[i]for z in cap)/r[i]for i in I]
 B=[max(a[i]+z[i]for a,z in zip(cap,param))for i in I]
 R=[central[i]+max(z[i]for z in param)for i in I]
 assert max(L)<1,('return contraction',list(map(float,L)),[float((central[i]+B[i])/r[i])for i in I])
 assert all(central[i]+B[i]<r[i]for i in I),('selected return failure',list(map(float,L)),[float(x/rr)for x,rr in zip(R,r)], [float((central[i]+B[i])/r[i])for i in I])
 stats=[(max(L),max(x/rr for x,rr in zip(R,r)))]
 print('PASS',dl,du,el,eu,'histories',len(paths),'possible centre histories',len(selected),'stats',[(float(a),float(b))for a,b in stats],'persistent q>',float(F(minq,D)),'links',links,'maxlinklip',maxlinklip,flush=True)
 return stats,F(minq,D),len(paths),links,maxlinklip

def setword(h,n,p):
 global H0,N0,P0,WORD
 H0=h;N0=n;P0=p;WORD=[[0,1,3]]*h+[[0,1,2]]*n+[[0,2,3]]*p

def float_return(c,d,e):
 c=list(c)
 for S in WORD:
  q=float_triple(c,S,d,e);P,Q,H,g=evaluate(q,c,d,e)
  if S==[0,1,2]and g[3]>0:
   q,_=float_newton([0,1,2,3],q,c,d,e);S=[0,1,2,3];P,Q,H,g=evaluate(q,c,d,e)
  c=[Q[i]if i in S else Q[i]-g[i]for i in I]
 return c

def proposed_radii(dl,du,el,eu):
 # Only proposes positive rational radii. All acceptance remains in verify().
 dc=(dl+du)/2;ec=(el+eu)/2;c,v,seeds=candidate(dc,ec)
 cf=list(map(float,c));vf=[list(map(float,row))for row in v]
 columns=[]
 for j in I:
  step=max(abs(cf[j])*1e-5,1e-9);lo=cf[:];hi=cf[:]
  lo[j]-=step;hi[j]+=step
  fl=float_return(lo,float(dc),float(ec));fh=float_return(hi,float(dc),float(ec))
  columns.append([(y-x)/(2*step)for x,y in zip(fl,fh)])
 derivative=list(map(list,zip(*columns)))
 error=[1e-12]*4
 for dd in(dl,du):
  for ee in(el,eu):
   affine=[cf[i]+vf[i][0]*float(dd-dc)+vf[i][1]*float(ee-ec)for i in I]
   returned=float_return(affine,float(dd),float(ee))
   error=[max(a,abs(x-y))for a,x,y in zip(error,affine,returned)]
 inverse=float_inverse([[float(i==j)-abs(derivative[i][j])for j in I]for i in I])
 radius=mv(inverse,error)
 assert all(x>0 for x in radius),('radius proposal',radius)
 return [F(str(max(2*x,1e-11)))for x in radius]

def numerical_score(h,n,p,dc,ec):
 setword(h,n,p)
 c,rows=center(float(dc),float(ec),h,n,p,False)
 assert max(abs(x-y)for x,y in zip(rows[0][3],c))<1e-10
 margins=[];condition=0
 for q,g,S,b,out in rows:
  margins.extend(min(q[i],1-q[i])for i in S)
  margins.extend(-g[i]for i in I if i not in S)
  jac=qjac(q,b,float(dc),float(ec))
  inv=float_inverse([[jac[i][j]for j in S]for i in S])
  condition=max(condition,max(sum(abs(x)for x in row)for row in inv))
 assert min(margins)>0,('numerical physical',min(margins))
 return min(margins)/max(condition,1)

def exact_attempt(cell,word):
 import contextlib,io
 setword(*word)
 radius=proposed_radii(*cell)
 for k in range(4):
  try:
   with contextlib.redirect_stdout(io.StringIO()):
    result=verify(*cell,radius,False)
   return result,radius,k+1
  except AssertionError as ex:
   info=ex.args[0]if ex.args else None
   if isinstance(info,tuple)and info[0]in('selected return failure','return contraction'):
    ratios=info[-1]
    radius=[max(r,F(str(1.3*x))*r)for r,x in zip(radius,ratios)]
   else:raise
 raise AssertionError(('radius retries',word,list(map(float,radius)),info))

# Finite initial delta partition, in descending order. The extra h choices
# alter only the proposal calendar; every selected phase is checked exactly.
BANDS=[(F(a),F(b),n,p)for a,b,n,p in[
 ('.08','.12',8,24),('.058','.08',9,24),('.04','.058',12,24),('.032','.04',13,24),
 ('.024','.032',16,24),('.016','.024',19,16),('.0105','.016',21,16),
 ('.008','.0105',27,12),('.006','.008',30,12),('.0048','.006',34,8),
 ('.004','.0048',39,8),('.0032','.004',42,8),('.002','.0032',48,8)]]
COUNT=FAILS=ATTEMPTS=MAX_PERIOD=0
START=0
MIN_PERSISTENT=F(1)
MAX_CONTRACTION=F(0)
MAX_RETURN_RATIO=F(0)
MAX_HISTORIES=1
LAST_REPORT=0

def ranked_calendars(dc,ec,n,p,extended=False):
 # Candidate-only neighbors at every scale, without a Cartesian n/p expansion.
 families=[(n,p)]if ec<F(3,5)else[(n-2,p),(n-1,p),(n,p),(n+1,p),(n+2,p),(n,p-4),(n,p+4)]
 ranked=[]
 for h in(1,2,3,4):
  for nn,pp in families:
   if nn<1 or pp<0:continue
   word=(h,nn,pp)
   try:ranked.append((numerical_score(*word,dc,ec),word))
   except(AssertionError,ValueError,ZeroDivisionError,OverflowError):pass
 return[word for score,word in sorted(ranked,reverse=True)]

def cover(dl,du,el,eu,n,p,depth=0):
 global COUNT,FAILS,ATTEMPTS,MAX_PERIOD,MIN_PERSISTENT,MAX_CONTRACTION,MAX_RETURN_RATIO,MAX_HISTORIES,LAST_REPORT
 assert time.monotonic()-START<7200 and ATTEMPTS<20000,('budget',COUNT,FAILS,ATTEMPTS)
 dc=(dl+du)/2;ec=(el+eu)/2
 extended=(du-dl)<dc/20 and(eu-el)<F(1,250)
 words=ranked_calendars(dc,ec,n,p,extended)
 result=None;reason='no numerically viable calendar'
 for word in words[:4]:
  ATTEMPTS+=1
  try:
   result,radius,tries=exact_attempt((dl,du,el,eu),word)
   break
  except(AssertionError,ValueError,ZeroDivisionError,OverflowError)as ex:reason=str(ex)
 if result is not None:
  COUNT+=1;MAX_PERIOD=max(MAX_PERIOD,len(WORD));MIN_PERSISTENT=min(MIN_PERSISTENT,result[1])
  MAX_CONTRACTION=max(MAX_CONTRACTION,result[0][0][0]);MAX_RETURN_RATIO=max(MAX_RETURN_RATIO,result[0][0][1]);MAX_HISTORIES=max(MAX_HISTORIES,result[2])
  if time.monotonic()-LAST_REPORT>=30:
   print('PROGRESS',COUNT,FAILS,ATTEMPTS,'max_period',MAX_PERIOD,'max_histories',MAX_HISTORIES,'seconds',int(time.monotonic()-START),flush=True);LAST_REPORT=time.monotonic()
  return
 FAILS+=1
 assert depth<24,('subdivision limit',dl,du,el,eu,n,p,reason)
 # Rescale delta by its positive center when choosing only the split axis.
 # Both closed children are always verified, so this does not alter coverage.
 if(du-dl)>=2*dc*(eu-el):
  dm=(dl+du)/2;cover(dl,dm,el,eu,n,p,depth+1);cover(dm,du,el,eu,n,p,depth+1)
 else:
  em=(el+eu)/2;cover(dl,du,el,em,n,p,depth+1);cover(dl,du,em,eu,n,p,depth+1)

def band(k):
 dl,du,n,p=BANDS[k]
 top=F(737,1000)+F(3,50)*du+F(1,10000)
 edges=[F(j,50)for j in range(37)]+[top]
 assert edges[-2]<top
 print('BEGIN_BAND',k,str(dl),str(du),'epsilon_top',str(top),flush=True)
 for j,(el,eu)in enumerate(zip(edges,edges[1:])):
  cover(dl,du,el,eu,n,p)
  print('PASS_CLOSED_EPSILON_SLICE',k,j,str(dl),str(du),str(el),str(eu),'cumulative',COUNT,FAILS,ATTEMPTS,'seconds',time.monotonic()-START,flush=True)
 print('PASS_CLOSED_BAND',k,str(dl),str(du),'epsilon_top',str(top),'cumulative',COUNT,FAILS,ATTEMPTS,'seconds',time.monotonic()-START,flush=True)

# Candidate-only floating clones. None of these helpers accepts a certificate.
from types import FunctionType
_FLOAT_GLOBALS=dict(globals())
for _name,_value in list(_FLOAT_GLOBALS.items()):
 if _name.startswith('C_'):_FLOAT_GLOBALS[_name]=float(_value)
_FLOAT_A=[[float(x)for x in row]for row in A]
_FLOAT_DD={}
for _S in ((0,1,3),(0,1,2),(0,2,3)):
 for _a in _S:
  _u,_v=[x for x in _S if x!=_a];_mask=(1<<_u)|(1<<_v)
  _FLOAT_DD[_a,_u,_v]=float(Z[_a,_mask|(1<<_a)]-Z[_a,_mask])

def _float_triple_fast(b,S,d,e):
 i,j,k=S
 def cf(a,u,v):
  au=-d if(a,u)==(2,0)else(-e if(a,u)==(3,1)else _FLOAT_A[a][u])
  av=-d if(a,v)==(2,0)else(-e if(a,v)==(3,1)else _FLOAT_A[a][v])
  dd=_FLOAT_DD[a,min(u,v),max(u,v)]
  return-b[a],b[a]-au,b[a]-av,dd+au+av-b[a]
 ci,ai,bi,di=cf(i,j,k);cj,aj,bj,dj=cf(j,i,k);ck,ak,bk,dk=cf(k,i,j)
 nx=[-cj,-bj];dx=[aj,dj];ny=[-ci,-bi];dy=[ai,di]
 def mul2(a,b):return[a[0]*b[0],a[0]*b[1]+a[1]*b[0],a[1]*b[1]]
 terms=[mul2(dx,dy),mul2(nx,dy),mul2(ny,dx),mul2(nx,ny)]
 cc=[sum(t[l]*x for t,x in zip(terms,[ck,ak,bk,dk]))for l in range(3)]
 from math import sqrt
 zz=(-cc[1]+sqrt(cc[1]*cc[1]-4*cc[2]*cc[0]))/(2*cc[2]);q=[0.]*4
 q[i]=(nx[0]+nx[1]*zz)/(dx[0]+dx[1]*zz);q[j]=(ny[0]+ny[1]*zz)/(dy[0]+dy[1]*zz);q[k]=zz
 return q

for _name in ('evaluate','gaps','qjac','float_gap_jac','float_newton','center'):
 _original=_FLOAT_GLOBALS[_name]
 _FLOAT_GLOBALS[_name]=FunctionType(_original.__code__,_FLOAT_GLOBALS,_name,_original.__defaults__)
_FLOAT_GLOBALS['float_triple']=_float_triple_fast
center=_FLOAT_GLOBALS['center']
float_gap_jac=_FLOAT_GLOBALS['float_gap_jac']
float_newton=_FLOAT_GLOBALS['float_newton']

# Original frozen proposal order, selected only by --baseline-proposals.
def _baseline_ranked_calendars(dc,ec,n,p,extended=False):
 words=[(h,n,p)for h in(1,2,3,4)]
 if extended:
  words.extend((h,nn,pp)for h in(1,2,3,4)for nn,pp in[(n-1,p),(n+1,p),(n,p+4)])
 ranked=[]
 for word in words:
  try:ranked.append((numerical_score(*word,dc,ec),word))
  except(AssertionError,ValueError,ZeroDivisionError,OverflowError):pass
 return[word for score,word in sorted(ranked,reverse=True)]

if __name__=='__main__':
 import argparse,hashlib
 parser=argparse.ArgumentParser();group=parser.add_mutually_exclusive_group()
 group.add_argument('--band',type=int,default=None);group.add_argument('--start-band',type=int,default=0)
 parser.add_argument('--end-band',type=int,default=None)
 parser.add_argument('--baseline-proposals',action='store_true',help='use the original frozen calendar ranking (for baseline band 0)')
 args=parser.parse_args()
 if args.baseline_proposals:ranked_calendars=_baseline_ranked_calendars
 START=LAST_REPORT=time.monotonic()
 print('SOURCE_SHA256',hashlib.sha256(open(__file__,'rb').read()).hexdigest(),flush=True)
 print('PROPOSAL_MODE','baseline'if args.baseline_proposals else 'v4',flush=True)
 audit_horner()
 assert BANDS[0][1]==F(3,25)and BANDS[-1][0]==F(1,500)
 assert all(a[0]==b[1]for a,b in zip(BANDS,BANDS[1:]))
 if args.band is not None:
  assert args.end_band is None
  assert 0<=args.band<len(BANDS);band(args.band)
  print('PASS SINGLE LOW BAND ONLY',args.band,flush=True)
 else:
  end_band=12 if args.end_band is None else args.end_band
  assert 0<=args.start_band<=end_band<len(BANDS)
  for k in range(args.start_band,end_band+1):band(k)
  marker='PASS COMPLETE LOW REGION'if(args.start_band,end_band)==(0,12)else 'PASS LOW BANDS '+str(args.start_band)+'..'+str(end_band)
  scope='delta['+str(BANDS[end_band][0])+','+str(BANDS[args.start_band][1])+'], epsilon[0,.737+.06delta+.0001]'
  print(marker,scope,COUNT,FAILS,ATTEMPTS,'maximum period',MAX_PERIOD,'minimum persistent hazard',float(MIN_PERSISTENT),'max contraction',float(MAX_CONTRACTION),'max return ratio',float(MAX_RETURN_RATIO),'max histories',MAX_HISTORIES,'seconds',time.monotonic()-START,flush=True)

