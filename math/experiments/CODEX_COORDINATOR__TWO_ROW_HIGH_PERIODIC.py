"""Exact graph certificates for the high two-row region; period at most18.
Target delta[6/5,3/2], epsilon[0,737/1000+3 delta/50+1/10000].
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
 g=gaps(q,b,d,e);A=[]
 for j in I:
  q0=q[:];q1=q[:];q0[j]=0.;q1[j]=1.
  v0=gaps(q0,b,d,e);v1=gaps(q1,b,d,e)
  A.append([y-x for x,y in zip(v0,v1)])
 return g,list(map(list,zip(*A)))

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

def center(d,e,n,p,prefer_pair=True):
 word=[[0,1,3]]*2+[[0,1,2]]*n+[[0,2,3]]*p
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
  assert all(qq[i].lo>0 and qq[i].hi<D for i in S)
  assert all(gq[i].v.hi<0 for i in I if i not in S)
  modes=[(oq,op,qq,qp,'q')]
 else:
  of,qf,gf,Gf,lf=branch([0,1,2,3],b,d,e,seed,graph=graph);ofp,qfp,_,_,_=branch([0,1,2,3],bp,dp,ep,seed)
  if gq[3].v.lo>0 and qf[3].lo>0:
   # Strict full selection needs physicality only for its selected full root.
   # The auxiliary quiet root retains its anchor and uniqueness obligations.
   assert all(qf[i].lo>0 and qf[i].hi<D for i in I)
   modes=[(of,ofp,qf,qfp,'f')]
  else:
   assert all(min(qq[i].lo,qf[i].lo)>0 and max(qq[i].hi,qf[i].hi)<D for i in S)
   assert qf[3].hi<D
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


N0=1;P0=8
WORD=[[0,1,3]]*2+[[0,1,2]]*N0+[[0,2,3]]*P0
BASE=[F(1,10**5),F(1,10**4),F(1,10**5),F(1,10**5)]
CALENDARS=[(n,p)for n in(1,2)for p in range(8,15)if 2+n+p<=18]


def setword(n,p):
 global N0,P0,WORD
 N0=n;P0=p;WORD=[[0,1,3]]*2+[[0,1,2]]*n+[[0,2,3]]*p


def ranked_calendars(dc,ec):
 candidates=[]
 for n,p in CALENDARS:
  try:
   c,rows=center(float(dc),float(ec),n,p,False)
   margins=[]
   for q,g,S,b,out in rows:
    margins.extend(min(q[i],1-q[i])for i in S)
    margins.extend(-g[i]for i in I if i not in S)
   residual=max(abs(x-y)for x,y in zip(rows[0][3],c))
   if min(margins)>0 and residual<1e-10:
    candidates.append((min(margins),n,p))
  except(AssertionError,ValueError,ZeroDivisionError,OverflowError):pass
 return[(n,p)for margin,n,p in sorted(candidates,reverse=True)[:3]]


def candidate(dc,ec):
 c,rows=center(float(dc),float(ec),N0,P0,False);v=[]
 assert all(row[2]==S or(S==[0,1,2]and row[2]==[0,1,2,3])for row,S in zip(rows,WORD))
 for k in range(2):
  us=[]
  for sg in(-1,1):
   dd=float(dc)+sg*1e-7*(k==0);ee=float(ec)+sg*1e-7*(k==1)
   us.append(center(dd,ee,N0,P0,False)[0])
  v.append([F(str((y-x)/2e-7))for x,y in zip(*us)])
 return[F(str(x))for x in c],list(zip(*v)),[row[0]for row in rows]

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
 assert max(L)<1
 assert all(central[i]+B[i]<r[i]for i in I),('selected return failure',list(map(float,L)),[float(x/rr)for x,rr in zip(R,r)], [float((central[i]+B[i])/r[i])for i in I])
 stats=[(max(L),max(x/rr for x,rr in zip(R,r)))]
 print('PASS',dl,du,el,eu,'histories',len(paths),'possible centre histories',len(selected),'stats',[(float(a),float(b))for a,b in stats],'persistent q>',float(F(minq,D)),'links',links,'maxlinklip',maxlinklip,flush=True)
 return stats,F(minq,D),len(paths),links,maxlinklip

COUNT=FAILS=ATTEMPTS=0
MAX_PERIOD=0
START=time.monotonic()

def cover(dl,du,el,eu,depth=0):
 global COUNT,FAILS,ATTEMPTS,MAX_PERIOD
 scale=max((du-dl)/F(1,500),(eu-el)/F(1,100))
 result=None;reason='no numerically viable calendar'
 for n,p in ranked_calendars((dl+du)/2,(el+eu)/2):
  setword(n,p)
  for k in(1,4,16,64):
   ATTEMPTS+=1
   assert ATTEMPTS<=30000 and time.monotonic()-START<5400,('budget',ATTEMPTS,COUNT,dl,du,el,eu)
   try:
    import contextlib,io
    with contextlib.redirect_stdout(io.StringIO()):result=verify(dl,du,el,eu,[k*scale*x for x in BASE],False)
    break
   except(AssertionError,ValueError,ZeroDivisionError,OverflowError)as ex:
    reason=str(ex)
    if not ('return failure' in reason):break
  if result is not None:break
 if result is not None:
  COUNT+=1;MAX_PERIOD=max(MAX_PERIOD,len(WORD))
  print('ACCEPT',COUNT,'fails',FAILS,'cell',*[float(x)for x in(dl,du,el,eu)],'calendar',N0,P0,'histories',result[2],'maxL',float(max(z[0]for z in result[0])),'maxR',float(max(z[1]for z in result[0])),'seconds',int(time.monotonic()-START),flush=True)
  return
 FAILS+=1
 if depth>=24:raise AssertionError(('subdivision limit',dl,du,el,eu,reason))
 if du-dl>=2*(eu-el):
  dm=(dl+du)/2;cover(dl,dm,el,eu,depth+1);cover(dm,du,el,eu,depth+1)
 else:
  em=(el+eu)/2;cover(dl,du,el,em,depth+1);cover(dl,du,em,eu,depth+1)

def tile(k):
 dl=F(120+k,100);du=F(121+k,100)
 # The slab's right-edge ceiling dominates the sloped target on the whole tile.
 top=F(737,1000)+F(3,50)*du+F(1,10000)
 edges=[F(j,50)for j in range(15)]
 edges.extend(F(j,100)for j in range(29,84)if F(j,100)<top)
 edges.append(top)
 for el,eu in zip(edges,edges[1:]):cover(dl,du,el,eu)
 print('TILE',k,'complete',COUNT,FAILS,ATTEMPTS,'seconds',time.monotonic()-START,flush=True)

if __name__=='__main__':
 START=time.monotonic();audit_horner()
 for k in range(30):tile(k)
 print('PASS COMPLETE HIGH REGION delta[1.2,1.5], epsilon[0,.737+.06delta+.0001]',COUNT,FAILS,ATTEMPTS,'maximum period',MAX_PERIOD,'seconds',time.monotonic()-START,flush=True)
