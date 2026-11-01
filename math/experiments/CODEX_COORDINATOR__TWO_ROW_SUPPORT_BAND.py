"""Exact support-seam certificate; standard library only. Floats propose; integer intervals certify."""
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


I=range(4);N=6;SEAM_INFO=[];VERBOSE=False

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
 g=evaluate(q,b,d,e)[3];A=[]
 for j in I:
  q0=q[:];q1=q[:];q0[j]=0.;q1[j]=1.
  v0=evaluate(q0,b,d,e)[3];v1=evaluate(q1,b,d,e)[3]
  A.append([y-x for x,y in zip(v0,v1)])
 return g,list(map(list,zip(*A)))

def float_newton(S,q,b,d,e):
 q=q[:]
 for _ in range(12):
  g,A=float_gap_jac(q,b,d,e);C=float_inverse([[A[i][j]for j in S]for i in S])
  err=mv(C,[g[i]for i in S])
  for i,x in zip(S,err):q[i]-=x
  if max(abs(x)for x in err)<1e-14:break
 assert max(abs(evaluate(q,b,d,e)[3][i])for i in S)<1e-10
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

def float_center(d,e,c=None):
 c=[.0041188900253007926,.0001243482175163462,.000041907755608047286,.36900861598844355]if c is None else c[:]
 for _ in range(8):
  seeds=[]
  for t in range(64):
   S=[0,1,3]if t<4 else[0,1,2];q=float_triple(c,S,d,e);P,Q,H,g=evaluate(q,c,d,e)
   if t==4 and g[3]>0:
    q,_=float_newton([0,1,2,3],q,c,d,e);S=[0,1,2,3];P,Q,H,g=evaluate(q,c,d,e)
   c=[Q[i]if i in S else P[i]+H[i]*c[i]for i in I];seeds.append(q)
 return c,seeds

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

def evaluate(q,b,delta,eps):
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

def qjac(q,b,d,e):
 qj=[Jet(x,[Iv(int(i==j))for j in range(N)])for i,x in enumerate(q)]
 g=evaluate(qj,[Jet(x)for x in b],Jet(d),Jet(e))[3]
 return[[x.d[j]for j in I]for x in g]

def proposal(S,b,d,e,seed,fixed):
 bb=[float(mid(x))for x in b];dd=float(mid(d));ee=float(mid(e));q=[float(mid(x))for x in fixed]
 for i in S:q[i]=float(seed[i])
 q,C=float_newton(S,q,bb,dd,ee)
 return[F(str(x))for x in q],[[F(str(x))for x in row]for row in C]

def rootbox(S,b,d,e,seed,fixed=None,must=None):
 S=list(S);fixed=[Iv(0)]*4 if fixed is None else fixed
 qhat,C=proposal(S,b,d,e,seed,fixed)
 bm=[Iv(mid(x))for x in b];dm=Iv(mid(d));em=Iv(mid(e))
 for _ in range(4):
  qp0=[Iv(x)if i in S else Iv(mid(fixed[i]))for i,x in enumerate(qhat)]
  correction=mv(C,[mid(evaluate(qp0,bm,dm,em)[3][i])for i in S])
  for i,x in zip(S,correction):
   z=qhat[i]-x;qhat[i]=F(z.numerator*10**60//z.denominator,10**60)
 qp=[Iv(x)if i in S else fixed[i]for i,x in enumerate(qhat)]
 resid=mv(C,[evaluate(qp,b,d,e)[3][i]for i in S]);rr=[2*mag(x)+F(1,10**55)for x in resid]
 if must:
  for k,i in enumerate(S):rr[k]=max(rr[k],mag(must[i]-qhat[i])*F(11,10))
 for attempt in range(8):
  qb=qp[:]
  for i,r in zip(S,rr):qb[i]=Iv.box(qhat[i],r)
  G=qjac(qb,b,d,e);A=[[G[i][j]for j in S]for i in S];M=[[Iv(int(i==j))-x for j,x in enumerate(row)]for i,row in enumerate(mm(C,A))]
  lip=max(sum(mag(x)for x in row)for row in M)
  if lip<F(9,10) and all(mag(z)+sum(mag(a)*r for a,r in zip(row,rr))<r0 for z,row,r0 in zip(resid,M,rr)):
   return qb,G,inv_pre(A,C),float(lip)
  rr=[2*x for x in rr]
 raise AssertionError(('stage Newton failed',S,float(lip),[float(x)for x in rr]))

def branch(S,b,d,e,seed,fixed=None):
 vals=[x.v for x in b];qb,G,inv,lip=rootbox(S,vals,d.v,e.v,seed,fixed)
 direct=evaluate([Jet(x)for x in qb],b,d,e)[3]
 deriv=mm(inv,[[ -x for x in direct[i].d]for i in S]);qj=[Jet(x)for x in qb]
 for i,der in zip(S,deriv):qj[i]=Jet(qb[i],der)
 P,Q,H,g=evaluate(qj,b,d,e);out=[Q[i]if i in S else P[i]+H[i]*b[i]for i in I]
 return out,qb,g,G,lip

def stage(b,d,e,seed,S,seam=False,point=False):
 quiet=branch(S,b,d,e,seed);oq,qq,gq,Gq,lq=quiet
 if not seam:
  assert all(qq[i].lo>0 and qq[i].hi<D for i in S),('bad hazard',S,qq)
  assert all(gq[i].v.hi<0 for i in I if i not in S)
  return oq,min(float(qq[i].lower())for i in(0,1)),lq,[qq]
 if gq[3].v.hi<0:
  assert all(qq[i].lo>0 and qq[i].hi<D for i in S)
  if not point:SEAM_INFO.append((gq[3].v,'quiet','strict'))
  return oq,min(qq[i].lower()for i in(0,1)),lq,[qq]
 full=branch([0,1,2,3],b,d,e,seed);of,qf,gf,Gf,lf=full
 if gq[3].v.lo>0 and qf[3].lo>0:
  assert all(qf[i].lo>0 and qf[i].hi<D for i in I)
  if not point:SEAM_INFO.append((gq[3].v,qf[3],'full'))
  return of,min(qf[i].lower()for i in(0,1)),max(lq,lf),[qq,qf]
 assert all(min(qq[i].lo,qf[i].lo)>0 and max(qq[i].hi,qf[i].hi)<D for i in S)
 assert qf[3].hi<D
 y=hull(Iv(0),qf[3]);fixed=[Iv(0)]*3+[y]
 bridge,Gb,ib,lb=rootbox(S,[x.v for x in b],d.v,e.v,seed,fixed,[hull(x,y)for x,y in zip(qq,qf)])
 assert all(bridge[i].lo<=qf[i].lo and qf[i].hi<=bridge[i].hi for i in S)
 schur=Gb[3][3]-sum(Gb[3][i]*x for i,x in zip(S,mv(ib,[Gb[i][3]for i in S])))
 assert schur.hi<0,('bad Schur',schur)
 if not point:SEAM_INFO.append((gq[3].v,qf[3],schur))
 if point:
  if gq[3].v.hi<0:out=oq
  elif gq[3].v.lo>0:
   assert qf[3].lo>0;out=of
  else:raise AssertionError('point on seam')
 else:out=[Jet(hull(x.v,y.v),[hull(a,c)for a,c in zip(x.d,y.d)])for x,y in zip(oq,of)]
 return out,min(min(qq[i].lower(),qf[i].lower())for i in(0,1)),max(lq,lf,lb),[qq,qf]

def candidate(dc,ec):
 c,seeds=float_center(float(dc),float(ec));v=[]
 for k in range(2):
  us=[]
  for sign in[-1,1]:
   dd=float(dc)+(sign*1e-8 if k==0 else 0);ee=float(ec)+(sign*1e-8 if k==1 else 0)
   us.append(float_center(dd,ee,c)[0])
  v.append([F(str((y-x)/2e-8))for x,y in zip(*us)])
 return[F(str(x))for x in c],list(zip(*v)),seeds

def verify(dl,du,el,eu,r):
 SEAM_INFO.clear();r=[r]*4 if isinstance(r,F)else r
 dc=(dl+du)/2;ec=(el+eu)/2;hd=(du-dl)/2;he=(eu-el)/2;c,v,seeds=candidate(dc,ec)
 b=[Jet(Iv.box(c[i],r[i]+abs(v[i][0])*hd+abs(v[i][1])*he),[Iv(int(i==j))for j in I]+[Iv(x)for x in v[i]])for i in I]
 bp=[Jet(x)for x in c];d=Jet(Iv.box(dc,hd),[Iv(0)]*4+[Iv(1),Iv(0)]);e=Jet(Iv.box(ec,he),[Iv(0)]*5+[Iv(1)])
 dp=Jet(dc);ep=Jet(ec);minq=1;maxlip=0
 for t in range(64):
  S=[0,1,3]if t<4 else[0,1,2];seam=t==4
  bp,_,_,pc=stage(bp,dp,ep,seeds[t],S,seam,True)
  b,mq,lp,bc=stage(b,d,e,seeds[t],S,seam);minq=min(minq,mq);maxlip=max(maxlip,lp)
  assert len(pc)<=len(bc) and all(y.lo<=x.lo and x.hi<=y.hi for pr,br in zip(pc,bc)for x,y in zip(pr,br)),('center root outside domain',t)
  assert all(row[i].lo*40000>3*D for row in bc for i in(0,1))
  for i in I:
   rad=sum(mag(b[i].d[j])*r[j] for j in I)+mag(b[i].d[4])*hd+mag(b[i].d[5])*he
   b[i].v=around(bp[i].v,rad)
  if VERBOSE and t in(4,15,31,63):print('STAGE',t,'minq01',minq,'max stage Newton lip',maxlip,flush=True)
 L=[sum(mag(x)*r[j]for j,x in enumerate(row.d[:4]))/r[i]for i,row in enumerate(b)]
 R=[mag(bp[i].v-c[i])+mag(b[i].d[4]-v[i][0])*hd+mag(b[i].d[5]-v[i][1])*he for i in I]
 if VERBOSE:print('RETURN L',list(map(float,L)),'R/r',[float(x/rr)for x,rr in zip(R,r)],flush=True)
 assert all(x*rr+y<rr for x,y,rr in zip(L,R,r)),('return failure',[float(x)for x in L],[float(x/rr)for x,rr in zip(R,r)],list(map(float,r)))
 if VERBOSE:print('SEAM data gap, signedhazard, Schur',SEAM_INFO,flush=True)
 assert all(x<F(7,40)for x in L) and all(x/rr<F(2,5)for x,rr in zip(R,r))
 print('PASS',float(dl),float(du),float(el),float(eu),'L',float(max(L)),'R/r',float(max(x/rr for x,rr in zip(R,r))),'q01',minq,'mode',SEAM_INFO[0][2],flush=True)

if __name__=='__main__':
 start=time.time()
 for k in range(340,360):
  verify(F(0),F(1,10**5),F(k,1000),F(k+1,1000),[F(5,10**5),F(15,10**7),F(1,10**6),F(5,10**3)])
 print('COMPLETE CONNECTED BOX delta[0,1e-5],epsilon[.34,.36];20 closed cells;SECONDS',time.time()-start)
