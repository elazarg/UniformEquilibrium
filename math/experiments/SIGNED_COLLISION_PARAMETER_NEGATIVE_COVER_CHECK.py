"""Finite exact certificates for the negative-p collision macros.
Only Python standard-library integers and fractions are used. Newton iteration
proposes rational centers; every conclusion is checked by outward intervals.
"""
from fractions import Fraction as Q
Fraction=Q
SCALE=2**80
class I:
 def __init__(self,a=0,b=None,raw=False):
  if raw:self.lo,self.hi=a,b;return
  if isinstance(a,I):self.lo,self.hi=a.lo,a.hi;return
  a=Fraction(str(a));b=a if b is None else Fraction(str(b))
  self.lo=a.numerator*SCALE//a.denominator
  self.hi=-((-b.numerator*SCALE)//b.denominator)
 def __add__(a,b):
  if isinstance(b,A):return NotImplemented
  a,b=I(a),I(b);return I(a.lo+b.lo,a.hi+b.hi,raw=True)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo,raw=True)
 def __sub__(a,b):return a+(-b if isinstance(b,(I,A)) else -I(b))
 def __rsub__(a,b):return I(b)+(-a)
 def __mul__(a,b):
  if isinstance(b,A):return NotImplemented
  a,b=I(a),I(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
  return I(min(v)//SCALE,-((-max(v))//SCALE),raw=True)
 __rmul__=__mul__
 def __truediv__(a,b):
  if isinstance(b,A):return NotImplemented
  a,b=I(a),I(b);assert b.lo*b.hi>0,'zero denominator'
  vals=[Fraction(x*SCALE,y) for x in [a.lo,a.hi] for y in [b.lo,b.hi]]
  low,high=min(vals),max(vals)
  return I(low.numerator//low.denominator,-((-high.numerator)//high.denominator),raw=True)
 def __rtruediv__(a,b):return I(b)/a
 def mag(a):return max(abs(a.lo),abs(a.hi))/SCALE
 def lower(a):return a.lo/SCALE
 def upper(a):return a.hi/SCALE
 def __repr__(a):return str((a.lower(),a.upper()))

class A:
 def __init__(self,v,g):self.v=I(v);self.g=g
 def __add__(a,b):
  if not isinstance(b,A):b=A(b,[I(0)]*len(a.g))
  return A(a.v+b.v,[x+y for x,y in zip(a.g,b.g)])
 __radd__=__add__
 def __neg__(a):return A(-a.v,[-x for x in a.g])
 def __sub__(a,b):return a+(-b if isinstance(b,(A,I)) else -I(b))
 def __rsub__(a,b):return -a+b
 def __mul__(a,b):
  if not isinstance(b,A):b=A(b,[I(0)]*len(a.g))
  return A(a.v*b.v,[x*b.v+a.v*y for x,y in zip(a.g,b.g)])
 __rmul__=__mul__
 def __truediv__(a,b):
  if not isinstance(b,A):b=A(b,[I(0)]*len(a.g))
  return A(a.v/b.v,[(x*b.v-a.v*y)/(b.v*b.v) for x,y in zip(a.g,b.g)])
 def __rtruediv__(a,b):return A(b,[I(0)]*len(a.g))/a

def core(C,D,w,s):
 c=s*C;d=s*D
 Q=[-100*d-100*w+211*d*w,-C+3*w+(1-s)*C*w,-D*(100-101*c)]
 F=[(-101*d-97*w+200*d*w)/((1-d)*(1-w)),(-C+2*c+4*w+(1-3*s)*C*w)/((1-c)*(1-w)),(2*C-101*D+106*c*D)/((1-c)*(1-d))]
 return Q,F

def model(v,s,n):
 if n==1:
  C,E0=v
  e=C/(3+(1-s)*C);Z=2*C/(101-106*s*C)
  roots=[(C,Z,e)]
 elif n==3:
  C,D,U,V,w,Y,t,E0=v
  e=C/(3+(1-s)*C);Z=2*Y/(101-106*s*Y)
  roots=[(C,D,e),(U,V,w),(Y,Z,t)]
 else:
  C,Y,t,E0=v
  e=C/(3+(1-s)*C);Z=2*Y/(101-106*s*Y)
  T3=-Z*(100-101*s*Y)
  D=(2*C-T3*(1-s*C))/(101-106*s*C-s*T3*(1-s*C))
  roots=[(C,D,e),(Y,Z,t)]
 qf=[core(*q,s) for q in roots]
 res=[]
 for j in range(n-1):res += [qf[j][1][k]-qf[j+1][0][k] for k in (range(3) if n==3 else range(2))]
 x=-qf[-1][1][0];E2=qf[-1][1][1]
 row0=[E0]
 for Ck,Dk,wk in roots[::-1]:
  ck=s*Ck;dk=s*Dk
  row0.append(3*ck-dk+3*wk-14*ck*dk-4*ck*wk-8*dk*wk+13*ck*dk*wk+(1-ck)*(1-dk)*(1-wk)*row0[-1])
 C0=row0[-1];C1=qf[0][0][0];C3=s*qf[0][0][2]
 b=C0/(1+C0);B1=b+(1-b)*C1;B3=b+(1-b)*C3
 a=B3/(1+B3);A1=2*a+(1-a)*B1;A2=2*a
 R=1-x/3;V0=(E0-x)/R;V2=(E2+x/3)/R;h=V0/3
 res += [A1*(1-h)-3*h,A2*(1-h)-V2-h]
 guards=[a,1-a,b,1-b,h,1-h,B1,B3,x,3-x,E0-x,E2-3*x/100,V2]+row0
 return res,guards,roots


def rounded(x,bits=60):
 sc=2**bits
 return Q((x.numerator*sc+x.denominator//2)//x.denominator,sc)

def midpoint(x):return Q(x.lo+x.hi,2*SCALE)

def solve(mat,rhs):
 a=[list(row)+list(rr) for row,rr in zip(mat,rhs)]
 d=len(mat);m=len(rhs[0])
 for j in range(d):
  k=next(k for k in range(j,d) if a[k][j])
  a[j],a[k]=a[k],a[j]
  z=a[j][j];a[j]=[x/z for x in a[j]]
  for k in range(d):
   if k!=j:
    z=a[k][j]
    a[k]=[x-z*y for x,y in zip(a[k],a[j])]
 return [row[d:d+m] for row in a]

def pointdata(x,s,n):
 d=len(x)
 av=[A(I(t),[I(int(j==k)) for j in range(d+1)]) for k,t in enumerate(x)]
 fs,_,_=model(av,A(I(s),[I(0)]*d+[I(1)]),n)
 return ([midpoint(f.v) for f in fs],
         [[midpoint(z) for z in f.g[:d]] for f in fs],
         [midpoint(f.g[d]) for f in fs])

def proposal(ini,s,n,steps=3):
 x=[Q(z) for z in ini]
 for _ in range(steps):
  f,j,_=pointdata(x,s,n)
  dx=solve(j,[[z] for z in f])
  x=[rounded(t-z[0]) for t,z in zip(x,dx)]
 f,j,fs=pointdata(x,s,n);d=len(x)
 R=solve(j,[[Q(int(i==k)) for k in range(d)] for i in range(d)])
 slope=[-sum(R[i][j]*fs[j] for j in range(d)) for i in range(d)]
 return x,R,slope

def box(x,r):
 xx=[I(z) for z in x];rr=[I(z) for z in r]
 return [I(a.lo-b.hi,a.hi+b.hi,raw=True) for a,b in zip(xx,rr)]

def inside(xx,yy):return all(x.lo>y.lo and x.hi<y.hi for x,y in zip(xx,yy))

def certificate(x,R,sl,sr,n,r):
 d=len(x);SI=I(sl,sr);xx=[I(z) for z in x];rr=[I(z) for z in r]
 outer=box(x,r)
 av=[A(t,[I(int(j==k)) for j in range(d)]) for k,t in enumerate(outer)]
 FF,gg,roots=model(av,SI,n);J=[z.g for z in FF]
 f=model(xx,I((sl+sr)/2),n)[0]
 pf=model([A(t,[I(0)]) for t in xx],A(SI,[I(1)]),n)[0]
 fs=[z.g[0] for z in pf];ds=SI-I((sl+sr)/2)
 RI=[[I(z) for z in row] for row in R]
 shifts=[-sum(RI[i][j]*f[j] for j in range(d))-sum(RI[i][j]*fs[j] for j in range(d))*ds for i in range(d)]
 B=[[I(int(i==j))-sum(RI[i][k]*J[k][j] for k in range(d)) for j in range(d)] for i in range(d)]
 images=[shifts[i]+sum(B[i][j]*I(-rr[j].hi,rr[j].hi,raw=True) for j in range(d)) for i in range(d)]
 assert all(im.lo>-rr[i].lo and im.hi<rr[i].lo for i,im in enumerate(images)),('inclusion',n,sl,sr)
 norms=[sum(I(max(abs(B[i][j].lo),abs(B[i][j].hi)),max(abs(B[i][j].lo),abs(B[i][j].hi)),raw=True)*rr[j] for j in range(d))/rr[i] for i in range(d)]
 assert all(z.hi<SCALE for z in norms),('contraction',n,sl,sr)
 guards=[g.v if isinstance(g,A) else g for g in gg]
 roots=[[z.v if isinstance(z,A) else z for z in q] for q in roots]
 return guards,roots

def prepare(sl,sr,n,ini,rscale=Q(1)):
 x,R,z=proposal(ini,(sl+sr)/2,n)
 r=[max(Q(11,10)*abs(v)*(sr-sl),abs(t)/10000,Q(1,10**9))*rscale for t,v in zip(x,z)]
 g,q=certificate(x,R,sl,sr,n,r)
 return x,R,z,r,g,q

def legal(guards,roots,sr,skipwash=False,skiplast=False):
 assert all(g.lo>0 for j,g in enumerate(guards) if not(skipwash and j==11))
 for j,(C,D,w) in enumerate(roots):
  assert w.lo>0 and w.hi<SCALE
  assert (I(sr)*C).hi<SCALE and (I(sr)*D).hi<SCALE
  if not(skiplast and j==len(roots)-1):assert C.lo>0 and D.lo>0

def derivatives(x,R,z,r,sl,sr,n):
 d=len(x);SI=I(sl,sr);outer=box(x,r)
 av=[A(t,[I(int(j==k)) for j in range(d+1)]) for k,t in enumerate(outer)]
 FF,gg,_=model(av,A(SI,[I(0)]*d+[I(1)]),n)
 J=[f.g[:d] for f in FF];fs=[f.g[d] for f in FF]
 RI=[[I(z) for z in row] for row in R]
 E=[[I(int(i==j))-sum(RI[i][k]*J[k][j] for k in range(d)) for j in range(d)] for i in range(d)]
 const=[-sum(RI[i][j]*fs[j] for j in range(d)) for i in range(d)]
 for fac in [Q(1,100),Q(1,10),Q(1,2),Q(1),Q(2)]:
  rad=[fac*(abs(t)+Q(1,10000)) for t in z];zz=box(z,rad)
  image=[const[i]+sum(E[i][j]*zz[j] for j in range(d)) for i in range(d)]
  if inside(image,zz):break
 else:raise AssertionError('implicit derivative enclosure')
 gd=[g.g[d]+sum(g.g[j]*zz[j] for j in range(d)) for g in gg]
 return zz,gd

SEED3=[Q(9,397),Q(54296564078592426,63070111151171990729),Q(573,39409),Q(654500574858,1572938403151657),Q(291,39700),Q(25581,3912673),Q(28227,3940900),Q(4738019,3912673)]
SEED2=list(map(Q,['.02187','.0097','.00712','1.2093']))
SEED1=list(map(Q,['.02093','1.20475']))

def cover(n,lo,hi,steps,ini):
 for k in range(steps):
  sl=lo+(hi-lo)*k/steps;sr=lo+(hi-lo)*(k+1)/steps
  x,R,z,r,g,q=prepare(sl,sr,n,ini);ini=x
  legal(g,q,sr)
  if k%100==0:print('PASS cell',n,k,flush=True)
 print('PASS full cover',n,str(lo),str(hi),steps,flush=True)
 return ini

def switch(n,sl,sr,oldseed,newseed):
 x,R,z,r,g,roots=prepare(sl,sr,n,oldseed);oldbox=box(x,r)
 dd,gd=derivatives(x,R,z,r,sl,sr,n);assert gd[11].lo>0
 y,T,v,h,gg,rr=prepare(sl,sr,n+1,newseed)
 h=[3*t for t in h]
 if n==1:h[2]*=Q(11,10)
 gg,rr=certificate(y,T,sl,sr,n+1,h);newbox=box(y,h)
 dd,gd=derivatives(y,T,v,h,sl,sr,n+1)
 last=1 if n==1 else 5
 assert dd[last].hi<0
 legal(g,roots,sr,skipwash=True);legal(gg,rr,sr,skiplast=True)
 assert (101-106*I(sl,sr)*rr[-1][0]).lo>0
 for s,sign in [(sl,-1),(sr,1)]:
  xp,P,zp=proposal(x,s,n);rp=[Q(1,10**10)]*len(xp)
  gp,_=certificate(xp,P,s,s,n,rp)
  assert inside(box(xp,rp),oldbox)
  assert gp[11].hi<0 if sign<0 else gp[11].lo>0
 _,oldg,oq=model(oldbox,I(sl,sr),n);q=oldg[8]/100
 if n==1:
  inserted=[oldbox[0],I(0),q,(oldbox[1]-3*q)/(1-q)]
 else:
  C,D,e=oq[0];Y,Z,t=oq[1]
  inserted=[C,D,Y,Z,t,I(0),q,(oldbox[3]-3*q)/(1-q)]
 assert inside(inserted,newbox)
 print('PASS support switch',n,n+1,str(sl),str(sr),flush=True)

if __name__=='__main__':
 import sys
 mode=sys.argv[1] if len(sys.argv)>1 else 'all'
 if mode in ['all','ray']:cover(3,Q(0),Q(1,10),1000,SEED3)
 if mode in ['all','middle']:cover(2,Q(101,1000),Q(13,40),1000,SEED2)
 if mode in ['all','switches']:
  switch(2,Q(1,10),Q(101,1000),SEED2,list(map(Q,['.02187','.000625','.00973','.000193','.00712','0','.006977','1.1967'])))
  switch(1,Q(13,40),Q(163,500),SEED1,list(map(Q,['.0214','0','.006919','1.1923'])))
 print('ALL REQUESTED EXACT CHECKS PASSED',flush=True)
