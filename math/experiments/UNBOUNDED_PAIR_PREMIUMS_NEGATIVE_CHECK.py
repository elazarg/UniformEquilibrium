"""Exact one-box certificate for K>=0 and p<=-max(200,2K).
Standalone standard-library rational/dyadic interval arithmetic.
The finite arithmetic certifies root existence/guards, not the game consumer.
Run: python UNBOUNDED_PAIR_PREMIUMS_NEGATIVE_CHECK.py
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

def core(C,D,w,s,u):
 c=s*C;d=s*D
 Q=[-u*D-100*w+(u+111*s)*D*w,-C+3*w+(1-s)*C*w,-D*(100-101*c)]
 F=[(-(u+s)*D-97*w+(u+100*s)*D*w)/((1-d)*(1-w)),(-C+2*c+4*w+(1-3*s)*C*w)/((1-c)*(1-w)),(2*C-101*D+106*c*D)/((1-c)*(1-d))]
 return Q,F

def model(v,s,u):
 C,D,U,V,w,Y,t,E0=v
 e=C/(3+(1-s)*C);Z=2*Y/(101-106*s*Y)
 roots=[(C,D,e),(U,V,w),(Y,Z,t)]
 qf=[core(*q,s,u) for q in roots]
 res=[]
 for j in range(2):res += [qf[j][1][k]-qf[j+1][0][k] for k in range(3)]
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

def box(x,r):
 xx=[I(z) for z in x];rr=[I(z) for z in r]
 return [I(a.lo-b.hi,a.hi+b.hi,raw=True) for a,b in zip(xx,rr)]

def inside(xx,yy):return all(x.lo>y.lo and x.hi<y.hi for x,y in zip(xx,yy))

SEED3=[Q(9,397),Q(54296564078592426,63070111151171990729),Q(573,39409),Q(654500574858,1572938403151657),Q(291,39700),Q(25581,3912673),Q(28227,3940900),Q(4738019,3912673)]

def pointdata(v,s,u):
 dim=len(v)
 vv=[A(I(x),[I(int(i==j)) for j in range(dim+2)]) for i,x in enumerate(v)]
 ss=A(I(s),[I(0)]*dim+[I(1),I(0)]);uu=A(I(u),[I(0)]*(dim+1)+[I(1)])
 ff=model(vv,ss,uu)[0]
 return [midpoint(f.v) for f in ff],[[midpoint(g) for g in f.g[:dim]] for f in ff],[[midpoint(g) for g in f.g[dim:]] for f in ff]

def proposal(v,s,u):
 v=list(map(Q,v))
 for _ in range(3):
  f,j,par=pointdata(v,s,u);dx=solve(j,[[z] for z in f]);v=[rounded(x-z[0]) for x,z in zip(v,dx)]
 f,j,par=pointdata(v,s,u);d=len(v);R=solve(j,[[Q(int(i==j)) for j in range(d)] for i in range(d)])
 slope=[[-sum(R[i][j]*par[j][k] for j in range(d)) for k in range(2)] for i in range(d)]
 return v,R,slope

def cert(v,R,rad,sl,sr,ul,ur):
 d=len(v);SI=I(sl,sr);UI=I(ul,ur);xx=[I(x) for x in v];rr=[I(x) for x in rad];outer=box(v,rad)
 vv=[A(x,[I(int(i==j)) for j in range(d)]) for i,x in enumerate(outer)]
 ff,gg,qs=model(vv,SI,UI);J=[f.g for f in ff]
 f=model(xx,I((sl+sr)/2),I((ul+ur)/2))[0]
 vv=[A(x,[I(0),I(0)]) for x in xx]
 pf=model(vv,A(SI,[I(1),I(0)]),A(UI,[I(0),I(1)]))[0]
 RI=[[I(x) for x in row] for row in R]
 shift=[]
 for i in range(d):
  z=-sum(RI[i][j]*f[j] for j in range(d))
  for k,(lo,hi) in enumerate([(sl,sr),(ul,ur)]):
   z=z-sum(RI[i][j]*pf[j].g[k] for j in range(d))*I(-(hi-lo)/2,(hi-lo)/2)
  shift.append(z)
 B=[[I(int(i==j))-sum(RI[i][k]*J[k][j] for k in range(d)) for j in range(d)] for i in range(d)]
 im=[shift[i]+sum(B[i][j]*I(-rad[j],rad[j]) for j in range(d)) for i in range(d)]
 inc=max(max(-im[i].lo,im[i].hi)/rr[i].lo for i in range(d))
 norms=[sum(I(max(abs(B[i][j].lo),abs(B[i][j].hi)),max(abs(B[i][j].lo),abs(B[i][j].hi)),raw=True)*rr[j] for j in range(d))/rr[i] for i in range(d)]
 con=max(x.hi/SCALE for x in norms)
 if not(all(2*im[i].lo>-rr[i].lo and 2*im[i].hi<rr[i].lo for i in range(d)) and all(10*x.hi<SCALE for x in norms)):return False,(inc,con)
 guards=[g.v for g in gg]
 for j,(C,D,w) in enumerate(qs):
  C,D,w=C.v,D.v,w.v
  guards +=[C,D,w,1-SI*C,1-SI*D,1-w]
 if not all(10000*g.lo>SCALE for g in guards):return False,('guard',[(j,g) for j,g in enumerate(guards) if 10000*g.lo<=SCALE])
 return True,(inc,con,min(g.lo/SCALE for g in guards))

def cover(ns,nu):
 worst=[0,0];ming=1.
 for i in range(ns):
  for j in range(nu):
   sl=Q(i,200*ns);sr=Q(i+1,200*ns);ul=Q(j,2*nu);ur=Q(j+1,2*nu)
   v,R,z=proposal(SEED3,(sl+sr)/2,(ul+ur)/2)
   rad=[max(Q(3,2)*(abs(zz[0])*(sr-sl)+abs(zz[1])*(ur-ul)),abs(x)/100000,Q(1,10**10)) for x,zz in zip(v,z)]
   ok,data=cert(v,R,rad,sl,sr,ul,ur)
   if not ok:print('FAIL',ns,nu,i,j,data,flush=True);return False
   worst=[max(worst[k],data[k]) for k in range(2)];ming=min(ming,data[2])
 print('PASS',ns,nu,worst,ming,flush=True);return True

if __name__=='__main__':
 assert cover(1,1)
