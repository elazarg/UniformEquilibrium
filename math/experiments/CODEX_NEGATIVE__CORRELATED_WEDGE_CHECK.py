"""Exact negative-wedge certificate for K>=100 and ratio*K<=p<=0.
Stdlib only; default ratio=-1/10. All arithmetic is rational. The extra
coordinate s in [0,1] means p=ratio*s*K. The displayed table is the fixed
canonical completion, with original own-singleton levels equal to one.
All 80 nonzero stationary and all 65 sure-root patterns are checked.
A failure or resource-limit assertion makes no exclusion claim.
The support123 origin argument uses a divided correlated polynomial justified
by F3=0 and strictly positive q1; its complete algebra is in the companion note.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb, lcm
import sys

ratio = Q(sys.argv[1]) if __name__=='__main__' and len(sys.argv)>1 else Q(-1,10)
assert ratio<0
assert __name__!='__main__' or len(sys.argv)<=2
pair_premium = 100*ratio
pair_cost = Q(100)
joining_premium = Q(0)
uniform_k = True
Z = [
 [0,0,3,0,-1,0,-12,-13,3,-3,2,-7,-6,-7,-8,-5],
 [0,2,0,-1,1,5,-100,6,-3,3,-100,8,9,-8,11,-9],
 [0,2,-2,-10,0,-10,0,-9,-1,-5,-1,10,3,-3,2,8],
 [0,-1,-2,-12,1,7,-6,11,0,1,0,-10,-100,Q(15,2),1,Q(21,2)],
]
Z[2][6] = pair_premium
Z[1][6] = -pair_cost
Z[3][10] = joining_premium
Z = [[Q(x) for x in row] for row in Z]
G = [[Z[i][1 << j] for j in range(4)] for i in range(4)]

def clean(p): return {m:c for m,c in p.items() if c}
def add(p,r):
 out=p.copy()
 for m,c in r.items():out[m]=out.get(m,Q(0))+c
 return clean(out)
def scale(p,c):return clean({m:v*c for m,v in p.items()})
def mul(p,r):
 out={}
 for m,c in p.items():
  for n,d in r.items():
   k=tuple(a+b for a,b in zip(m,n));out[k]=out.get(k,Q(0))+c*d
 return clean(out)
one={(0,0,0,0):Q(1)}
xs=[{tuple(int(j==i) for j in range(4)):Q(1)} for i in range(4)]
cs=[add(one,scale(x,-1)) for x in xs]
F=[]; ROOT=[]; HS=[]
floor=[min([Q(-1)]+[Z[i][a] for a in range(1,16) if not (a>>i&1)]) for i in range(4)]
assert floor==[-12,-8,-10,-12]
for i in range(4):
 P={};R={};H=one
 for j in range(4):
  if j!=i:H=mul(H,cs[j])
 HS.append(H)
 for mask in range(16):
  if mask>>i&1:continue
  w=one
  for j in range(4):
   if j!=i:w=mul(w,xs[j] if mask>>j&1 else cs[j])
  P=add(P,scale(w,Z[i][mask]));R=add(R,scale(w,Z[i][mask|(1<<i)]))
 F.append(add(mul(add(one,scale(H,-1)),R),scale(P,-1)))
 ROOT.append(add(add(R,scale(P,-1)),scale(H,-floor[i])))
assert all(max(m)<=2 for p in F for m in p)

# Derivatives with respect to Delta=K-100 on the ray p=beta*K.
a1=mul(mul(mul(add(one,scale(HS[1],-1)),cs[0]),xs[2]),cs[3])
a2=mul(mul(mul(add(one,scale(HS[2],-1)),cs[0]),xs[1]),cs[3])
b1=mul(mul(cs[0],xs[2]),cs[3])
b2=mul(mul(cs[0],xs[1]),cs[3])
w1=scale(mul(add(one,scale(HS[2],-1)),xs[1]),ratio)
w2=mul(add(one,scale(HS[1],-1)),xs[2])
assert add(scale(mul(w1,a1),-1),scale(mul(w2,a2),ratio))=={}
assert add(scale(mul(xs[1],b1),-ratio),scale(mul(xs[2],b2),ratio))=={}
CF=add(scale(mul(mul(add(one,scale(HS[2],-1)),xs[1]),F[1]),ratio),mul(mul(add(one,scale(HS[1],-1)),xs[2]),F[2]))
CR=add(scale(mul(xs[1],ROOT[1]),ratio),mul(xs[2],ROOT[2]))

# Embed q-polynomials into five variables and interpolate in s=beta/beta_max.
# Only F2 and ROOT2 change with beta; CF and CR are affine in beta as well.
def embed(p, power=0):return {m+(power,):c for m,c in p.items()}
changeF=scale(mul(mul(mul(add(one,scale(HS[2],-1)),cs[0]),xs[1]),cs[3]),pair_premium)
changeR=scale(mul(mul(cs[0],xs[1]),cs[3]),pair_premium)
Fzero=list(F);Fzero[2]=add(F[2],scale(changeF,-1))
Rzero=list(ROOT);Rzero[2]=add(ROOT[2],scale(changeR,-1))
CFzero=mul(mul(add(one,scale(HS[1],-1)),xs[2]),Fzero[2])
CRzero=mul(xs[2],Rzero[2])
def interpolate(p0,p1):return add(embed(p0),embed(add(p1,scale(p0,-1)),1))
F=[interpolate(a,b) for a,b in zip(Fzero,F)]
ROOT=[interpolate(a,b) for a,b in zip(Rzero,ROOT)]
CF=interpolate(CFzero,CF);CR=interpolate(CRzero,CR)
assert all(m[-1]<=1 for pp in F+ROOT+[CF,CR] for m in pp)
assert all(max(m[:4])<=3 for m in CF)

def inverse(A):
 n=len(A);a=[list(row)+[Q(int(i==j)) for j in range(n)] for i,row in enumerate(A)]
 for j in range(n):
  k=next(i for i in range(j,n) if a[i][j]);a[j],a[k]=a[k],a[j]
  t=a[j][j];a[j]=[v/t for v in a[j]]
  for i in range(n):
   if i!=j:
    t=a[i][j];a[i]=[v-t*w for v,w in zip(a[i],a[j])]
 return [row[n:] for row in a]

def restrict(p,pat,free):
 out={}
 for m,c in p.items():
  if any(pat[i]==0 and m[i] for i in range(4)):continue
  n=tuple(m[i] for i in free)+(m[4] if len(m)>4 else 0,);out[n]=out.get(n,Q(0))+c
 return clean(out)

def exclude(pat,polynomials=F):
 if polynomials is F and pat[0]==0 and pat[3]==0 and pat[1]!=0 and pat[2]!=0:
  return 1 # F1=-q2-Kq2^2<0 on support12, incompatible with mixed/sure1.
 if polynomials is F and pat[0]==0 and pat[2]==0 and pat[1]!=0 and pat[3]==2:
  return 1 # F3=2q1>0 on support13; mixed3 requires equality.
 # Increasing K decreases row1 by a nonnegative multiple of
 # (1-q0)q2(1-q3), with an additional factor (1-H1) for F.
 # A formerly active/sure row therefore requires its baseline value >=0;
 # a quiet row imposes no useful baseline inequality.
 relaxed=uniform_k and pat[2]!=0 and pat[0]!=1 and pat[3]!=1
 free=[i for i in range(4) if pat[i]==2];d=len(free)
 ps=[restrict(p,pat,free) for p in polynomials]
 tags=['eq' if v==2 else 'le' if v==0 else 'ge' for v in pat]
 if relaxed:tags[1]='ignore' if pat[1]==0 else 'ge'
 relaxed_p=pat[1]!=0 and pat[0]!=1 and pat[3]!=1
 if relaxed_p:tags[2]='ignore' if pat[2]==0 else 'ge'
 # A signed combination cancels the shared unbounded parameter; signs below
 # account for its nonpositive row1 and nonnegative row2 multipliers.
 weights=[scale(mul(add(one,scale(HS[2],-1)),xs[1]),ratio),mul(add(one,scale(HS[1],-1)),xs[2])] if polynomials is F else [scale(xs[1],ratio),xs[2]]
 signs=[]
 for j,w in zip((1,2),weights):
  if restrict(w,pat,free):signs.append(((-1) if j==1 else 1)*(0 if pat[j]==2 else -1 if pat[j]==0 else 1))
 if not signs or all(v==0 for v in signs):ctag='eq'
 elif all(v>=0 for v in signs):ctag='ge'
 elif all(v<=0 for v in signs):ctag='le'
 else:ctag='ignore'
 ps.append(restrict(CF if polynomials is F else CR,pat,free));tags.append(ctag)
 if d==1 and 1 not in pat:
  j=free[0]
  assert any(i!=j and G[i][j]<0 and Z[i][(1<<i)|(1<<j)]>=0 for i in range(4))
  return 1
 E=None
 custom_origin=None
 if polynomials is F and pat==(0,2,2,2):
  # F3=2y-z*R. On the three strictly mixed owners R*z=2*y.
  # Divide the correlated equality by y and multiply by R, using this
  # relation; the resulting polynomial is still necessary, including at
  # beta=0. Adding (y-z)*F3 makes its quadratic part coercive on the nonnegative orthant.
  zero=(0,)*4
  yy={(1,0,0,0):Q(1)};zz={(0,1,0,0):Q(1)};ww={(0,0,1,0):Q(1)}
  rr=add(scale(yy,2),scale(ps[3],-1))
  assert all(m[1]>=1 for m in rr)
  rr={tuple(v-(idx==1) for idx,v in enumerate(m)):c for m,c in rr.items()}
  opp1=add(add(zz,ww),scale(mul(zz,ww),-1))
  opp2=add(add(yy,ww),scale(mul(yy,ww),-1))
  beta={(0,0,0,1):ratio}
  divided=add(mul(mul(mul(beta,rr),opp2),ps[1]),scale(mul(opp1,ps[2]),2))
  positive=add(divided,mul(add(yy,scale(zz,-1)),ps[3]))
  assert not any(sum(m[:-1])<2 for m in positive)
  quad={m:c for m,c in positive.items() if sum(m[:-1])==2}
  monoms={m[:-1] for m in quad}
  for monom in monoms:
   endpoints=[quad.get(monom+(0,),Q(0)),sum(c for m,c in quad.items() if m[:-1]==monom)]
   assert min(endpoints)>=0,(monom,endpoints)
  for axis in range(3):
   monom=tuple(2*(i==axis) for i in range(3))
   endpoints=[quad.get(monom+(0,),Q(0)),sum(c for m,c in quad.items() if m[:-1]==monom)]
   assert min(endpoints)>=1,(monom,endpoints)
  custom_origin=sum(abs(c) for m,c in positive.items() if sum(m[:-1])>=3)
  assert custom_origin>0
  E=1
  while Q(1,2**E)>=1/custom_origin:E+=1
  ps.append(positive);tags.append('eq')
 if d>=2:
  A=[[G[i][j] for j in free] for i in free];V=inverse(A)
  if 1 not in pat and custom_origin is None:
   for ii,i in enumerate(free):
    assert ps[i].get((0,)*(d+1),Q(0))==0
    for j in range(d):
     unit=tuple(int(k==j) for k in range(d))+(0,)
     assert ps[i].get(unit,Q(0))==-A[ii][j]
   for ii,i in enumerate(free):
    low={m:c for m,c in ps[i].items() if sum(m[:-1])<2}
    wanted={tuple(int(k==j) for k in range(d))+(0,):-A[ii][j] for j in range(d) if A[ii][j]}
    assert low==wanted, ('UNEXPECTED_LOW_TERM',pat,i,low,wanted)
   C=[sum(abs(c) for m,c in ps[i].items() if sum(m[:-1])>=2) for i in free]
   weights=None
   for ell in product(range(1,9),repeat=d):
    coeff=[sum(Q(ell[i])*V[i][j] for i in range(d)) for j in range(d)]
    if relaxed and 1 in free and coeff[free.index(1)]<0:continue
    if relaxed_p and 2 in free and coeff[free.index(2)]<0:continue
    weights=ell;break
   assert weights is not None, ('NO_ORIGIN_WEIGHTS',pat,V)
   K=sum(abs(coeff[j])*C[j] for j in range(d))/min(weights)
   if not K:return 1
   E=1
   while Q(1,2**E)>=1/K:E+=1
  extra=[];etags=[]
  for row in V:
   pp={}
   for cc,j in zip(row,free):pp=add(pp,scale(ps[j],cc))
   signs=[]
   for cc,j in zip(row,free):
    if tags[j]=='ge':signs.append(cc)
    elif tags[j]=='le':signs.append(-cc)
    else:assert tags[j]=='eq'
   if all(cc==0 for cc in signs):tag='eq'
   elif all(cc>=0 for cc in signs):tag='ge'
   elif all(cc<=0 for cc in signs):tag='le'
   else:continue
   extra.append(pp);etags.append(tag)
  ps+=extra;tags+=etags
 ndim=d+1
 degrees=[max([1]+[m[i] for p in ps for m in p]) for i in range(ndim)]
 inds=list(product(*(range(k+1) for k in degrees)));loc={a:i for i,a in enumerate(inds)};size=len(inds)
 Bs=[]
 for p in ps:
  row=[]
  for k in inds:
   b=Q(0)
   for m,c in p.items():
    if all(m[i]<=k[i] for i in range(ndim)):
     for i in range(ndim):c*=Q(comb(k[i],m[i]),comb(degrees[i],m[i]))
     b+=c
   row.append(b)
  Bs.append(row)
 den=lcm(*(b.denominator for row in Bs for b in row));Bs=[[int(b*den) for b in row] for row in Bs]
 fibers=[]
 for axis in range(ndim):
  lines=[]
  for a in inds:
   if a[axis]:continue
   line=[]
   for v in range(degrees[axis]+1):
    b=list(a);b[axis]=v;line.append(loc[tuple(b)])
   lines.append(line)
  fibers.append(lines)
 stack=[(Bs,(0,)*ndim,(0,)*ndim)];nodes=0
 while stack:
  bs,ks,ds=stack.pop();nodes+=1
  if any((min(r)>0 or max(r)<0) if t=='eq' else min(r)>0 if t=='le' else max(r)<0 if t=='ge' else False for r,t in zip(bs,tags)):continue
  if E is not None and all(ds[i]>=E and ks[i]+1<=2**(ds[i]-E) for i in range(d)):continue
  assert nodes<=100000 and max(ds)<=35, ('UNRESOLVED',pat,ks,ds)
  axis=min(range(d or 1),key=lambda i:ds[i]);left=[];right=[]
  for row in bs:
   a=[0]*size;b=[0]*size
   deg=degrees[axis]
   for line in fibers[axis]:
    for r,idx in enumerate(line):
     a[idx]=2**(deg-r)*sum(comb(r,j)*row[line[j]] for j in range(r+1))
     b[idx]=2**r*sum(comb(deg-r,j)*row[line[r+j]] for j in range(deg-r+1))
   left.append(a);right.append(b)
  nd=list(ds);nd[axis]+=1;lo=list(ks);hi=list(ks);lo[axis]*=2;hi[axis]=2*hi[axis]+1
  stack.extend([(right,tuple(hi),tuple(nd)),(left,tuple(lo),tuple(nd))])
 return nodes

if __name__=='__main__':
 total=0
 for pat in product((0,1,2),repeat=4):
  if any(pat):total+=exclude(pat)
 expected=(1230,369) if ratio==Q(-1,10) else None
 if expected:assert total==expected[0],total
 scope=f'every K>=100, {ratio}*K<=p<=0; canonical completion'
 print(f'EXACT RATIONAL PASS: {scope}; all 80 nonzero supports excluded; {total} nodes')
 roots=0
 for pat in product((0,1,2),repeat=4):
  if 1 in pat:roots+=exclude(pat,ROOT)
 if expected:assert roots==expected[1],roots
 print(f'EXACT RATIONAL PASS: {scope}; all 65 sure-root patterns excluded; {roots} nodes')
