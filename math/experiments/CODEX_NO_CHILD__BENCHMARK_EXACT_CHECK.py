"""Exact Bernstein exclusion checker for the no-child cycle benchmark.
Original nonempty rewards are 4+Z; live/Never=0. Optional M defaults14.
All arithmetic is rational/integer. Failure of a check makes no claim.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb,lcm
import sys
M=Q(sys.argv[1]) if __name__=='__main__' and len(sys.argv)>1 else Q(14)
G=[[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]]
succ=[1,3,0,2]
Z=[[Q(0)]*16 for i in range(4)]
for j in range(4):
 for i in range(4):Z[i][1<<j]=Q(G[i][j])
for D in range(1,16):
 if D.bit_count()<2:continue
 for i in range(4):
  if D>>i&1:Z[i][D]=Q(-5)
for j,i in enumerate(succ):Z[i][(1<<i)|(1<<j)]=Q(G[i][j])+M
G=[[Q(x) for x in row] for row in G]

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
floor=[min([Q(-4)]+[Z[i][a] for a in range(1,16) if not (a>>i&1)]) for i in range(4)]
assert floor==[-4]*4
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
  n=tuple(m[i] for i in free);out[n]=out.get(n,Q(0))+c
 return clean(out)

def exclude(pat,polynomials=F):
 free=[i for i in range(4) if pat[i]==2];d=len(free)
 ps=[restrict(p,pat,free) for p in polynomials]
 tags=['eq' if v==2 else 'le' if v==0 else 'ge' for v in pat]
 if not d:
  vals=[p.get((),Q(0)) for p in ps]
  assert any(v>0 if t=='le' else v<0 if t=='ge' else v!=0 if t=='eq' else False for v,t in zip(vals,tags))
  return 1
 if d==1 and 1 not in pat:
  # Verify a quiet row's actual polynomial is strictly positive for q>0.
  # This rule is derived from the new table, not inherited from a prior family.
  assert any(tags[i]=='le' and ps[i] and all(c>=0 for c in ps[i].values()) for i in range(4))
  return 1
 E=None
 if d>=2:
  A=[[G[i][j] for j in free] for i in free];V=inverse(A)
  if 1 not in pat:
   for ii,i in enumerate(free):
    assert ps[i].get((0,)*d,Q(0))==0
    for j in range(d):
     unit=tuple(int(k==j) for k in range(d))
     assert ps[i].get(unit,Q(0))==-A[ii][j]
   for ii,i in enumerate(free):
    low={m:c for m,c in ps[i].items() if sum(m)<2}
    expected={tuple(int(k==j) for k in range(d)):-A[ii][j] for j in range(d) if A[ii][j]}
    assert low==expected
   C=[sum(abs(c) for m,c in ps[i].items() if sum(m)>=2) for i in free]
   K=max(sum(abs(V[i][j])*C[j] for j in range(d)) for i in range(d))
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
 degrees=[max([1]+[m[i] for p in ps for m in p]) for i in range(d)]
 inds=list(product(*(range(k+1) for k in degrees)));loc={a:i for i,a in enumerate(inds)};size=len(inds)
 Bs=[]
 for p in ps:
  row=[]
  for k in inds:
   b=Q(0)
   for m,c in p.items():
    if all(m[i]<=k[i] for i in range(d)):
     for i in range(d):c*=Q(comb(k[i],m[i]),comb(degrees[i],m[i]))
     b+=c
   row.append(b)
  Bs.append(row)
 den=lcm(*(b.denominator for row in Bs for b in row));Bs=[[int(b*den) for b in row] for row in Bs]
 fibers=[]
 for axis in range(d):
  lines=[]
  for a in inds:
   if a[axis]:continue
   line=[]
   for v in range(degrees[axis]+1):
    b=list(a);b[axis]=v;line.append(loc[tuple(b)])
   lines.append(line)
  fibers.append(lines)
 stack=[(Bs,(0,)*d,(0,)*d)];nodes=0
 while stack:
  bs,ks,ds=stack.pop();nodes+=1
  if any((min(r)>0 or max(r)<0) if t=='eq' else min(r)>0 if t=='le' else max(r)<0 if t=='ge' else False for r,t in zip(bs,tags)):continue
  if E is not None and all(ds[i]>=E and ks[i]+1<=2**(ds[i]-E) for i in range(d)):continue
  assert nodes<=100000 and max(ds)<=35, ('UNRESOLVED',pat,ks,ds)
  axis=min(range(d),key=lambda i:ds[i]);left=[];right=[]
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
 assert len(sys.argv)<=2
 total=sum(exclude(pat) for pat in product((0,1,2),repeat=4) if any(pat))
 if M in (10,12,13,14):assert total=={10:426,12:482,13:514,14:560}[M]
 print(f'EXACT RATIONAL PASS: M={M}; all80 nonzero stationary patterns excluded; {total} nodes',flush=True)
 roots=sum(exclude(pat,ROOT) for pat in product((0,1,2),repeat=4) if 1 in pat)
 if M in (10,12,13,14):assert roots==65
 print(f'EXACT RATIONAL PASS: M={M}; all65 sure-root patterns excluded; {roots} nodes',flush=True)
