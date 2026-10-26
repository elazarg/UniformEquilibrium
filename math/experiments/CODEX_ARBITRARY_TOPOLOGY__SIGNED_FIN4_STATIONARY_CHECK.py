"""Exact stationary and sure-root exclusions for a rational quitting table.
Standard library only. Native table columns are coalition masks 0,...,15;
original nonempty rewards are 1+Z, while live/Never remains zero.
Optional rational CLI arguments set p=Z_2({1,2}) and K=-Z_1({1,2});
their defaults are zero and 100.
Alternatively --uniform-k proves both exclusions for every K>=100 at p=0.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb, lcm
import sys

pair_premium = Q(0)
pair_cost = Q(100)
uniform_k = False
if __name__ == '__main__':
 args = sys.argv[1:]
 if args == ['--uniform-k']:
  uniform_k = True
 else:
  if len(args)>2 or any(a.startswith('--') for a in args):
   raise SystemExit('usage: SIGNED_FIN4_STATIONARY_CHECK.py [p] [K] | --uniform-k')
  if args:pair_premium = Q(args[0])
  if len(args)==2:pair_cost = Q(args[1])
Z = [
 [0,0,3,0,-1,0,-12,-13,3,-3,2,-7,-6,-7,-8,-5],
 [0,2,0,-1,1,5,-100,6,-3,3,-100,8,9,-8,11,-9],
 [0,2,-2,-10,0,-10,0,-9,-1,-5,-1,10,3,-3,2,8],
 [0,-1,-2,-12,1,7,-6,11,0,1,0,-10,-100,Q(15,2),1,Q(21,2)],
]
Z[2][6] = pair_premium
Z[1][6] = -pair_cost
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
F=[]; ROOT=[]
floor=[min([Q(-1)]+[Z[i][a] for a in range(1,16) if not (a>>i&1)]) for i in range(4)]
assert floor==[-12,-8,-10,-12]
for i in range(4):
 P={};R={};H=one
 for j in range(4):
  if j!=i:H=mul(H,cs[j])
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
 if uniform_k and polynomials is F and pat[0]==0 and pat[2]==2 and (pat[1]!=0 or pat[3]!=0):
  return 1 # F2>0: Q2=w(3-y)>=0, P2=-2y-w+2yw<0.
 # Increasing K decreases row1 by a nonnegative multiple of
 # (1-q0)q2(1-q3), with an additional factor (1-H1) for F.
 # A formerly active/sure row therefore requires its baseline value >=0;
 # a quiet row imposes no useful baseline inequality.
 relaxed=uniform_k and pat[2]!=0 and pat[0]!=1 and pat[3]!=1
 free=[i for i in range(4) if pat[i]==2];d=len(free)
 ps=[restrict(p,pat,free) for p in polynomials]
 tags=['eq' if v==2 else 'le' if v==0 else 'ge' for v in pat]
 if relaxed:tags[1]='ignore' if pat[1]==0 else 'ge'
 if not d:
  vals=[p.get((),Q(0)) for p in ps]
  assert any(v>0 if t=='le' else v<0 if t=='ge' else v!=0 if t=='eq' else False for v,t in zip(vals,tags))
  return 1
 if d==1 and 1 not in pat:
  j=free[0]
  assert any(i!=j and G[i][j]<0 and Z[i][(1<<i)|(1<<j)]>=0 for i in range(4))
  return 1
 E=None
 if d>=2:
  A=[[G[i][j] for j in free] for i in free];V=inverse(A)
  if 1 not in pat:
   if relaxed and 1 in free:
    # V*ps=-q+V*R>=0 still gives q<=V*R and the same origin bound.
    assert all(row[free.index(1)]>=0 for row in V),(pat,V)
   for ii,i in enumerate(free):
    assert ps[i].get((0,)*d,Q(0))==0
    for j in range(d):
     unit=tuple(int(k==j) for k in range(d))
     assert ps[i].get(unit,Q(0))==-A[ii][j]
   C=[sum(abs(c) for m,c in ps[i].items() if sum(m)>=2) for i in free]
   K=max(sum(abs(V[i][j])*C[j] for j in range(d)) for i in range(d))
   if not K:return 1
   E=1
   while Q(1,2**E)>=1/K:E+=1
  extra=[];etags=[]
  for row in V:
   p={}
   for c,j in zip(row,free):p=add(p,scale(ps[j],c))
   extra.append(p)
   v=row[free.index(1)] if relaxed and 1 in free else Q(0)
   etags.append('ge' if v>0 else 'le' if v<0 else 'eq')
  ps+=extra;tags+=etags
 inds=list(product(range(3),repeat=d));loc={a:i for i,a in enumerate(inds)};size=len(inds)
 Bs=[]
 for p in ps:
  row=[]
  for k in inds:
   b=Q(0)
   for m,c in p.items():
    if all(m[i]<=k[i] for i in range(d)):
     for i in range(d):c*=Q(comb(k[i],m[i]),comb(2,m[i]))
     b+=c
   row.append(b)
  Bs.append(row)
 den=lcm(*(b.denominator for row in Bs for b in row));Bs=[[int(b*den) for b in row] for row in Bs]
 triples=[]
 for axis in range(d):
  t=[]
  for a in inds:
   if a[axis]:continue
   b=list(a);b[axis]=1;c=list(a);c[axis]=2
   t.append((loc[a],loc[tuple(b)],loc[tuple(c)]))
  triples.append(t)
 stack=[(Bs,(0,)*d,(0,)*d)];nodes=0
 while stack:
  bs,ks,ds=stack.pop();nodes+=1
  if any((min(r)>0 or max(r)<0) if t=='eq' else min(r)>0 if t=='le' else max(r)<0 if t=='ge' else False for r,t in zip(bs,tags)):continue
  if E is not None and all(ds[i]>=E and ks[i]+1<=2**(ds[i]-E) for i in range(d)):continue
  assert nodes<=1000000 and max(ds)<=35, ('UNRESOLVED',pat,ks,ds)
  axis=min(range(d),key=lambda i:ds[i]);left=[];right=[]
  for row in bs:
   a=[0]*size;b=[0]*size
   for i,j,k in triples[axis]:
    u,v,w=row[i],row[j],row[k];mid=u+2*v+w
    a[i]=4*u;a[j]=2*(u+v);a[k]=mid
    b[i]=mid;b[j]=2*(v+w);b[k]=4*w
   left.append(a);right.append(b)
  nd=list(ds);nd[axis]+=1;lo=list(ks);hi=list(ks);lo[axis]*=2;hi[axis]=2*hi[axis]+1
  stack.extend([(right,tuple(hi),tuple(nd)),(left,tuple(lo),tuple(nd))])
 return nodes

if __name__=='__main__':
 total=sum(exclude(pat) for pat in product((0,1,2),repeat=4) if any(pat))
 if pair_premium==0 and pair_cost==100:assert total==(862 if uniform_k else 978),total
 scope='every K>=100, p=0' if uniform_k else f'K={pair_cost}, p={pair_premium}'
 print(f'EXACT RATIONAL PASS: {scope}; all 80 nonzero supports excluded; {total} nodes')
 roots=sum(exclude(pat,ROOT) for pat in product((0,1,2),repeat=4) if 1 in pat)
 if pair_premium==0 and pair_cost==100:assert roots==369,roots
 print(f'EXACT RATIONAL PASS: {scope}; all 65 sure-root patterns excluded; {roots} nodes')
