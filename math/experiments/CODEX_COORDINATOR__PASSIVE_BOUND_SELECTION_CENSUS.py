"""Exact fixed-table stationary/sure-first exclusion by rational Bernstein boxes."""
import itertools
import sympy as s
R=s.Rational(-25);t=s.Rational(987);K=s.Rational(-1,4);eta=s.Rational(-3)
Z={1:[0,2,2,-1],2:[3,0,-2,-2],4:[-1,s.Rational(1,2),0,1],8:[3,-3,-1,0],3:[s.Rational(-1,100),-1,-10,-12],5:[s.Rational(-1,10),5,2+eta,s.Rational(-219,29)],6:[-12,-K,s.Rational(-1,10000),-6],9:[-20,3,-5,1],10:[2,-100,-1,10],12:[R,9,3,-100],7:[-20,6,-100,11],11:[-20,8,10,-10],13:[-20,-8,-100,t],14:[-8,11,2,1],15:[-5,-9,-100,s.Rational(21,2)]}
Z[14][0]=-1000
x=s.symbols('x0:4');gamma=s.Matrix([[Z[1<<j][i] for j in range(4)] for i in range(4)])
F=[];G=[];L=[]
for i in range(4):
 h=s.prod(1-x[j] for j in range(4) if i!=j);p=0;q=0
 for a in range(16):
  if a>>i&1:continue
  pr=s.prod(x[j] if a>>j&1 else 1-x[j] for j in range(4) if j!=i)
  p+=pr*(Z[a][i] if a else 0);q+=pr*Z[a|1<<i][i]
 li=min([-1]+[Z[a][i] for a in Z if not(a>>i&1)]);L.append(li)
 F.append(s.Poly(s.expand((1-h)*q-p),x));G.append(s.Poly(s.expand(q-p-h*li),x))
def bern(expr,free):
 p=s.Poly(expr,free);d=len(free);coeff=p.terms();out=[]
 assert all(max(a)<=2 for a,c in coeff)
 for k in itertools.product(range(3),repeat=d):
  out.append(sum(c*s.prod(s.binomial(ki,mi)/s.binomial(2,mi) for ki,mi in zip(k,m)) for m,c in coeff if all(mi<=ki for mi,ki in zip(m,k))))
 out=list(map(s.Rational,out));den=s.ilcm(*[c.q for c in out]) if len(out)>1 else out[0].q
 return tuple(int(c*den) for c in out)
def split(a,axis,d):
 step=3**(d-axis-1);left=list(a);right=list(a)
 for base in range(0,len(a),3*step):
  for j in range(step):
   ids=(base+j,base+j+step,base+j+2*step);v0,v1,v2=(a[k] for k in ids)
   for k,v,w in zip(ids,(4*v0,2*(v0+v1),v0+2*v1+v2),(v0+2*v1+v2,2*(v1+v2),4*v2)):left[k]=v;right[k]=w
 return tuple(left),tuple(right)
def rejects(coeff,sign):
 return min(coeff)>0 if sign<0 else max(coeff)<0 if sign>0 else min(coeff)>0 or max(coeff)<0
for mode,base in [('stationary',F),('sure',G)]:
 total=0;closed=0
 for pat in itertools.product(range(3),repeat=4):
  if not any(pat) or(mode=='sure' and 2 not in pat):continue
  freeidx=[i for i in range(4) if pat[i]==1];free=[x[i] for i in freeidx];d=len(free)
  # For p>-2: F2 >= q1(1-q3)[2+p(1-H2)]+q3 > 0 on this face.
  if mode=='stationary' and pat[0]==0 and pat[2]==1 and(pat[1] or pat[3]):closed+=1;continue
  if mode=='stationary' and 2 not in pat and d==1:closed+=1;continue
  sub={x[i]:int(pat[i]==2) for i in range(4) if pat[i]!=1}
  pp=[f.as_expr().subs(sub).expand() for f in base];signs=[v-1 for v in pat]
  if not free:
   assert any(rejects((p,),sg) for p,sg in zip(pp,signs)),(mode,pat,'PURE CANDIDATE');closed+=1;continue
  orig=None
  if d>=2:
   V=gamma.extract(freeidx,freeidx).inv()
   combos=list(V*s.Matrix([pp[i] for i in freeidx]));pp+=combos;signs+=[0]*d
   if mode=='stationary' and 2 not in pat:
    c=[]
    for i in freeidx:
     rem=s.Poly(pp[i]+sum(gamma[i,j]*x[j] for j in freeidx),free)
     assert all(sum(m)>=2 for m,v in rem.terms() if v)
     c.append(sum(abs(v) for m,v in rem.terms()))
    D=max(sum(abs(V[i,j])*c[j] for j in range(d)) for i in range(d))
    E=0
    while 2**E<=D:E+=1
    orig=E
  coeff=tuple(bern(p,free) for p in pp);stack=[(coeff,(0,)*d,(0,)*d)];nodes=0
  while stack:
   coeff,low,depth=stack.pop();nodes+=1
   if any(rejects(c,sg) for c,sg in zip(coeff,signs)):continue
   if orig is not None and all(dep>=orig and lo+1<=2**(dep-orig) for lo,dep in zip(low,depth)):continue
   if nodes>=200000 or max(depth)>200:
    print('UNRESOLVED',mode,pat,'nodes',nodes,'depth',depth,'low',low,flush=True);raise SystemExit(2)
   axis=min(range(d),key=lambda i:depth[i]);pairs=[split(c,axis,d) for c in coeff]
   nd=list(depth);nd[axis]+=1;ll=list(low);rr=list(low);ll[axis]*=2;rr[axis]=2*rr[axis]+1
   stack.append((tuple(p[1] for p in pairs),tuple(rr),tuple(nd)))
   stack.append((tuple(p[0] for p in pairs),tuple(ll),tuple(nd)))
  total+=nodes;closed+=1
 assert (closed,total)==((80,891) if mode=='stationary' else (65,256))
 print('PASS',mode,'patterns',closed,'nodes',total,'L',L,flush=True)
# Complete relaxed withdrawal duals: singleton coalition entries are indexed by bits.
def withdrawal(C,o,kind,A):
 left=-Z[A][o] if kind=='F' else Z[A|(1<<o)][o]-Z[A][o]
 lam=[];mu=[]
 for i in C:
  w=Z[A^(1<<i)][i]-Z[A][i] if A>>i&1 and A!=(1<<i) else 0
  lam.append(-Z[A][i] if kind=='F' else Z[A|(1<<i)][i]-Z[A][i])
  mu.append(max(w,0) if kind=='F' else w)
 return s.Matrix([left]+lam+mu)
duals={1:(3,[('J',1,1)]),2:(2,[('J',2,1)]),4:(0,[('J',4,1)]),8:(1,[('F',8,1)]),3:(3,[('J',1,1)]),5:(3,[('J',1,1)]),9:(1,[('F',8,1)]),6:(0,[('F',4,1)]),10:(2,[('J',8,1)]),12:(0,[('J',4,1)]),7:(3,[('J',1,1)]),11:(2,[('J',8,1)]),13:(1,[('F',1,1),('F',4,1),('F',8,2)]),14:(0,[('J',14,1)])}
for mask,(o,terms) in duals.items():
 C=[i for i in range(4) if mask>>i&1];v=s.zeros(1+2*len(C),1)
 for kind,A,n in terms:v+=n*withdrawal(C,o,kind,A)
 assert v[0]>0 and all(z<=0 for z in v[1:]),(mask,v)
assert len(duals)==14
# All-role raw return orientation screens.
roles=[]
for a,b,c,d in itertools.permutations(range(4)):
 if -gamma[a,c]>0 and gamma[c,a]>0 and gamma[a,d]>0 and -gamma[b,d]>0 and Z[(1<<c)|(1<<d)][c]>0:roles.append((a,b,c,d))
assert roles==[(0,1,2,3)]
macros=[]
for i,j in itertools.permutations(range(4),2):
 z=Z[(1<<i)|(1<<j)]
 if z[i]<0 and z[i]>gamma[i,j] and z[j]>0 and z[j]>gamma[j,i]:macros.append((i,j))
assert not macros
assert all(not(Z[(1<<i)|(1<<j)][i]>0 and Z[(1<<i)|(1<<j)][j]>0) for i,j in itertools.combinations(range(4),2))
# Three universal-weight contradictions, coefficientwise.
H=lambda A:s.Matrix(Z[A])
J=lambda A:s.Matrix([0 if A>>i&1 else Z[A|(1<<i)][i]-Z[A][i] for i in range(4)])
floor=lambda A:s.Matrix([Z[A|(1<<i)][i] for i in range(4)])
for v in (H(6)+H(2)+H(8),4*H(4)+H(2)-3*J(5),floor(3)+floor(4)):assert all(z<0 for z in v)
# The safe-positive graph has no nonempty proper predecessor-closed set.
edges={(j,i) for i in range(4) for j in range(4) if i!=j and gamma[i,j]>0 and Z[(1<<i)|(1<<j)][i]<=gamma[i,j]}
assert all(any((mask>>i&1) and not(mask>>j&1) for j,i in edges) for mask in range(1,15))
assert gamma.det()==s.Rational(35,2)
assert all(gamma.extract(C,C).det()!=0 for k in range(2,5) for C in itertools.combinations(range(4),k))
print('PASS fourteen withdrawal duals, all return-role/pair selectors, three weight duals, all proper marked sets, singleton determinants')
# A proper all-positive Nash crossing arbitrarily close to continuation zero.
eps=s.symbols('eps');odds=[0,20*eps,eps,eps/1000]
qn=[];pn=[]
for i in range(4):
 qi=0;pi=0
 for A in range(16):
  if A>>i&1:continue
  m=s.prod(odds[j] for j in range(4) if A>>j&1)
  qi+=m*Z[A|(1<<i)][i];pi+=m*(Z[A][i] if A else 0)
 qn.append(s.expand(qi));pn.append(s.expand(pi))
v=[0,-s.Rational(347,1000)*eps+eps**2/500,s.Rational(20001,500)*eps+3*eps**2/50,139*eps+140*eps**2]
assert all(s.expand(qn[i]-pn[i]-v[i])==0 for i in (1,2,3))
assert qn[1:]==[3*eps/20+11*eps**2/1000,eps/1000+eps**2/25,100*eps+20*eps**2]
assert pn[0]==s.Rational(59003,1000)*eps-s.Rational(47997,200)*eps**2-20*eps**3
assert qn[0]==-s.Rational(8,25)*eps-s.Rational(20021,50)*eps**2-eps**3/10
small=s.Rational(1,1000000)
assert all(f.subs(eps,small)>0 for f in qn[1:]+[pn[0]]) and qn[0].subs(eps,small)<0
assert v[1].subs(eps,small)<0 and sum(abs(f.subs(eps,small)) for f in map(s.sympify,v))<s.Rational(1,1000)
print('PASS exact near-zero proper Nash crossing and its strict margins')
