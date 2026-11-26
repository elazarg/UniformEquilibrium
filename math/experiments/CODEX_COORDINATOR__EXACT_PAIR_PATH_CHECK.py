"""Exact opposed-pair path calibration and complete prior-producer exclusions.

Run: python math/experiments/CODEX_COORDINATOR__EXACT_PAIR_PATH_CHECK.py
Requires SymPy; all decisions use rational arithmetic. Bit i denotes owner i.
The example has original own levels one. This is bounded evidence for the
literal table, not an all-behavior gap or a proof by numerical root search.
The general theorem and complete census interpretation are documented in
the accompanying mathematical packet and independent coverage review.
"""
import itertools
import sympy as s
rows={1:'0 2 5 -3',2:'3 0 -2 -2',4:'-1 1/2 0 1',8:'3 -3 -1 0',3:'-20 3 -10 -1',5:'-1/10 5 4 -1000',6:'-12 1/4 1 -6',9:'-1000 10 0 -4',10:'2 -100 -1 10',12:'-25 9 3 -100',7:'-1 33/5 -58/5 -1',11:'-5 11 -2 -2',13:'-10 10 -1 -1001',14:'-10000 11 2 1',15:'-20 11 -3 -2'}
Z={A:list(map(s.Rational,row.split())) for A,row in rows.items()}
assert Z[7][1]-Z[5][1]==s.Rational(8,5) and Z[3][2]-Z[7][2]==s.Rational(8,5)
assert max([0]+[Z[A][2] for A in Z if not A&4])==5
assert max([0]+[Z[A][3] for A in Z if not A&8])==1
assert all(Z[A][0]<=0 for A in Z if A&1)
assert Z[5][0]>Z[4][0] and Z[7][0]>Z[6][0]
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
  # For q0=0: Q2>=0 and P2=-2q1(1-q3)-q3<0 whenever q1+q3>0.
  if mode=='stationary' and pat[0]==0 and pat[2]==1 and(pat[1] or pat[3]):closed+=1;continue
  if mode=='stationary' and 2 not in pat and d==1:
   j=freeidx[0];lo=s.Rational(0);hi=s.Rational(1);impossible=False
   for i in range(4):
    if i==j:continue
    singleton=Z[1<<j][i];J=Z[(1<<i)|(1<<j)][i]
    if J>0:hi=min(hi,s.Rational(singleton)/J)
    elif J<0:lo=max(lo,s.Rational(singleton)/J)
    elif singleton<0:impossible=True
   assert impossible or lo>hi or hi<=0 or lo>=1,('SOLE ROOT',j,lo,hi)
   closed+=1;continue
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
 assert closed==(80 if mode=='stationary' else 65)
 print('PASS',mode,'patterns',closed,'nodes',total,'L',L,flush=True)
# All standard joint/solo-return roles, including the signed beta,e,f triple version.
roles=[]
for a,b,c,d in itertools.permutations(range(4)):
 if gamma[a,d]>0 and gamma[c,d]<0 and gamma[b,d]<0 and -Z[(1<<b)|(1<<d)][b]>-gamma[b,d] and Z[(1<<c)|(1<<d)][c]>0:roles.append((a,b,c,d))
assert roles==[(0,1,2,3)] and -Z[6][1]<0
assert not any(Z[(1<<i)|(1<<j)][i]<0 and Z[(1<<i)|(1<<j)][i]>gamma[i,j] and Z[(1<<i)|(1<<j)][j]>0 and Z[(1<<i)|(1<<j)][j]>gamma[j,i] for i,j in itertools.permutations(range(4),2))
assert [i for i in range(4) if all(Z[A][i]<=0 for A in Z if A>>i&1)]==[0]
for b in [1,2,3]:assert any(Z[(1<<b)|(1<<c)][b]>0 for c in [1,2,3] if c!=b)
# Exact all15 marked-Nash-invariance countercontrols in every neighborhood of0.
def endpoints(q,v):
 Q=[];C=[];U=[]
 for i in range(4):
  qi=ci=0
  for A in range(16):
   if A>>i&1:continue
   pr=s.prod(q[j] if A>>j&1 else 1-q[j] for j in range(4) if j!=i)
   qi+=pr*Z[A|1<<i][i];ci+=pr*(Z[A][i] if A else v[i])
  Q.append(qi);C.append(ci);U.append(q[i]*qi+(1-q[i])*ci)
 assert all((q[i]==0 or Q[i]>=C[i]) and(q[i]==1 or C[i]>=Q[i]) for i in range(4))
 return U
edges=sorted((j,i) for j in range(4) for i in range(4) if i!=j and gamma[i,j]>0 and Z[(1<<i)|(1<<j)][i]<=gamma[i,j])
eps=s.Rational(1,1000000)
for mask in range(1,15):
 j,i=next((j,i) for j,i in edges if mask>>i&1 and not(mask>>j&1))
 v=[0 if k in(i,j) else eps*(1+abs(gamma[k,j])+abs(Z[(1<<j)|(1<<k)][k])) for k in range(4)]
 U=endpoints([eps if k==j else 0 for k in range(4)],v)
 assert min(v[k] for k in range(4) if mask>>k&1)==0 and min(U[k] for k in range(4) if mask>>k&1)>0
v=[0,-eps/(4*(1-eps)),3*eps/(1-eps),2*eps]
U=endpoints([0,eps,eps,0],v)
assert min(v)<0 and min(U)>0
assert U==[2*eps-14*eps**2,eps/4,eps,eps-9*eps**2+2*eps**3]
print('PASS all return roles, all12 reset macros, passive-threshold anchor screen, and all15 marked-invariance controls')

# Independent legacy certificates, evaluated on the same literal table.
G=s.Matrix([[Z[1<<j][i] for j in range(4)] for i in range(4)])
def withdrawal(C,o,kind,A):
 left=-Z[A][o] if kind=='F' else Z[A|1<<o][o]-Z[A][o]
 lam=[];mu=[]
 for i in C:
  w=Z[A^(1<<i)][i]-Z[A][i] if A>>i&1 and A!=1<<i else 0
  lam.append(-Z[A][i] if kind=='F' else Z[A|1<<i][i]-Z[A][i])
  mu.append(max(w,0) if kind=='F' else w)
 return [left]+lam+mu
choices={1:(1,'J',1),2:(2,'J',2),4:(0,'J',4),8:(1,'F',8),3:(2,'J',2),5:(1,'J',1),9:(1,'J',1),6:(0,'F',4),10:(2,'J',8),12:(0,'J',4),7:(3,'F',1),11:(2,'J',8),13:(1,'J',1),14:(0,'J',14)}
for mask,(o,k,A) in choices.items():
 C=[i for i in range(4) if mask>>i&1];v=withdrawal(C,o,k,A)
 assert v[0]>0 and all(a<=0 for a in v[1:]),(mask,v)
H=lambda A:s.Matrix(Z[A])
J=lambda A:s.Matrix([0 if A>>i&1 else Z[A|1<<i][i]-Z[A][i] for i in range(4)])
K=lambda A:s.Matrix([Z[A|1<<i][i] for i in range(4)])
for got,want in [(H(6)+H(2)+H(8),[-6,-s.Rational(11,4),-2,-8]),(-J(6)-J(10)-J(12),[-19,-2,-3,-7]),(K(3)+K(4)+K(8),[-s.Rational(10201,10),-s.Rational(387,4),-s.Rational(43,5),-102])]:
 assert list(got)==want and all(a<0 for a in got)
eight=[];ten=[];reference=[]
ref=s.Matrix([[0,3,-1,3],[2,0,1,-3],[2,-2,0,-1],[-1,-2,1,0]])
for P in itertools.permutations(range(4)):
 g=lambda i,j:G[P[i],P[j]]
 if all(a>0 for a in [-g(0,2),-g(3,0),g(3,2),g(2,0),g(0,3),-g(2,3),-g(1,3),-g(3,1)]):eight.append(P)
 if all(a>0 for a in [-g(0,1),-g(0,2),g(0,3),-g(1,0),g(1,2),g(1,3),g(2,0),-g(2,3),-g(3,0),g(3,2)]):ten.append(P)
 scales=[g(i,(i+1)%4)/ref[i,(i+1)%4] for i in range(4)]
 if all(a>0 for a in scales) and all(g(i,j)==scales[i]*ref[i,j] for i in range(4) for j in range(4)):reference.append(P)
assert eight==[(0,1,2,3)] and ten==[(3,1,0,2)] and not reference
C=s.Rational(4,3);b=s.Rational(4,7);a=s.Rational(4,25);L=(1-a)*(1-b);A10=a*2+(1-a)*b/2
j=(3*C-A10*(3-C))/(3-L*(3-C));assert j==s.Rational(23,18)
assert b/2-(1-b)*j==-s.Rational(11,42)
assert G.det()==s.Rational(53,2)
assert all(G.extract(C,C).det()!=0 for k in range(2,5) for C in itertools.combinations(range(4),k))
positive=[]
for C in itertools.combinations(range(4),3):
 V=G.extract(C,C).inv();o=next(i for i in range(4) if i not in C)
 if all(v>=0 for v in V):
  positive.append(C);assert list(G.extract([o],C)*V)==[-s.Rational(23,24),s.Rational(1,8),-s.Rational(11,24)]
assert positive==[(0,2,3)]
assert G.inv()[1,2]<0 and G.inv()[0,2]>0
assert all(any(G[i,j]>0 for i in range(4) if i!=j) for j in range(4))
scalar=[(i,j) for i in range(4) for j in range(4) if i!=j and G[i,j]<0 and Z[(1<<i)|(1<<j)][i]>0]
assert scalar==[(2,1),(2,3),(3,1)]
pp=[C for C in itertools.combinations(range(4),2) if G[C[0],C[1]]>0 and G[C[1],C[0]]>0]
nn=[C for C in itertools.combinations(range(4),2) if G[C[0],C[1]]<0 and G[C[1],C[0]]<0]
assert pp==[(0,1)] and nn==[(1,3)]
assert sum(bool(G[1,j]*G[j,1]<0) for j in (0,2,3))==1
assert [Z[3][0]-G[0,1],Z[10][1]-G[1,3],Z[9][0]-G[0,3]]==[-23,-97,-1003]
assert Z[10][1]<0 and G[2,1]<0

positive_edges={(j,i) for i in range(4) for j in range(4) if i!=j and G[i,j]>0}
assert all(any(mask>>i&1 and not(mask>>j&1) for j,i in positive_edges) for mask in range(1,15))
flat=[i for i in range(4) if all(Z[A][i]<=0 for A in Z if A>>i&1)];assert flat==[0]
assert all(any(Z[(1<<i)|(1<<j)][i]>0 for j in (1,2,3) if i!=j) for i in (1,2,3))
assert all(Z[14][i]>0 for i in (1,2,3))
print('PASS 14 withdrawal duals; three all-weight duals; all singleton/reference permutations; inverse, circuit, anchor and threshold selectors')


# Four actual quiet increments, exact path tests, and boundary controls.
import itertools
import sympy as z
alpha,x,y,s,c,d0,d1,e0,e1,l,m,n=z.symbols('alpha x y s c d0 d1 e0 e1 l m n')
u00,u10,u01,u11=z.symbols('u00 u10 u01 u11')
A=s*x+d0*alpha;B=c*y+e0*alpha;C=s-d1*alpha;D=c-e1*alpha
phi=l*y+m*x+n*x*y
N=l*B*C+m*A*D+n*A*B-phi*C*D+alpha*(u00*C*D+u10*B*C+u01*A*D+u11*A*B)
r0=c*(d0+d1*x)*(m+n*y)+s*(e0+e1*y)*(l+n*x)+c*s*(u00+u10*y+u01*x+u11*x*y)
r1=n*d0*e0-m*d0*e1-l*d1*e0-d1*e1*(l*y+m*x+n*x*y)+u00*(-c*d1-s*e1)+u10*(s*e0-c*y*d1)+u01*(c*d0-s*x*e1)+u11*(c*y*d0+s*x*e0)
r2=u00*e1*d1-u10*e0*d1-u01*e1*d0+u11*e0*d0
R=z.expand(r0+r1*alpha+r2*alpha**2)
assert z.expand(N-alpha*R)==0
assert z.cancel(-s*A/(A+C)+s*x*C/(A+C)+alpha*(d0*C+d1*A)/(A+C))==0
assert z.cancel(c*B/(B+D)-c*y*D/(B+D)-alpha*(e0*D+e1*B)/(B+D))==0
assert z.Poly(R,x,y).degree(x)==z.Poly(R,x,y).degree(y)==1
assert z.Poly(R.coeff(x,1),alpha).degree()<=1
for key,weight in [(u00,C*D),(u10,B*C),(u01,A*D),(u11,A*B)]:
 assert z.expand(z.diff(R,key)-weight)==0
print('PASS exact factor, active gaps, four separate monotone increments')
def test(p,tau):
 p=z.Poly(z.expand(p),alpha);a,b,d=[p.nth(k) for k in range(3)]
 vals=[p.eval(0),p.eval(tau)]
 if d<0 and 0<-b/(2*d)<tau:vals.append(p.eval(-b/(2*d)))
 assert all(v<=0 for v in vals),(p,vals)
 return vals
base={s:z.Rational(1,4),c:3,l:12,m:-101,n:7}
X=z.Rational(5,3)
examples=[
 ('eight-fifths gains',{d0:1,d1:z.Rational(8,5),e0:1,e1:z.Rational(8,5),u00:-1,u10:-1,u01:-1,u11:-1},z.Rational(5,32)),
 ('scalar bound loss',{d0:1,d1:1,e0:1,e1:1,u00:150,u10:-1,u01:-1,u11:-1},z.Rational(1,4)),
 ('owner1 first',{d0:1,d1:1,e0:16,e1:16,u00:-1000,u10:-1000,u01:-1000,u11:-1000},z.Rational(3,16)),
]
for name,completion,tau in examples:
 rr=z.expand(R.subs(base|completion))
 values=[]
 for yy in (0,X):
  for k in (0,1):values.append(test(rr.coeff(x,k).subs(y,yy),tau))
 print('PASS',name,'unbounded negative continuation tests',values)
# Exact endpoint numerator in the owner1-first control, including negative g01.
endpoint1=-23*(z.Rational(1,4)-z.Rational(3,16))+11*(x/4+z.Rational(3,16))
assert z.expand(endpoint1)==11*x/4+z.Rational(5,8)
f=z.symbols('f')
# Frozen convexity criterion at (v1,v2,alpha)=(0,0,5/32).
k=z.Rational(8,5);tau=z.Rational(5,32)
old=-12*k+101*k+7-60*k*k+f*(z.Rational(1,4)*(k-1)+3*(k-1))-3*f*(k-1)**2*tau
assert z.expand(old)==-z.Rational(21,5)+z.Rational(57,32)*f
assert old.subs(f,1)==-z.Rational(387,160) and z.diff(old,f)>0
# A large positive 00 increment defeats every scalar bound, while exact path passes.
endpoint=-241-2*f
assert endpoint.subs(f,-150)==59
print('PASS exact separation from every admissible scalar/curvature bound')
# Arbitrary-core triple guards at the unchanged numerical core, W=5.
F=z.Rational(101)-7*X;G=100-X;Y=12*X/F;Bs=97-2*Y
Delta=Bs*3*F-z.Rational(1,4)*(4+3*X)*(12+7*Y)
assert all(a>0 for a in [F,G,Bs,Delta,190,190+58*X])
print('PASS inherited triple guards',F,G,Y,Bs,Delta)

# Interior concave vertices must be tested even when both endpoints pass.
assert test(-(alpha-z.Rational(1,2))**2,z.Integer(1))==[-z.Rational(1,4),-z.Rational(1,4),0]
try:
 test(z.Rational(1,10)-(alpha-z.Rational(1,2))**2,z.Integer(1))
except AssertionError:
 pass
else:
 raise AssertionError('A positive interior vertex was missed')
print('PASS interior-vertex maximum controls')
