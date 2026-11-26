"""Exact Bernstein stationary/sure support screen for one literal completion."""
import itertools
import sympy as s
rows={1:'0 -2 2 2',2:'5 0 -1 -1',3:'-12 -6 -3 10',4:'-1 1 0 -1',5:'-15/4 0 15/2 0',6:'-10 -3 -5 -3',7:'-30 30 30 30',8:'-1 1 -1 0',9:'0 -3 10 13/2',10:'3 -2 0 -4/5',11:'-30 10 30 -1000',12:'-3 10 -3 0',13:'-3 -3 -3 0',14:'-3 10 3 3',15:'3 -30 -30 -30'}
Z={A:list(map(s.Rational,row.split())) for A,row in rows.items()}
x=s.symbols('x0:4');gamma=s.Matrix([[Z[1<<j][i] for j in range(4)] for i in range(4)])
F=[];G=[];L=[]
for i in range(4):
 h=s.prod(1-x[j] for j in range(4) if j!=i);p=q=0
 for a in range(16):
  if a>>i&1:continue
  pr=s.prod(x[j] if a>>j&1 else 1-x[j] for j in range(4) if j!=i)
  p+=pr*(Z[a][i] if a else 0);q+=pr*Z[a|1<<i][i]
 li=min([-1]+[Z[a][i] for a in Z if not(a>>i&1)]);L.append(li)
 F.append(s.Poly(s.expand((1-h)*q-p),x));G.append(s.Poly(s.expand(q-p-h*li),x))
def bern(expr,free):
 p=s.Poly(expr,free);d=len(free);out=[]
 assert all(max(a)<=2 for a,c in p.terms())
 for k in itertools.product(range(3),repeat=d):
  out.append(sum(c*s.prod(s.binomial(ki,mi)/s.binomial(2,mi) for ki,mi in zip(k,m)) for m,c in p.terms() if all(mi<=ki for mi,ki in zip(m,k))))
 out=list(map(s.Rational,out));den=s.ilcm(*[c.q for c in out]) if len(out)>1 else out[0].q
 return tuple(int(c*den) for c in out)
def split(a,axis,d):
 step=3**(d-axis-1);left=list(a);right=list(a)
 for base in range(0,len(a),3*step):
  for j in range(step):
   ids=(base+j,base+j+step,base+j+2*step);v0,v1,v2=(a[k] for k in ids)
   for k,v,w in zip(ids,(4*v0,2*(v0+v1),v0+2*v1+v2),(v0+2*v1+v2,2*(v1+v2),4*v2)):left[k]=v;right[k]=w
 return tuple(left),tuple(right)
def rejects(coeff,sign):return min(coeff)>0 if sign<0 else max(coeff)<0 if sign>0 else min(coeff)>0 or max(coeff)<0
if __name__=='__main__':
 for mode,base in [('stationary',F),('sure',G)]:
  total=closed=0
  pats=list(itertools.product(range(3),repeat=4));pats.sort(key=lambda p:sum(v==1 for v in p))
  for pat in pats:
   if not any(pat) or(mode=='sure' and 2 not in pat):continue
   freeidx=[i for i in range(4) if pat[i]==1];free=[x[i] for i in freeidx];d=len(free)
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
    pp+=list(V*s.Matrix([pp[i] for i in freeidx]));signs+=[0]*d
    if mode=='stationary' and 2 not in pat:
     c=[]
     for i in freeidx:
      rem=s.Poly(pp[i]+sum(gamma[i,j]*x[j] for j in freeidx),free)
      assert all(sum(m)>=2 for m,v in rem.terms() if v)
      c.append(sum(abs(v) for m,v in rem.terms()))
     D=max(sum(abs(V[i,j])*c[j] for j in range(d)) for i in range(d));E=0
     while 2**E<=D:E+=1
     orig=E
   coeff=tuple(bern(p,free) for p in pp);stack=[(coeff,(0,)*d,(0,)*d)];nodes=0
   while stack:
    coeff,low,depth=stack.pop();nodes+=1
    if any(rejects(c,sg) for c,sg in zip(coeff,signs)):continue
    if orig is not None and all(dep>=orig and lo+1<=2**(dep-orig) for lo,dep in zip(low,depth)):continue
    if nodes>=100000 or max(depth)>100:
     print('UNRESOLVED',mode,pat,'nodes',nodes,'depth',depth,'low',low,flush=True);raise SystemExit(2)
    axis=min(range(d),key=lambda i:depth[i]);pairs=[split(c,axis,d) for c in coeff]
    nd=list(depth);nd[axis]+=1;ll=list(low);rr=list(low);ll[axis]*=2;rr[axis]=2*rr[axis]+1
    stack.append((tuple(p[1] for p in pairs),tuple(rr),tuple(nd)))
    stack.append((tuple(p[0] for p in pairs),tuple(ll),tuple(nd)))
   total+=nodes;closed+=1
  assert closed==(80 if mode=='stationary' else 65)
  print('PASS',mode,'patterns',closed,'nodes',total,'L',L,flush=True)

 # Exact absorbing child Nash profiles: play q once, then all Never.
 # Every profile has a sure owner; if the sole sure owner deviates Continue,
 # the normalized optimal continuation is 0 (original own reward is 1).
 def endpoints(q):
  Q=[];P=[]
  for i in range(4):
   qi=pi=0
   for A in range(16):
    if A>>i&1:continue
    pr=s.prod(q[j] if A>>j&1 else 1-q[j] for j in range(4) if j!=i)
    qi+=pr*Z[A|1<<i][i];pi+=pr*(Z[A][i] if A else 0)
   Q.append(qi);P.append(pi)
  return Q,P
 child_choices={1:(1,2),2:(2,3),3:(1,2),4:(4,3),5:(4,3),6:(2,3),7:(2,3),8:(8,0),9:(9,1),10:(8,0),12:(8,0),13:(9,1),14:(8,0)}
 child_gains={}
 for C in range(1,15):
  if C==11:q=[s.Integer(1),s.Rational(9,2029),s.Integer(0),s.Rational(4,17)];o=2
  else:
   sure,o=child_choices[C];assert sure&C==sure
   q=[s.Integer(bool(sure>>i&1)) for i in range(4)]
  assert not(C>>o&1) and any(q[i]==1 for i in range(4))
  Q,P=endpoints(q)
  assert all((q[i]==0 or Q[i]>=P[i]) and (q[i]==1 or P[i]>=Q[i]) for i in range(4) if C>>i&1)
  assert Q[o]>P[o];child_gains[C]=Q[o]-P[o]
 assert child_gains[11]==s.Rational(41091,34493)
 print('PASS all14 intrinsic child quiet-lift counterprofiles; exceptional gain',child_gains[11])

 # Whole-weight duals. Every vector has a strict common sign, so these
 # exclude all nonzero nonnegative weights, not merely selected weights.
 H=lambda A:s.Matrix(Z[A])
 Jin=lambda A:s.Matrix([0 if A>>i&1 else Z[A|1<<i][i]-Z[A][i] for i in range(4)])
 K=lambda A:s.Matrix([Z[A|1<<i][i] for i in range(4)])
 duals=[(H(6),[-10,-3,-5,-3]),(Jin(1)+Jin(5)+Jin(8),[1,23,s.Rational(7,2),s.Rational(9,2)]),(20*K(13)+K(3),[-72,-606,-30,-1000])]
 for got,want in duals:assert list(got)==want
 assert all(v<0 for v in duals[0][0]) and all(v>0 for v in duals[1][0]) and all(v<0 for v in duals[2][0])
 assert list(K(14))==[3,10,3,3]  # excludes every nonzero upper-floor weight
 assert not any(all(Z[A][i]<=0 for A in Z if A>>i&1) for i in range(4))

 # Complete finite role choices used by the named return and pair producers.
 J=s.Matrix([[0 if i==j else Z[(1<<i)|(1<<j)][i] for j in range(4)] for i in range(4)])
 eight=[];ten=[];relaxed=[]
 for p in itertools.permutations(range(4)):
  g=lambda i,j:gamma[p[i],p[j]]
  if all(v>0 for v in [-g(0,2),-g(3,0),g(3,2),g(2,0),g(0,3),-g(2,3),-g(1,3),-g(3,1)]):eight.append(p)
  if all(v>0 for v in [-g(0,1),-g(0,2),g(0,3),-g(1,0),g(1,2),g(1,3),g(2,0),-g(2,3),-g(3,0),g(3,2)]):ten.append(p)
  if all(v>0 for v in [-g(0,2),g(2,0),g(0,3),-g(1,3),J[p[2],p[3]]]):relaxed.append(p)
 assert eight==[(1,2,0,3),(1,3,0,2)] and all(J[p[2],p[3]]<=0 for p in eight)
 assert not ten and not relaxed
 assert not any(J[i,j]<0 and J[i,j]>gamma[i,j] and J[j,i]>0 and J[j,i]>gamma[j,i] for i,j in itertools.permutations(range(4),2))
 assert not any(gamma[i,j]<0 and J[i,j]>0 for i,j in itertools.permutations(range(4),2))
 assert not any(gamma[i,j]>0 and gamma[j,i]>0 for i,j in itertools.combinations(range(4),2))
 partitions=[[(0,1),(2,3)],[(0,2),(1,3)],[(0,3),(1,2)]]
 for pairs in partitions:
  ordered=[(i,j) for a,b in pairs for i,j in [(a,b),(b,a)]]
  assert any(J[i,j]-gamma[i,j]<=0 for i,j in ordered)
  assert any(J[i,j]<0 for i,j in ordered)
 assert gamma.det()==6 and all(v>0 for v in gamma.inv())
 assert all(gamma.extract(C,C).det()!=0 for k in range(2,5) for C in itertools.combinations(range(4),k))
 assert all(any(gamma[i,j]<0 for i in range(4)) for j in range(4))
 positive=[]
 for C in itertools.combinations(range(4),3):
  V=gamma.extract(C,C).inv();o=next(i for i in range(4) if i not in C)
  if all(v>=0 for v in V):
   positive.append(C);assert all(v<0 for v in gamma.extract([o],C)*V)
 assert positive==[(0,1,2),(0,1,3)]
 print('PASS whole-weight duals, all role/partition choices, and exact inverse/principal screens')

 # Global marked Nash invariance: three exact real-continuation controls.
 # These are NOT asserted to be actual strategic continuations or local controls.
 controls=[('0 7/10 3/10 17/20','0 -131/7 19 724/105'),
           ('3/20 1/200 7/10 1/5',None),('7/10 1/200 0 3/100',None)]
 covered=set()
 for qtext,utext in controls:
  q=list(map(s.Rational,qtext.split()));Q,P=endpoints(q)
  H=[s.prod(1-q[j] for j in range(4) if j!=i) for i in range(4)]
  u=list(map(s.Rational,utext.split())) if utext else [(Q[i]-P[i])/H[i] for i in range(4)]
  C=[P[i]+H[i]*u[i] for i in range(4)]
  assert all((q[i]==0 or Q[i]>=C[i]) and(q[i]==1 or C[i]>=Q[i]) for i in range(4))
  U=[q[i]*Q[i]+(1-q[i])*C[i] for i in range(4)]
  assert all(min([0]+[Z[A][i] for A in Z])<=u[i]<=max([0]+[Z[A][i] for A in Z]) for i in range(4))
  for mask in range(1,16):
   ids=[i for i in range(4) if mask>>i&1]
   if min(u[i] for i in ids)<=0 and min(U[i] for i in ids)>0:covered.add(mask)
 assert covered==set(range(1,16))
 print('PASS all15 marked-invariance countercontrols inside playerwise reward boxes (no actual/local claim)')

 # Every merged response quotient would require proportional F rows in
 # each block. A nonzero coefficient minor excludes all constant row scales.
 def partitions(prefix=(0,)):
  if len(prefix)==4:yield prefix;return
  for b in range(max(prefix)+2):yield from partitions(prefix+(b,))
 parts=list(partitions());assert len(parts)==15 and len(set(parts))==15
 checked=0
 for part in parts:
  if part==(0,1,2,3):continue
  y=s.symbols('y:'+str(max(part)+1));sub=dict(zip(x,[y[k] for k in part]))
  pol=[s.Poly(f.as_expr().subs(sub),y) for f in F];found=False
  for i,j in itertools.combinations(range(4),2):
   if part[i]!=part[j]:continue
   mon=sorted(set(pol[i].monoms())|set(pol[j].monoms()))
   if any(pol[i].coeff_monomial(a)*pol[j].coeff_monomial(b)!=pol[i].coeff_monomial(b)*pol[j].coeff_monomial(a) for a,b in itertools.combinations(mon,2)):found=True;break
  assert found,('unexcluded quotient',part)
  checked+=1
 assert checked==14
 print('PASS all14 merged response-quotient partitions, including constant positive row scalings')

 # Weak signs enlarge the named scalar/reset/core/negative-value criteria,
 # so a strict failure in every role also excludes their reward closures.
 minima={name:[] for name in ('scalar','reset','core','negative')};triples=[]
 for role in itertools.permutations(range(4)):
  g=lambda i,j:gamma[role[i],role[j]];j=lambda i,k:J[role[i],role[k]]
  z=lambda i,*owners:Z[sum(1<<role[a] for a in owners)][role[i]]
  tests={'scalar':[j(0,2),-j(2,0),-g(0,2),g(2,0),j(2,1),-g(3,1),-g(3,0),-g(1,3),j(2,1)-g(2,1)],
   'reset':[g(0,3),-g(3,0),-j(0,3),j(3,0),-j(0,2),j(0,2)-g(0,2),j(2,0),j(2,0)-g(2,0)],
   'core':[-g(0,2),g(3,2),g(2,0),g(0,3),-g(2,3),-g(1,3),g(1,3)-j(1,3),j(2,3),j(0,2)-g(0,2),j(2,0)-g(2,0),g(0,3)-j(0,3)],
   'negative':[-g(0,2),-g(3,0),g(3,2),g(2,0),g(0,3),-g(2,3),-g(1,3),-g(3,1),g(1,3)-j(1,3),j(2,3),j(3,1),g(3,2)-j(3,2),j(0,2)-g(0,2),j(2,0)-g(2,0)]}
  for name,values in tests.items():assert min(values)<0;minima[name].append(min(values))
  if min(g(0,3),-g(2,3),-g(1,3),g(1,3)-j(1,3),j(2,3),g(0,3)-j(0,3))>=0:
   d,e=-g(3,0),g(3,2);a3,v,w,t3=j(3,0),j(3,2),z(3,0,2),z(3,0,2,3);omega=w+d-e
   J0,J1=e*a3+d*v,e*(t3-a3)-(omega+e)*v;assert J1!=0
   b=-J0/J1;D=d-omega*b;assert D!=0;rate=e*b/D;triples.append(role)
   if role==(1,0,3,2):assert b==s.Rational(2,5) and D==s.Rational(1,5) and rate==-2
   else:
    assert role==(1,2,0,3)
    C=b*(-g(0,2)+j(0,2))/(1-b)
    a0=j(0,3)-g(0,3)+b*(z(0,0,2,3)-z(0,2,3))/(1-b)
    assert C==-s.Rational(14,1475) and a0==-s.Rational(8759,2950)
 assert {name:max(values) for name,values in minima.items()}=={'scalar':-2,'reset':-2,'core':-s.Rational(4,5),'negative':-3}
 assert triples==[(1,0,3,2),(1,2,0,3)]
 print('PASS all weak/closure scalar, reset, core, negative-value and general three-owner-return roles')

 # Coefficients at the SAME guarded actual three-cycle completion.
 r=s.symbols('r');w=gamma.inv().T*s.ones(4,1);Cs=[]
 for i in (1,2,3):
  lam=1-gamma[i,0]/J[i,0];A=gamma[0,i]*lam+J[0,i]*(1-lam)
  K=s.Matrix([0 if j in (0,i) else -gamma[j,0]+lam*gamma[j,i]+(1-lam)*Z[1|1<<i][j] for j in range(4)])
  Cs.append(s.factor(A-r*(w.T*K)[0]))
 expected=[(51*r-4)/6,-(287*r+78)/45,-(133*r+9)/13]
 assert all(s.expand(a-b)==0 for a,b in zip(Cs,expected))
 print('PASS fixed-r coefficients',Cs,'all negative for 0 <= r < 4/51')
