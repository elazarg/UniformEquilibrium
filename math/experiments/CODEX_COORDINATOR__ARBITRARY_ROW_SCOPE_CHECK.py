"""Supplementary raw-selector audit for the arbitrary-row stationary theorem.
Run from any directory with Python and SymPy. The frozen packet supplies
its exact raw table; no generated subdivision payload is saved.
"""
from pathlib import Path
import hashlib
packet=Path(__file__).resolve().parents[1]/'exports/DOMINATED_ROW_ARBITRARY_ROW_STATIONARY_UNIFORM_EQUILIBRIUM.md'
assert hashlib.sha256(packet.read_bytes()).hexdigest()=='f72f6182367c715845eff7ed630cffedc6abcde5ebbee9cc15cf9317d9c45a6e'
source=packet.read_text().split('```python\n',1)[1].split('\n```',1)[0]
exec(compile(source.split('# Analytic sure0 strip')[0],str(packet),'exec'))
# Scope formulas use the same raw table; no strategic data are inputs.
J=s.Matrix(4,4,lambda i,j:0 if i==j else Z[i,(1<<i)|(1<<j)])
G=A+J;adj=G.adjugate();det=s.factor(G.det());L=s.symbols('L',nonnegative=True)
assert s.factor(det-(4799250*d*e-18361800*d-275427000*e+515204117)/500000000)==0
E=(515204117-18361800*d)/(275427000-4799250*d)
assert s.factor(s.diff(E,d))==-s.Rational(14182398519,250)/(711*d-40804)**2
assert 0<E.subs(d,12)<E.subs(d,0)<2
# All fourteen security-child duals remain global in both parameters.
for mask in range(1,15):
 C=[i for i in I if mask>>i&1]
 if len(C)==1:
  i=C[0];h={0:3,1:2,2:0,3:1}[i];S=mask
 elif len(C)==2:
  h={3:2,5:3,9:1,6:0,10:2,12:1}[mask]
  S={3:2,12:4}.get(mask,mask)
 elif mask==14:
  assert -10*Z[0,6]-Z[0,4]==s.Rational(3,5)
  assert [-10*Z[i,6]-Z[i,4] for i in C]==[-s.Rational(3,20),-s.Rational(27,5),-s.Rational(1101,100)]
  continue
 else:h,S={7:(3,5),11:(2,10),13:(1,9)}[mask]
 lhs=Z[h,S|(1<<h)]-Z[h,S]
 advance=[Z[i,S|(1<<i)]-Z[i,S] for i in C]
 withdrawal=[0 if not S>>i&1 or S==1<<i else Z[i,S^(1<<i)]-Z[i,S] for i in C]
 assert lhs.is_positive and not lhs.has(d,e)
 assert all(all(t<=0 for t in s.Poly(v,d,e).coeffs()) for v in advance+withdrawal)
print('PASS all14 literal child duals on the entire closed parameter quadrant')

# Full cone-selection obstruction, matching02|13.
row=[s.factor(e*adj[1,j]-adj[0,j]-adj[2,j]) for j in I]
expected=[-(39600*d*e+11244835*e+24408)/10000000,
 3*(7425*d*e+4580350*e-8640771)/25000000,
 3*(78319*e-273912)/20000000,
 -(53325*d*e-181800*d-3060300*e+12038008)/5000000]
assert all(s.factor(a-b)==0 for a,b in zip(row,expected))
m1=s.factor(8640771-(7425*d+4580350)*E)
assert s.factor(m1-101*(27*d+14)*(1999800*d+568216603)/(270*(40804-711*d)))==0
m3=s.factor(12038008-181800*d+(53325*d-3060300)*E)
assert s.factor(m3-(1999800*d+568216603)/90)==0
assert 273912-78319*E.subs(d,0)>0
assert 53325*12-3060300<0 and 40804-711*12>0
# Every row entry is negative when0<=d<=12 and0<=e<E(d).
# The other crossing matching has incompatible raw cone caps.
assert -A[0,3]==s.Rational(1,100) and Z[0,5]==s.Rational(27,5)
assert -A[1,2]==s.Rational(3,2) and Z[1,11]==1
assert Z[3,13]==1 and -A[3,1]==e
print('PASS exact separating covector for every finite invariant cone and all pairings')

# Entire inverse-corner selection obstruction: determinant decreases from its
# (0,0) maximum, while these two needed adjugate entries increase.
assert s.Rational(63,1000)*adj[3,3].subs(d,0)-det.subs({d:0,e:0})/768==s.Rational(364417003,384000000000)>0
assert s.Rational(27,5)*adj[0,0].subs(e,0)-det.subs({d:0,e:0})/768==s.Rational(4511202283,384000000000)>0

# Triple spectra: no positive real mode in the open parameter quadrant.
triples=[((0,1,2),s.Rational(18,5),3*d/2),
 ((0,1,3),s.Rational(7,250),e/100),
 ((0,2,3),s.Rational(21,50),d/100),
 ((1,2,3),s.Rational(6,25),3*e/2)]
for S,tripleH,tripleK in triples:
 target=(L+s.Rational(1,100))*(tripleH*(L-s.Rational(9,10))**2+tripleK*(L-s.Rational(1,10))**2)
 assert s.factor((L*A.extract(S,S)+J.extract(S,S)).det()-target)==0
 assert s.factor(A.extract(S,S).det()-tripleH-tripleK)==0
print('PASS all triple spectral factors and marked-orientation signs')

# Fixed calibration inside the arbitrary-row class. Grand penalty never enters
# the following proper-coalition witnesses.
zz={key:value.subs({d:s.Rational(8,5),e:s.Rational(1,2)}) for key,value in Z.items()}
gg=G.subs({d:s.Rational(8,5),e:s.Rational(1,2)})
assert all(v>0 for v in gg.inv())
for i,j in itertools.combinations(I,2):
 outside=[k for k in I if k not in (i,j)]
 assert any(zz[h,mask|(1<<h)]-zz[h,mask]<0
  for h in (i,j) for mask in range(1,16)
  if all(not(mask>>k&1) for k in I if k not in outside))
for owner,passive in itertools.permutations(I,2):
 outside=[k for k in I if k not in (owner,passive)]
 masks=[sum(1<<k for p,k in enumerate(outside) if bits>>p&1) for bits in range(4)]
 lowerfails=any(zz[owner,B]>zz[owner,A|(1<<owner)] for A in masks for B in masks if B)
 # Singleton or empty outsider masks keep every witness a proper coalition.
 joinfails=any(zz[passive,T|(1<<owner)|(1<<passive)]>zz[passive,T|(1<<owner)]
  for T in masks if T.bit_count()<=1)
 assert lowerfails or joinfails
assert min(zz[0,mask] for mask in range(1,16) if mask&1)>=0
assert zz[0,1<<2]==-s.Rational(3,5)
print('PASS every guarded-crossed pair, every one-sided weak-unit role, and raw face-range obstruction')


# Complete repeated-pair fixed-tube selection audit.
Z={key:value.subs({d:R(8,5),e:R(1,2)})for key,value in Z.items()}
y=R(12,25);h=y+R(1,20000);tc=R(3,5)*h-R(51233,500000)+(h-R(49351,100000))**2/2
seen=0
for a in itertools.permutations(range(4)):
 if not all(Z[a[i],1<<a[i^1]]>0 for i in range(4)):continue
 seen+=1
 z=lambda i,js:Z[a[i],sum(1<<a[j]for j in set(js))]
 G=[[z(i,[j])for j in range(4)]for i in range(4)]
 J=[[z(i,[i,j])for j in range(4)]for i in range(4)]
 beta={j:(J[3-j][j]-G[3-j][j])/J[3-j][j]for j in (0,3)}
 D=(1+beta[0])*(1+beta[3]);p=[J[i][3-i]/(1+beta[3-i])if i in(0,3)else J[i][3-i]for i in range(4)]
 P=[z(i,[1,2]if i in(0,3)else[0,3])for i in range(4)]
 Pc=[P[i]if i in(0,3)else((1+beta[0]*beta[3])*P[i]+beta[3]*G[i][0]+beta[0]*G[i][3])/D for i in range(4)]
 guards=[G[0][1]>=p[0],G[0][2]<=P[0]<=G[0][1],G[3][2]>=p[3],G[3][1]<=P[3]<=G[3][2],G[2][0]<=Pc[2]<=G[2][3],G[2][3]>=p[2]]
 if not all(guards):print(a,'fails M0');continue
 c=[p[i]-G[i][3-i]for i in range(4)]
 rejected=False
 for side in(-1,1):
  t=tc+side*R(1,8000);H=(1-y)*(1-t)
  rc={i:G[i][1]*y*(1-t)+G[i][2]*t*(1-y)+P[i]*y*t for i in(0,3)}
  if any(v<=0 for v in rc.values()):print(a,'fails positive passive corner');rejected=True;break
  def response(i):
   assert c[i]>p[i]>0
   lo=R(0);hi=R(1)
   for _ in range(40):
    mid=(lo+hi)/2
    if c[i]*mid-(1-mid)*(p[i]*H*mid+rc[i])<0:lo=mid
    else:hi=mid
   return(lo,hi)
  def g2(x,z):return G[2][0]*x*(1-z)+G[2][3]*z*(1-x)+Pc[2]*x*z+p[2]*y*(1-x)*(1-z)-c[2]*y/(1-y)
  vals=[g2(x,z)for x in response(3)for z in response(0)]
  if side==-1 and max(vals)<-R(4,5):print(a,'G2 at lower boundary < -4/5');rejected=True;break
  if side==1 and min(vals)>R(1,10):print(a,'G2 at upper boundary > 1/10');rejected=True;break
 assert rejected,a
assert seen==8
print('All eight role assignments rejected; row scales cancel all tests. PASS')
