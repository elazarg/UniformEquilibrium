"""Auxiliary architecture/coverage audit at delta=1/10, not the UE producer.
Run from the repository root; requires SymPy and NumPy. --algebra-only skips
only the long stationary-cube census. No subdivision leaves are written.
The pinned frozen export supplies the complete case proofs and audit code.
"""
from pathlib import Path
from hashlib import sha256
import itertools
import sys
SOURCE=Path('math/exports/COMPLEX_SPECTRUM_PERIODIC_UNIFORM_EQUILIBRIUM.md')
PIN='9c3174c7576f1a066b7432db713052cf2259a42ab35a15b38910b22df1c41f38'
raw=SOURCE.read_bytes();assert sha256(raw).hexdigest()==PIN
text=raw.decode()
def block(heading):
 assert text.count(heading)==1
 start=text.index('```python\n',text.index(heading))+len('```python\n')
 return text[start:text.index('\n```',start)]
def module(code,label):
 ns={'__name__':label};exec(compile(code,str(SOURCE)+'::'+label,'exec'),ns);return ns
C=module(block('## Appendix C.'),'stationary_scope')
Dcode=block('## Appendix D.')
for old,new in [('ends=(s.S.Zero,s.Rational(1,1000))','ends=(s.Rational(1,10),s.Rational(1,10))'),
                ('ends=[s.S.Zero,s.Rational(1,1000)]','ends=[s.Rational(1,10),s.Rational(1,10)]')]:
 assert Dcode.count(old)==1;Dcode=Dcode.replace(old,new)
D=module(Dcode,'paired_raw_scope');s=C['s'];q=C['q'];I=range(4);delta=s.Rational(1,10)
z=C['table'](delta);H,F,g=C['fields'](z)
G=s.Matrix([[z[i,1<<j]for j in I]for i in I])
J=s.Matrix([[0 if i==j else z[i,(1<<i)|(1<<j)]for j in I]for i in I]);A=G-J
assert G.det()>0 and min(G.inv())>0 and A.det()>0 and min(A.inv())>0
K=max(sum(abs(v)for mon,v in f.terms()if sum(mon)>=2)for f in F)
L=max(sum(G.inv().row(i))for i in I)
assert K==s.Rational(135711,1000)and L==s.Rational(619418250,251185027)and K*L/512<1
for owner in I:
 other=next(i for i in I if G[i,owner]<0);assert J[other,owner]>0
for i,j in itertools.combinations(I,2):assert G[i,j]<0 or G[i,j]>J[i,j]>0
for S in itertools.combinations(I,3):
 i=next(i for i in S if(i^1)not in S);j,k=[h for h in S if h!=i]
 loss=-G[i,j]-G[i,k];passive=z[i,(1<<j)|(1<<k)]
 assert G[i,j]<0 and G[i,k]<0 and passive>=0 and(loss+passive)/512<loss
print('PASS exact origin exclusion and inverse-positive singleton cell',flush=True)
zd=D['table']();D['sure_faces'](zd)
# Frozen closed-face exhaustion uses only delta in[0,1] for sure owner0.
# Owners1,3 are unchanged. Recheck the sole sure2 candidate at delta1/10.
t=(15-s.sqrt(205))/20
point={q[0]:1/(2*(1-t)),q[1]:t,q[2]:1,q[3]:(6-5*t)/(7-5*t)}
value=s.expand(s.radsimp(g[2].subs(point)));b=value.coeff(s.sqrt(205));a=s.simplify(value-b*s.sqrt(205))
assert a>0 and b<0 and b*b*205>a*a
for owner,point in [(0,(1,s.Rational(7,107),0,s.Rational(1,2))),
                    (1,(1,1,1,0)),(3,(0,1,1,1))]:
 assert g[owner].subs(dict(zip(q,point)))<0
print('PASS all closed sure faces at delta1/10',flush=True)
D['raw_guards'](zd)
# Favorite matching is excluded by c=-1; the two crossing matchings require
# full closed-cube certificates. Their origin controls are checked internally.
assert all(A[i,i^1]==1 for i in I)
for mate in ((2,3,0,1),(3,2,1,0)):
 r=D['certify'](zd,mate)
 print('PASS crossing pair cube',mate,r['nodes'],len(r['leaves']),r['maxdepth'],flush=True)
if '--algebra-only' not in sys.argv:C['certify'](F+F,max_nodes=2000000,max_depth=120)
print('PASS requested exact coverage audits; original own levels=1',flush=True)
