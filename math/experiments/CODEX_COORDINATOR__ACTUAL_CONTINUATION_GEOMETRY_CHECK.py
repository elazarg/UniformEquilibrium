"""Exact actual zero-debt positive-Never Nash-word trap; no numerical root census."""
from fractions import Fraction as F
from itertools import product
import sympy as S
Z={2:[100,0,-2,-2],4:[-3,F(1,2),0,1],8:[100,-3,-1,0],6:[-3,F(1,4),1,-6],10:[100,-100,-1,10],12:[-3,9,3,-100],14:[-3,11,2,1]}
gamma=[0,F(-194,3599),F(13203,7198),F(6)]
for A in range(1,16,2):Z[A]=[0]+[-1 if A>>i&1 else gamma[i] for i in range(1,4)]
assert all(Z[1<<i][i]==0 for i in range(4))
assert all(Z[A][0]<=0 for A in Z if A&1)
assert max(Z[A][2] for A in Z if not A&4)==F(13203,7198)<10
# 1,2 label the first two decision periods (physical natural times0,1).
# No earlier deadline is available. 99 denotes Never. There are only two finite opponent dates,
# so deadline3 represents every later finite deadline; native own rewards0.
laws=[{2:F(1,2),99:F(1,2)},{1:F(1,5),99:F(4,5)},{99:F(1)},{1:F(1,3600),99:F(3599,3600)}]
def payoff(ls):
 u=[F(0)]*4
 for ts in product(*(list(l) for l in ls)):
  pr=S.prod(ls[i][ts[i]] for i in range(4));t=min(ts)
  if t==99:continue
  A=sum(1<<i for i in range(4) if ts[i]==t)
  for i in range(4):u[i]+=pr*Z[A][i]
 return u
v=[F(901,45),F(-1,36),F(1,3),F(2)]
assert payoff(laws)==v
for i in range(4):
 vals=[]
 for t in [1,2,3,99]:
  ls=laws.copy();ls[i]={t:F(1)};vals.append(payoff(ls)[i])
 assert max(vals)==v[i] and vals[-1]==v[i],(i,vals)
assert S.prod(l[99] for l in laws)==F(3599,9000)
def ends(q,w):
 Q=[];C=[]
 for i in range(4):
  qi=ci=0
  for A in range(16):
   if A>>i&1:continue
   pr=S.prod(q[j] if A>>j&1 else 1-q[j] for j in range(4) if j!=i)
   qi+=pr*Z[A|1<<i][i];ci+=pr*(Z[A][i] if A else w[i])
  Q.append(qi);C.append(ci)
 return Q,C
for q,w,want in [([F(1,2),0,0,0],[0]*4,[0,F(-97,3599),F(13203,14396),3]),([0,F(1,5),0,F(1,3600)],[0,F(-97,3599),F(13203,14396),3],v),([0,F(1,10),F(1,10),0],v,[F(12459,500),F(1,40),F(1,10),F(147,100)])]:
 Q,C=ends(q,w)
 assert all((q[i]==0 or Q[i]>=C[i]) and(q[i]==1 or C[i]>=Q[i]) for i in range(4))
 assert [q[i]*Q[i]+(1-q[i])*C[i] for i in range(4)]==want
x=S.symbols('x0:4');w=S.symbols('w0:4');Q,C=ends(x,w)
core=[S.expand((Q[i]-C[i]).subs(x[0],0)) for i in range(4)]
for i in range(1,4):assert S.expand(Q[i]-C[i]-(1-x[0])*core[i]+(1+gamma[i])*x[0])==0
assert S.expand(C[0]-((1-x[2])*(100-(100-w[0])*(1-x[1])*(1-x[3]))-3*x[2]))==0
assert S.expand(core[1]-((1-x[3])*(-x[2]/4-w[1]*(1-x[2]))+x[3]*(-97+99*x[2])))==0
assert S.expand(core[2]-(3*x[1]+4*(1-x[1])*x[3]-(1-x[1])*(1-x[3])*w[2]))==0
assert S.expand(core[3].subs(x[2],0)-(12*x[1]-w[3]*(1-x[1])))==0
assert S.expand(core[3].subs(x[2],1)-(-101*(1-x[1])+7*x[1]))==0
print('PASS: actual U=B=e, positive Never, both Nash prefixes, positive crossing, and complete support-proof identities')

# Exact reselection curve; all domain sign claims are proved in the companion note.
r=S.symbols('r',positive=True);D=(r+2)*(2*r+3599)
q=[0,r/(r+2),0,2*r/(3599+2*r)];tail=[r*g for g in gamma]
Q,C=ends(q,tail)
curve=[100*(1-7198/D),-200*r/(3599+2*r),r*(6001-2*r)/D,10*r/(r+2)]
assert all(S.cancel(q[i]*Q[i]+(1-q[i])*C[i]-curve[i])==0 for i in range(4))
assert S.cancel(Q[1]-C[1])==S.cancel(Q[3]-C[3])==0
assert S.cancel(C[2]-Q[2]-2*r*(1195-3*r)/D)==0
nu=7198*(1-r)/D
assert S.cancel(S.diff(nu,r)-7198*(2*r*r-4*r-10801)/D**2)==0
assert S.cancel(curve[0]+12*curve[1]-100*r*(3555-22*r)/D)==0
assert S.cancel(curve[3]-4*curve[2]-2*r*(5993+14*r)/D)==0
# Binding version: reconstruct the actual full caps before differentiating.
gamma[2]=F(5408,3599)
for coal in range(1,16,2):Z[coal]=[0]+[-1 if coal>>i&1 else gamma[i] for i in range(1,4)]
vb=[F(901,45),F(-1,36),F(3613,18000),F(2)]
assert payoff(laws)==vb
for i in range(4):
 vals=[]
 for t in [1,2,3,99]:
  ls=laws.copy();ls[i]={t:F(1)};vals.append(payoff(ls)[i])
 assert max(vals)==vals[-1]==vb[i]
q=[0,F(3613,57613),F(1,10),0];Q,C=ends(q,vb)
assert all((q[i]==0 or Q[i]>=C[i]) and(q[i]==1 or C[i]>=Q[i]) for i in range(4))
assert [q[i]*Q[i]+(1-q[i])*C[i] for i in range(4)]==[F(12809661,576130),F(1,40),F(3613,57613),F(469644,288065)]
y=S.symbols('y');A=S.Rational(1,2);B=S.Rational(2,3599)
x=(12*A*r+101*y)/(12+7*y);z=(97*B*r-y/4)/(97-2*y)
poly=3*x+4*z+3*x*z-gamma[2]*r
assert S.cancel(poly.subs(y,0)-3*A*B*r*(r-S.Rational(1,2)))==0
at={r:S.Rational(1,2),y:0}
Fr=S.diff(poly,r).subs(at);Fy=S.diff(poly,y).subs(at)
assert Fr==S.Rational(3,7198)
rp=-Fy/Fr;xp=(S.diff(x,r)*rp+S.diff(x,y)).subs(at);zp=(S.diff(z,r)*rp+S.diff(z,y)).subs(at)
assert (rp,xp,zp)==(S.Rational(-46188057,776),S.Rational(-69262831,2328),S.Rational(-11547912,349103))
assert -2*rp-xp/(1+x.subs(at))-1-zp/(1+z.subs(at))==S.Rational(4157665811,29100)
a=200*r/(3599+2*r);b=10*r/(r+2);c=r*(3614-2*r)/D
assert S.cancel(c-b/4-4*a/97-a*b/388+r*(3958*r+1047599)/(194*D))==0
q=[0,r/(r+2),0,2*r/(3599+2*r)];Q,C=ends(q,[r*g for g in gamma])
assert S.cancel(C[2]-Q[2]-3*r*(1-2*r)/D)==0
# Sharp finite compression controls, without claiming finite testing proves the bound.
for m in range(1,9):
 alpha=F(1,2);delta=alpha/(2**m-1);mass=[delta*2**(m-1-t) for t in range(m)]
 assert sum(mass)==alpha
 assert all(mass[t]-sum(mass[t+1:])==delta for t in range(m))
print('PASS: exact reselection curve, binding full caps/local derivatives, finite support grammar, and sharp compression controls')
