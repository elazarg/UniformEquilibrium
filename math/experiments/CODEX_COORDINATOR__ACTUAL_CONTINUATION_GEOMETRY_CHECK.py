"""Exact actual continuation controls and head/tail descent; no numerical root census."""
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
a=200*r/(3599+2*r);b=10*r/(r+2);c=r*(3614-2*r)/D
assert S.cancel(c-b/4-4*a/97-a*b/388+r*(3958*r+1047599)/(194*D))==0
q=[0,r/(r+2),0,2*r/(3599+2*r)];Q,C=ends(q,[r*g for g in gamma])
assert S.cancel(C[2]-Q[2]-3*r*(1-2*r)/D)==0
# Sharp finite compression controls, without claiming finite testing proves the bound.
for m in range(1,9):
 alpha=F(1,2);delta=alpha/(2**m-1);mass=[delta*2**(m-1-t) for t in range(m)]
 assert sum(mass)==alpha
 assert all(mass[t]-sum(mass[t+1:])==delta for t in range(m))
print('PASS: exact reselection curve, binding full caps, finite support grammar, and sharp compression controls')

# Complete all-support finite-calendar classification and sharp path barrier.
from fractions import Fraction as Q
import sympy as s

r, y = s.symbols('r y', real=True)
a = s.Rational(194, 3599)
g = s.Rational(5408, 3599)
B = s.Rational(2, 3599)
x = (6*r + 101*y)/(12 + 7*y)
z = (194*r/s.Integer(3599) - y/4)/(97 - 2*y)
F = 3*x + 4*z + 3*x*z - g*r
same = lambda lhs, rhs: s.cancel(lhs-rhs) == 0
assert same(F.subs(y, 0), 3*r*(2*r-1)/7198)
assert same(s.diff(x,y), (1212-42*r)/(12+7*y)**2)
assert same(s.diff(z,y), 97*(16*r-3599)/(14396*(97-2*y)**2))
assert same(F.subs(y, 776*r/s.Integer(3599)),
            13*r*(32531361-1129856*r)/(7198*(1358*r+10797)))
# Full rectangle: 0<=r<=1, 0<=y<=776*r/3599<1/4.
assert Q(776,3599)<Q(1,4)
assert Q(1170)/(Q(55,4)**2)>Q(61,10)
assert -Q(97,4)/(Q(193,2)**2)>-Q(1,300)
assert Q(125,48)<3
assert 3*Q(61,10)-Q(13,300)>18
# Triple rectangle r<=1/2, y<=388/3599<1/8.
assert Q(388,3599)<Q(1,8)
assert Q(1191)/(Q(103,8)**2)>7
assert Q(125,96)<Q(4,3)
assert 21-Q(8,300)>20
assert Q(1212,144)<9
assert -Q(97,4)/(Q(387,4)**2)>-Q(1,380)
assert Q(3,143960)<Q(1,47000)
assert Q(1,2)+Q(9,47000)<Q(501,1000)
assert Q(2,3599)-Q(1,47000*380)>Q(1,1800)
# Exact signs used to eliminate other supports and control every output.
aa, gg = Q(194,3599), Q(5408,3599)
assert 50*gg/(4+gg)>12*aa
assert 4*gg-404*aa-6+Q(28,3)*gg*aa<0
assert 6-Q(2,3)*gg+4*aa-8*gg*aa>0
assert Q(1,18)-Q(1,188000)-Q(11,2*47000*1799)>0
assert Q(50,1799)<Q(1,4)
assert Q(501,1000)+Q(3,1799)+Q(501,1000*1799)<Q(503,1000)
assert (5-Q(1,470))/((1+Q(251,1000))*(1+Q(1,1000)))>3
assert 3>4*Q(51,100)
assert (50-Q(4,47000))/((1+Q(251,1000))*(1+Q(1,1000))**2)>39
assert 39>Q(1200,1799)
assert (Q(41,4)+Q(9,94000))/47000<Q(1,2)
assert Q(1,2)/(Q(5,4)*(1+Q(1,3599)))==Q(3599,9000)
print('PASS: exhaustive-support identities, strict interval bounds, trap and global minimum bounds')

# Section11: compensate a regular three-owner head over an ALL-active tail.
# All identities are symbolic; interval signs also have proofs in the note.
def descent_reward(i, coalition):
    if 0 in coalition:
        if i == 0:
            return s.Integer(0)
        if i not in coalition:
            return s.Rational(13, 4)
        return s.Integer(5 if len(coalition) == 2 else 2)
    if i == 0:
        return s.Integer({1: 1, 2: -1, 3: 0}[len(coalition)])
    if i in coalition:
        return s.Integer(0 if len(coalition) == 1 else -1)
    return s.Integer(-2 if len(coalition) == 1 else -1)


def descent_offers(hazards, continuation):
    quit_offers, continue_offers = [], []
    for i in range(4):
        others = [j for j in range(4) if j != i]
        qi = ci = s.Integer(0)
        for bits in product((0, 1), repeat=3):
            coalition = {j for j, bit in zip(others, bits) if bit}
            probability = s.prod(hazards[j] if j in coalition else 1-hazards[j]
                                 for j in others)
            qi += probability*descent_reward(i, coalition | {i})
            ci += probability*(descent_reward(i, coalition) if coalition
                               else continuation[i])
        quit_offers.append(s.cancel(qi))
        continue_offers.append(s.cancel(ci))
    return quit_offers, continue_offers


assert all(descent_reward(i, {i}) == 0 for i in range(4))
tail = [s.Integer(0), s.Integer(1), s.Integer(1), s.Integer(1)]
tq, tc = descent_offers([s.Rational(1, 2)]*4, [0]*4)
assert tq == tc == tail  # Full one-date cap: Quit0 or Continue/Never.
tau = s.symbols('tau', real=True)
qt, ct = descent_offers([tau, 0, 0, 0], tail)
assert qt[0] == ct[0] == 0
for i in range(1, 4):
    assert same(qt[i]-ct[i], 11*tau/4-1)
    assert same(ct[i], 1+9*tau/4)
z = (4+9*tau)/(12+9*tau)
hq, hc = descent_offers([0, z, z, z], ct)
assert hq[0] == 0 and same(hc[0], 3*z*(1-z)*(1-2*z))
assert all(same(hq[i], hc[i]) and same(hq[i], -(2*z-z*z))
           for i in range(1, 4))
assert s.Rational(4, 11) < s.Rational(4, 9)  # z<1/2 on the claimed interval.
assert [v.subs(tau, 0) for v in hc] == [s.Rational(2, 9)]+[s.Rational(-5, 9)]*3

hx = s.symbols('h0:4')
oq, oc = descent_offers(hx, tail)
gaps = [s.expand(a-b) for a, b in zip(oq, oc)]
at_head = dict(zip(hx, [0]+[s.Rational(1, 3)]*3))
jacobian = s.Matrix([[s.diff(gaps[i], hx[j]).subs(at_head)
                      for j in range(1, 4)] for i in range(1, 4)])
assert jacobian == s.ones(3)-s.eye(3) and jacobian.det() == 2
direction = jacobian.inv()*s.ones(3, 1)  # H_i*(Gamma_i0-w_i)=(4/9)*(9/4)=1.
assert direction == s.ones(3, 1)/2
never = (1-tau)*(1-z)**3/16
assert same(never, 32*(1-tau)/(12+9*tau)**3)
assert never.subs(tau, 0) == s.Rational(1, 54)
assert (s.diff(never, tau)/never).subs(tau, 0) == -s.Rational(13, 4)
# The control's existing absorbing equilibrium prevents any new-coverage claim.
pq, pc = descent_offers([0, 1, 1, 1], [0]*4)
assert pq == pc == [0, -1, -1, -1]
print('PASS: all-active exact tail, compensated full-cap head, Jacobian, and strict Never descent')
