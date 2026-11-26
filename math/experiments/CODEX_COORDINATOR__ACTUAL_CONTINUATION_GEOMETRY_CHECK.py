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

# Section11: geometric insertion at a two-zero tail, with exact head compensation.
q=s.symbols('q0:4')

def reward(i,A):
    if 0 not in A:
        if i==0:return s.Integer({1:1,2:-4,3:12}[len(A)])
        if A=={i}:return s.Integer(0)
        if i in A:
            return s.Integer((-3 if i==1 else -2) if len(A)==2 else (2 if i==1 else 0))
        if len(A)==1:return s.Integer(-2)
        return s.Integer(0 if i==1 else -1)
    if i==0:
        return s.Integer({1:0,2:2,3:-6,4:12}[len(A)])
    if i==1:
        if i not in A:return s.Integer(1) if A=={0} else s.Rational(4,5)
        return s.Integer(2) if A=={0,1} else s.Rational(2,5)
    if i==2:
        if i not in A:return s.Integer(-1) if A=={0} else s.Rational(31,5)
        return s.Integer(-1) if A=={0,2} else s.Integer(6)
    if i not in A:return s.Integer(2) if A=={0} else s.Rational(19,5)
    return s.Integer(2) if A=={0,3} else s.Rational(18,5)

def offers(i, reward_fn=reward):
    others=[j for j in range(4) if j!=i]
    Q=P=s.Integer(0)
    for bs in product([0,1],repeat=3):
        A={j for j,b in zip(others,bs) if b}
        pr=s.prod(q[j] if j in A else 1-q[j] for j in others)
        Q+=pr*reward_fn(i,A|{i})
        if A:P+=pr*reward_fn(i,A)
    return s.expand(Q),s.expand(P)

for i in range(4):assert reward(i,{i})==0
OP=[offers(i) for i in range(4)]
tail_sub=dict(zip(q,[s.Rational(1,2)]+[s.Rational(1,3)]*3))
w=[s.Integer(0),s.Integer(0),s.Integer(1),s.Integer(1)]
assert [v[0].subs(tail_sub) for v in OP]==w
assert [v[1].subs(tail_sub) for v in OP]==w
head_sub=dict(zip(q,[0]+[s.Rational(1,2)]*3))
H=[s.prod(1-q[k] for k in range(4) if k!=i) for i in range(4)]
g=[OP[i][0]-OP[i][1]-H[i]*w[i] for i in range(4)]
assert [g[i].subs(head_sub) for i in range(4)]==[-s.Rational(3,8),0,0,0]
assert [OP[i][1].subs(head_sub)+H[i].subs(head_sub)*w[i] for i in range(4)]==[s.Rational(3,8),-1,-1,-1]
J=s.Matrix([[s.diff(g[i],q[j]).subs(head_sub) for j in [1,2,3]] for i in [1,2,3]])
assert J==s.ones(3)-s.eye(3)
assert J.det()==2
# The last-atom test forbids every nonempty finite one-owner insertion.
assert reward(1,{0,1})-reward(1,{0})==1
assert reward(0,{0,1})-reward(0,{1})==1
# Geometric j=0 rate1/2 meets zero observer1 exactly.
r=s.Rational(1,2)
assert r*reward(1,{0,1})==reward(1,{0})
a=s.Matrix([reward(i,{0})-w[i] for i in [1,2,3]])
assert a==s.Matrix([1,-2,1])
b=J.inv()*a/4
assert b==s.Matrix([-s.Rational(1,4),s.Rational(1,2),-s.Rational(1,4)])
L=1+sum(2*x for x in b)
assert L==1
assert s.prod(1-v for v in tail_sub.values())==s.Rational(4,27)
assert s.Rational(1,8)*s.Rational(4,27)==s.Rational(1,54)
# Positive outside rows allow beta<=2/3 (row2 is the binding buffer).
assert r*reward(2,{0,2})-reward(2,{0})==s.Rational(1,2)
assert r*reward(3,{0,3})-reward(3,{0})==-1
# Pure123 is already an absorbing equilibrium; this is no new raw UE class.
pure_sub=dict(zip(q,[0,1,1,1]))
for i in range(4):
    d=(OP[i][0]-OP[i][1]).subs(pure_sub)
    assert d<=0 if i==0 else d>=0

# Symbolic active branch, without selecting numerical roots.
tau=s.symbols('tau', real=True)
x1,x2,x3=s.symbols('x1 x2 x3', positive=True)
odds=dict(zip(q,[0,x1/(1+x1),x2/(1+x2),x3/(1+x3)]))
wt=[0,tau,1-2*tau,1+tau]
branch=[-x2-x3+2*x2*x3-tau, x1*x3-1+2*tau, x1*x2-1-tau]
for i in [1,2,3]:
    assert same(((OP[i][0]-OP[i][1])/H[i]).subs(odds)-wt[i],branch[i-1])
poly=tau*x1**2+(2-tau)*x1-2+2*tau+4*tau**2
assert same(branch[0].subs({x2:(1+tau)/x1,x3:(1-2*tau)/x1}),-poly/x1**2)
at_zero={x1:1,tau:0}
assert poly.subs(at_zero)==0 and s.diff(poly,x1).subs(at_zero)==2
x1prime=-s.diff(poly,tau).subs(at_zero)/s.diff(poly,x1).subs(at_zero)
assert x1prime==-1
assert 1-x1prime==2 and -2-x1prime==-1
assert -1-2*sum(b)==-1  # Complete original Never logarithmic derivative.
assert all(any(reward(i,{j})<0 for i in range(4) if i!=j) for j in range(4))
print('PASS: two-zero full-cap tail, finite-clock obstruction, geometric insertion, exact compensated branch and Never descent')

# Section12: a moving actual continuation defeats the fixed-tail floor.
beta=s.symbols('beta', positive=True)
def moving_reward(i,A):
    if i==0:
        if A=={1}: return s.Integer(-2)
        if A=={0,1}: return s.Integer(-1)
        return s.Integer(int(2 in A)-int(3 in A))
    if i==1:
        if A=={0}: return s.Integer(-2)
        if A=={0,1}: return s.Integer(-1)
        return s.Integer(0)
    return s.Integer(int((3 if i==2 else 2) in A))
OP=[offers(i,moving_reward) for i in range(4)]
assert all(moving_reward(i,{i})==0 for i in range(4))
assert moving_reward(0,{1})==moving_reward(1,{0})==-2
assert moving_reward(0,{0,1})==moving_reward(1,{0,1})==-1
S=s.Rational(1,2)+beta/(1-beta)
qt={q[0]:0,q[1]:0,q[2]:S,q[3]:s.Rational(1,2)}
w=[beta/(1-beta),0,s.Rational(1,2),S]
for i in range(4):
    assert s.simplify(OP[i][0].subs(qt)-w[i])==0
    assert s.simplify(OP[i][1].subs(qt)-w[i])==0
qh={q[0]:0,q[1]:beta,q[2]:0,q[3]:0}
H=[s.prod(1-q[j] for j in range(4) if j!=i) for i in range(4)]
Q=[s.simplify(OP[i][0].subs(qh)) for i in range(4)]
C=[s.simplify(OP[i][1].subs(qh)+H[i].subs(qh)*w[i]) for i in range(4)]
assert Q==[-beta,0,0,0]
assert C==[-beta,0,(1-beta)/2,(1+beta)/2]
assert s.simplify((1-beta)*(1-S)/2-(s.Rational(1,4)-3*beta/4))==0
# For 0<beta<1/3 every tail hazard is proper and positive-owner gaps >0.
pure=dict(zip(q,[0,0,1,1]))
assert all(s.simplify((Q-P).subs(pure))==0 for Q,P in OP)
print('PASS: blocked pair with actual nearby-tail marked descent and zero full debt')

# Section12: exact first-date-feasible control and finite nineteen-date certificate.
G=s.Matrix([[0,1,1],[1,0,-1],[-1,-100,0]])
J=s.Matrix([[0,2,2],[2,0,-s.Rational(3,2)],[-s.Rational(3,2),-150,0]])
assert G*s.ones(3,1)/3-J*s.Matrix([0,1,0])/3==s.Matrix([0,0,s.Rational(49,3)])
assert 3**18>1200*2**18
assert min(J[i,j]/G[i,j] for i in range(3) for j in range(3) if G[i,j]>0)==2
assert max(J[i,j]/G[i,j] for i in range(3) for j in range(3) if G[i,j]<0)==s.Rational(3,2)

def rigid_reward(i,A):
    if i==0:
        return s.Integer(A!={0})
    core={1,2,3}
    if len(A)==1:
        return G[i-1,next(iter(A))-1] if 0 not in A else s.Integer(0)
    if len(A)==2 and i in A and A<=core:
        j=next(iter(A-{i}))
        return J[i-1,j-1]
    if A==core-{i}:return -sum(G.row(i-1))
    if A==core:return -sum(J.row(i-1))
    return s.Integer(0)

OP=[offers(i,rigid_reward) for i in range(4)]
root=s.symbols('root', nonnegative=True)
at_root=dict(zip(q,[root]+[s.Rational(1,2)]*3))
want=[s.Rational(7,8),0,0,0]
assert [s.simplify(Q.subs(at_root)) for Q,P in OP]==want
assert [s.simplify(P.subs(at_root)) for Q,P in OP]==want
assert s.prod(1-x for x in at_root.values())==(1-root)/8
print('PASS: nineteen-date obstruction, actual four-owner continuation, and payoff-preserving existing-law descent')

# Section13: revise the existing inert source and add an exact infinite tail.
# Reuse the canonical fixture and its checks instead of copying sixty rewards.
from pathlib import Path
from contextlib import redirect_stdout
import io
import runpy

with redirect_stdout(io.StringIO()):
    fixture=runpy.run_path(str(Path(__file__).with_name(
        'CODEX_GLOBAL_CREATIVE__FINITE_EXACT_NASH_INCOMPLETENESS_CHECK.py')))
p=s.symbols('p', nonnegative=True)
core_value=2*p-p**2
passive=p+p**2
survival=(1-p)**2
for i in range(3):
    P,Q,H=fixture['endpoints'](i,[p,p,p,0])
    assert same(P,passive) and same(Q,core_value) and same(H,survival)
seam=p*(1-2*p)/(1-p)**2
step=1-s.sqrt(1-seam)
assert same(seam,p-p**3/(1-p)**2)
assert same(2*step-step**2,seam)
assert same(passive+survival*seam,core_value)
assert s.Rational(1,2)>s.Rational(4,9)  # 1+sqrt(1/2)>5/3 gives T(p)<=3p/5.
assert step.subs(p,0)==step.subs(p,s.Rational(1,2))==0
assert s.diff(step,p).subs(p,0)==s.Rational(1,2)
assert s.diff(step,p).subs(p,s.Rational(1,2))==-2
tail_sum_slope=2/(1-s.Rational(1,2))
log_never_slope=3*(2-tail_sum_slope)
assert log_never_slope==-6
assert s.Rational(1,8)*log_never_slope==-s.Rational(3,4)
epsilon=s.symbols('epsilon', positive=True)
assert same(core_value.subs(p,s.Rational(1,2)-epsilon),
            s.Rational(3,4)-epsilon-epsilon**2)
# Explicit interval 0<epsilon<=1/32: the first three survival factors suffice.
assert same(((1-p)**2*(1-seam)).subs(p,s.Rational(1,2)-epsilon),
            s.Rational(1,4)+3*epsilon**2)
assert 2*(1-2*s.Rational(1,32))/(1+2*s.Rational(1,32))**2==s.Rational(480,289)>1
assert s.Rational(1,5)>6*s.Rational(1,32)
# Exact induction for the prescribed and Never truncation defects.
tail_never,end_value=s.symbols('tail_never end_value', nonnegative=True)
prescribed=p*core_value+(1-p)*(passive+survival*(seam-tail_never**3*end_value))
never_value=passive+survival*(seam-tail_never**2*end_value)
assert same(prescribed,core_value-((1-p)*tail_never)**3*end_value)
assert same(never_value,core_value-((1-p)*tail_never)**2*end_value)
print('PASS: actual infinite-tail whole-law descent, strict Never derivative, and exact truncation defects')

# Section13: the full vector tail map removes every symmetric-orbit minimum.
r=s.symbols('r', real=True)
v=s.symbols('v:3')
quit=s.Matrix([fixture['endpoints'](i,list(v)+[0])[1] for i in range(3)])
seams=s.Matrix([(fixture['endpoints'](i,list(v)+[0])[1]
                 -fixture['endpoints'](i,list(v)+[0])[0])
                /fixture['endpoints'](i,list(v)+[0])[2] for i in range(3)])
J=quit.jacobian(v).subs(dict.fromkeys(v,r))
K=seams.jacobian(v).subs(dict.fromkeys(v,p))
L=s.simplify(J.inv()*K)
assert L.subs({p:0,r:0})==s.eye(3)/2
curvature_a=(9*p**2-15*p+7)/((1-p)**6*(r**2-2*r+28))
curvature_b=(3*(1-2*p)/(1-p)**4-curvature_a)/(2*(1-r))
for direction in [s.Matrix([1,-1,0]),s.Matrix([1,1,-2])]:
    tangent=L*direction
    assert same(tangent.dot(tangent),curvature_a*direction.dot(direction))
    zdd=s.Matrix([(direction.T*s.hessian(seams[i],v)*direction)[0]
                  .subs(dict.fromkeys(v,p)) for i in range(3)])
    Qdd=s.Matrix([(tangent.T*s.hessian(quit[i],v)*tangent)[0]
                  for i in range(3)])
    assert same(sum(J.inv()*(zdd-Qdd)),curvature_b*direction.dot(direction))
margin=s.expand(81*(1-2*p)*(1-p)**2-(9*p**2-15*p+7))
assert margin==74-309*p+396*p**2-162*p**3
assert margin.subs(p,s.Rational(9,20))==s.Rational(1511,4000)
assert s.diff(margin,p).subs(p,s.Rational(9,20))<0
assert s.diff(margin,p,2).subs(p,s.Rational(9,20))>0
assert s.Rational(9,20)**2-5*s.Rational(9,20)+2<0
print('PASS: vector tail derivative, transverse curvature identities, and exact whole-orbit sign margins')

# Section13: a different source is isolated among ALL nearby exact clock laws.
def isolated_reward(i,A):
    if i==3:
        return s.Rational(1,10) if 3 not in A else s.Integer(-int(len(A)>1))
    if 3 in A:return s.Integer(0 if i in A else -1)
    j,k=(i+1)%3,(i-1)%3
    table={frozenset({i}):0,frozenset({j}):2,frozenset({k}):-3,
           frozenset({i,j}):20,frozenset({i,k}):-10,
           frozenset({j,k}):100,frozenset({0,1,2}):0}
    return s.Integer(table[frozenset(A)])

assert all(isolated_reward(i,{i})==0 for i in range(4))
G=s.Matrix(4,4,lambda i,j:isolated_reward(i,{j}))
J=s.Matrix(4,4,lambda i,j:isolated_reward(i,{i,j}))
assert [sum(G.col(j)) for j in range(4)]==[-s.Rational(9,10)]*3+[-3]
assert [sum(J.col(j)) for j in range(4)]==[9,9,9,0]
OP=[offers(i,isolated_reward) for i in range(4)]
star=s.Rational(11,111)
at_star=dict(zip(q,[star]*3+[0]))
w=s.Rational(11000,12321)
ws=[w]*3+[s.Rational(1,10)*(1-(1-star)**3)]
assert all(OP[i][0].subs(at_star)==OP[i][1].subs(at_star)==w for i in range(3))
assert OP[3][0].subs(at_star)<OP[3][1].subs(at_star)==ws[3]
for i in range(3):
    x,y=q[(i+1)%3],q[(i-1)%3]
    F0=18*x-7*y-111*x*y
    assert same(OP[i][0]-OP[i][1],(1-q[3])*F0+q[3])
    core_gap=(OP[i][0]-OP[i][1]).subs(q[3],0)
    assert s.diff(core_gap,x).subs(at_star)==7
    assert s.diff(core_gap,y).subs(at_star)==-18
assert same(121*(1-p)**2-400*(11*p-111*p**2),(211*p-11)**2)
assert s.Rational(121,400)<w
assert s.Rational(9,10)-600*s.Rational(3,4000)==s.Rational(9,20)
# Known absorbing competitor: full Bellman comparisons, including quiet owners.
stationary=dict(zip(q,[s.Rational(3,10),s.Rational(1,10),0,0]))
target=[2,-3,9,s.Rational(1,10)]
for i in range(4):
    quit_offer=OP[i][0].subs(stationary)
    H=s.prod(1-q[j] for j in range(4) if j!=i)
    continue_offer=(OP[i][1]+H*target[i]).subs(stationary)
    assert continue_offer==target[i]
    assert quit_offer==target[i] if i<2 else quit_offer<target[i]
print('PASS: all-law isolation control, local debt-floor data, root-inertia identities, and absorbing competitor')
