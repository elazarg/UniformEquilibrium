from fractions import Fraction as Q
from itertools import combinations
I=range(4)
eta0=Q(12281660,12608823)
def table(eta=eta0,K=1000,p=0,R=-25,t=987,g02=-1):
 return {1:[0,2,2,-1],2:[3,0,-2,-2],4:[g02,Q(1,2),0,1],8:[3,-3,-1,0],3:[0,-1,-10,-12],5:[Q(-1,10),5,2+eta,Q(-219,29)],6:[-12,-K,p,-6],9:[-20,3,-5,1],10:[2,-100,-1,10],12:[R,9,3,-100],7:[-20,6,-100,11],11:[-20,8,10,-10],13:[-20,-8,-100,t],14:[-8,11,2,1],15:[-5,-9,-100,Q(21,2)]}
def endpoints(Z,q,v):
 quit=[];cont=[];out=[]
 for i in I:
  Q_i=0;C_i=0
  for S in range(16):
   if S>>i&1:continue
   pr=Q(1)
   for j in I:
    if j!=i:pr*=q[j] if S>>j&1 else 1-q[j]
   Q_i+=pr*Z[S|1<<i][i]
   C_i+=pr*(Z[S][i] if S else v[i])
  quit.append(Q_i);cont.append(C_i);out.append(q[i]*Q_i+(1-q[i])*C_i)
 return quit,cont,out

def nash(q,A,C):
 return all((q[i]==0 or A[i]>=C[i]) and(q[i]==1 or C[i]>=A[i]) for i in I)
Z=table(K=0,t=Q(28599,29),R=777)
qs=[[0,0,0,Q(1,20)],[Q(87,947),0,Q(3,10),0],[0,0,0,Q(3,100)],[0,0,0,Q(525873,29323973)],[0,0,0,Q(22221,476821)]]
vs=[[Q(243,2000),Q(66663,454600),Q(607433,2898580),0],[Q(-3,100),Q(134853,431870),Q(39598,144929),0],[Q(27,70),Q(-42984,302309),Q(14281,144929),0],[Q(207,679),Q(-1577619,29323973),Q(1862887,14058113),0],[Q(12069,47210),0,Q(104816681,684209809),0]]
for k,(q,v) in enumerate(zip(qs,vs)):
 A,C,F=endpoints(Z,q,vs[(k+1)%5]);assert F==v,(k,F,v);assert nash(q,A,C),(k,A,C)
 margins=[F[i]-A[i] for i in I]
 print('five_date',k,'quiet_margins',margins)
Z=table()
controls=[([Q(1,2),0,Q(1,2),Q(1,50)],[Q(261,490),1,eta0-Q(13,7),Q(25971,29)]),([0,Q(99,100),Q(19,20),Q(9999,10000)],[200000000,Q(-1217901,2),3009897,12436])]
for k,(q,v) in enumerate(controls):
 A,C,F=endpoints(Z,q,v);assert nash(q,A,C),(k,A,C);print('global_control',k,'Q',A,'C',C,'F',F)
Z=table(eta=500,K=Q(1,2),R=4000,t=60000,g02=-500)
q=[0,Q(99,100),Q(99,100),Q(1,2)];v=[-1,2,499,59796]
A,C,F=endpoints(Z,q,v);assert nash(q,A,C),(A,C);assert F==[Q(150977,20000),Q(1879,400),Q(201,200),Q(891,10000)]
print('negative_control PASS',F)
Z=table();edges={(j,i) for i in I for j in I if i!=j and Z[1<<j][i]>0 and Z[(1<<i)|(1<<j)][i]<=Z[1<<j][i]}
assert edges=={(0,1),(1,0),(2,1),(2,3),(3,0)}
closed=[]
for mask in range(1,15):
 if all(not(mask>>i&1) or bool(mask>>j&1) for j,i in edges):closed.append(mask)
assert closed==[4,12]
print('safe-edge closure PASS')
# Exact symbolic two-date identities after solving the raw hazard equations.
import sympy as s
x,z,K,e=s.symbols('x z K e')
ZZ=table(eta=e,K=K,R=(9/z-209)/10,t=(2929/x-3148)/29)
A,C,F=endpoints(ZZ,[x,0,1,z],[0,0,-10,0])
assert s.simplify(A[0]-C[0])==0
assert s.simplify(A[3]-C[3])==0
assert s.simplify(C[1]-A[1]-((1-3*x-5*z+9*x*z)/2+K*(1-x)*(1-z)))==0
assert s.simplify(A[2]-C[2]-(10+(e-10)*x-6*z-(e+89)*x*z))==0
print('two-date symbolic identities PASS')

# The negative-K extension and its exact bounded-invariance countercontrol.
b,R=s.symbols('b R')
f=(30+173*b)/(100*(100-111*b))
assert s.simplify(s.diff(f,b)-2063/(10*(100-111*b)**2))==0
assert f.subs(b,Q(3,4))==Q(639,6700)
assert f.subs(b,Q(4,5))==Q(421,2800)
assert s.simplify(f.subs(b,3/(3-R))-(609-30*R)/(100*(-33-100*R)))==0
Z=table(K=Q(-1,4),p=0)
q=[0,Q(3,5),Q(1,10),Q(1,10000)]
v=[0,Q(-13483,359964),Q(60011,19998),Q(143,18)]
A,C,F=endpoints(Z,q,v)
assert nash(q,A,C)
assert A[0]==Q(-1507237,1250000)
assert F==[Q(429991,500000),Q(6443,400000),Q(3,12500),Q(73,50)]
assert all(min(0,min(Z[a][i] for a in Z))<=v[i]<=max(0,max(Z[a][i] for a in Z)) for i in I)
print('negative-K extension algebra and bounded-invariance countercontrol PASS')
