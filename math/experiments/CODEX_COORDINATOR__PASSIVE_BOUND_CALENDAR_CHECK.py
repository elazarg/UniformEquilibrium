"""Exact all-marked calendar-NI controls for the index-selected separating table."""
from fractions import Fraction as F
import sympy as s
Z={1:[0,2,2,-1],2:[3,0,-2,-2],4:[-1,F(1,2),0,1],8:[3,-3,-1,0],3:[F(-1,100),-1,-10,-12],5:[F(-1,10),5,-1,F(-219,29)],6:[-12,F(1,4),F(-1,10000),-6],9:[-20,3,-5,1],10:[2,-100,-1,10],12:[-25,9,3,-100],7:[-20,6,-100,11],11:[-20,8,10,-10],13:[-20,-8,-100,987],14:[-1000,11,2,1],15:[-5,-9,-100,F(21,2)]}
def vertex(bs):
 u=Z[bs[0]] if bs else [0]*4;m=[]
 for i in range(4):
  rest=[b&~(1<<i) for b in bs];rest=[b for b in rest if b]
  m.append(Z[rest[0]][i] if rest else 0)
 return list(u)+m
blocks=[(1,2),(1,14),(4,3),(5,),(8,6),(8,7),(10,),(11,),(13,)]
M=s.Matrix.hstack(*(s.Matrix(vertex(b)+[1]) for b in blocks));V=M.inv()
def inside(v):
 y=s.Matrix(v+v+[1]);w=V*y
 assert all(a>0 for a in w) and sum(w)==1 and M*w==y
for i in range(4):
 for sign in [-1,1]:
  v=[0]*4;v[i]=F(sign,1000);inside(v)
def endpoints(q,v):
 Q=[];C=[];U=[]
 for i in range(4):
  qi=ci=0
  for A in range(16):
   if A>>i&1:continue
   pr=F(1)
   for j in range(4):
    if j!=i:pr*=q[j] if A>>j&1 else 1-q[j]
   qi+=pr*Z[A|1<<i][i];ci+=pr*(Z[A][i] if A else v[i])
  Q.append(qi);C.append(ci);U.append(q[i]*qi+(1-q[i])*ci)
 assert all((q[i]==0 or Q[i]>=C[i]) and(q[i]==1 or C[i]>=Q[i]) for i in range(4))
 return U
edges=sorted((j,i) for j in range(4) for i in range(4) if i!=j and Z[1<<j][i]>0 and Z[(1<<i)|(1<<j)][i]<=Z[1<<j][i])
e=F(1,1000000)
for mask in range(1,15):
 j,i=next((j,i) for j,i in edges if mask>>i&1 and not(mask>>j&1))
 v=[0 if k in (i,j) else e*(1+abs(Z[1<<j][k])+abs(Z[(1<<j)|(1<<k)][k])) for k in range(4)]
 q=[e if k==j else 0 for k in range(4)];U=endpoints(q,v);inside(v)
 assert min(v[k] for k in range(4) if mask>>k&1)==0
 assert min(U[k] for k in range(4) if mask>>k&1)>0
odds=[0,20*e,e,e/1000];q=[F(a)/(1+a) for a in odds]
v=[0,-347*e/1000+e*e/500,20001*e/500+3*e*e/50,139*e+140*e*e]
U=endpoints(q,v);inside(v)
assert v[1]<0 and min(U)>0 and sum(abs(a) for a in v)<F(1,1000)
assert U[0]*s.prod(1+a for a in odds)==59003*e/1000-47997*e*e/200-20*e**3
print('PASS: calendar diagonal contains l1-ball1/1000; all15 marked Nash-invariance choices fail inside it')
