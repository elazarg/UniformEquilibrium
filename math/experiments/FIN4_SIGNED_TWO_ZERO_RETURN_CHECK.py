"""Exact unequal-premium two-root source comparison, with all behavioral caps.

Run: python math/experiments/FIN4_SIGNED_TWO_ZERO_RETURN_CHECK.py
Requires SymPy. The complete fixed reward table is below. Exact polynomial
identities and Bernstein coefficients certify the example; this is not a
search over arbitrary tables or controllers. The literal game has absorbing
Nash (checked below), so it is not a positive-gap or new UE-class witness.
The corresponding proof is in SIGNED_TWO_ZERO_CONTINUATION_REDUCTION.md.
"""
import sympy as s
R=s.Rational
G=s.Matrix([[0,5,-1,-1],[-2,0,1,1],[2,-1,0,-1],[2,-1,-1,0]])
L=s.Integer(1000)
Z={}
for mask in range(1,16):
    Z[mask]=list(G[:,mask.bit_length()-1]) if mask & (mask-1)==0 else [s.Integer(0)]*4
Z[5][2]=8; Z[9][3]=8; Z[12][2]=-R(1,2); Z[12][3]=-R(4,5)
Z[12][0]=L; Z[12][1]=-L
Z[3][0]=-256; Z[3][1]=1; Z[6][2]=-8; Z[10][3]=-8
U0=[R(2802569,32000000),R(40951,250000),0,0]
B0=[R(3683,16000),R(40951,250000),0,0]
N0=[R(9,20),R(1,2),R(81,200),R(81,200)]
def root(q,U,B,N):
    PP=[];QQ=[];HH=[]
    for i in range(4):
        P=Q=s.Integer(0)
        for mask in range(16):
            if mask>>i&1:continue
            prob=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in range(4) if j!=i)
            if mask:P+=prob*Z[mask][i]
            Q+=prob*Z[mask|1<<i][i]
        PP.append(s.factor(P));QQ.append(s.factor(Q));HH.append(s.prod(1-q[j] for j in range(4) if j!=i))
    c=s.prod(1-qj for qj in q)
    UU=[s.factor(q[i]*QQ[i]+(1-q[i])*PP[i]+c*U[i]) for i in range(4)]
    EE=[s.factor(PP[i]+HH[i]*B[i]) for i in range(4)]
    return UU,EE,QQ,[s.factor((1-q[i])*N[i]) for i in range(4)]
f=B0[1]/(B0[1]+3);g=2*f/(1+f)
U,B,Q,N=root([f,g,0,0],U0,B0,N0)
assert all(U[i]==B[i] for i in (1,2,3))
assert B[2]==B[3]==0 and B[0]>0 and B[1]>0
assert all(B[i]>=Q[i] for i in range(4))
bp,bk=B[:2];u=U[0];nu=s.prod(N)
assert u<-2*bk and u+bk<-R(2,5)
print('Produced U=',U)
print('Produced B=e=',B)
print('Produced N=',N)
print('u+2bk=',s.factor(u+2*bk),' u+bk+2/5=',s.factor(u+bk+R(2,5)))
v=s.symbols('v',positive=True)
z=v*(2+3*v)/(2*(1-2*v));t=7*v*(1+v)/(2*(1-2*v))
w=v/(2-2*v+3*v*v)
UT=[(1-t)*u,(1-t)*bk-2*t,2*t,2*t]
BT=[bp,UT[1],2*t,2*t]
NT=[(1-t)*N[0],N[1],N[2],N[3]]
U1,B1,Q1,N1=root([z/(1+z),0,5*v/(1+5*v),2*v/(1+2*v)],UT,BT,NT)
assert all(s.cancel(U1[i]-B1[i])==s.cancel(Q1[i]-B1[i])==0 for i in (2,3))
assert s.cancel(B1[2]-14*w)==s.cancel(B1[3]-8*w)==0
UU,EE,QQ,NN=root([w/(1+w),0,10*w/(1+10*w),16*w/(1+16*w)],U1,B1,N1)
assert UU[2]==EE[2]==QQ[2]==0 and UU[3]==EE[3]==QQ[3]==0
P=s.Poly(s.cancel((EE[1]-bk)/v).as_numer_denom()[0],v)
assert P.as_expr()==(-11056770*v**7+286365677031*v**6-4320206716803*v**5
 +571366811308*v**4-1645508206366*v**3-1265376442516*v**2
 -316159728872*v+55085880)
lo=R(17411,10**8);hi=R(17412,10**8)
assert P.eval(lo)>0>P.eval(hi)
# Exact positivity on [lo,hi] by Bernstein coefficients.
def positive_on(expr):
    num,den=s.fraction(s.factor(expr));x=s.symbols('x')
    if den.subs(v,(lo+hi)/2)<0:num,den=-num,-den
    for part in (num,den):
        poly=s.Poly(s.expand(part.subs(v,lo+(hi-lo)*x)),x)
        deg=poly.degree()
        coeff=[sum(poly.nth(j)*s.binomial(k,j)/s.binomial(deg,j) for j in range(k+1)) for k in range(deg+1)]
        assert all(v>0 for v in coeff),(expr,part,coeff)
positive_on(-P.diff().as_expr())
positive_on(t);positive_on(1-t);positive_on(UT[1])
positive_on(B1[0]-Q1[0]);positive_on(B1[1]-Q1[1])
positive_on(B1[2]);positive_on(B1[3])
positive_on(bp-EE[0]);positive_on(UU[0]-u)
positive_on(EE[0]-QQ[0]);positive_on(EE[1]-QQ[1])
positive_on(nu-s.prod(NN));positive_on(s.prod(NN))
print('Return polynomial=',P.as_expr())
print('Unique return root within the rational interval',lo,hi)
pure_u,pure_e,pure_q,_=root([0,1,1,1],[0]*4,[0]*4,[1]*4)
assert all(pure_u[i]==max(pure_e[i],pure_q[i]) for i in range(4))
print('PASS both-root contacts, exact return, full guards, strict dominance, and solved-game boundary.')
