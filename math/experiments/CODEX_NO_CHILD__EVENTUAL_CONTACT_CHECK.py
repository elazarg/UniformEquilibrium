"""Exact finite checks for the M14 eventual-full-contact proof.
Analytic and optimization arguments require the written proof.
Run with Python 3 and SymPy. No numerical root search is used.
"""
import sympy as s
G=s.Matrix([[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]])
J=s.Matrix([[0,-5,13,-5],[13,0,-5,-5],[-5,-5,0,13],[-5,13,-5,0]])
PD=s.Matrix([[-4,2,12,-2],[2,-8,8,8],[12,8,-35,19],[-2,8,19,-17]])/10
PV=s.Matrix([[-183,60,141,97],[60,-49,137,-44],[141,137,-282,111],[97,-44,111,-93]])/100
p=2; ep=s.eye(4)[:,p];Gi=G.inv();w=(s.ones(1,4)*Gi).T
v=Gi*ep
assert PD*v==ep and PV*v==w[p]*ep
K=s.Matrix(4,4,lambda i,j:0 if i==j else (w[i]*J[i,j]+w[j]*J[j,i]-1)/2)
def QQ(P):return (P*Gi*J+J.T*Gi.T*P-P)/2
r=s.symbols('r');P=PD+r*PV;M=ep*ep.T+r*s.diag(*w)-P*Gi
assert M*ep==s.zeros(4,1)
a=s.Matrix(s.symbols('a0:4'));E=s.Matrix(s.symbols('E0:4'))
# Raw quadratic part of c-1+w e-c w T, without observer-contact substitution.
P2=[]
for i in range(4):
 P2.append(-sum((G[i,j]+G[i,k])*a[j]*a[k] for j in range(4) for k in range(j+1,4) if i not in (j,k)))
c2=sum(a[i]*a[j] for i in range(4) for j in range(i+1,4))
V2=s.expand(c2+(w.T*s.Matrix(P2))[0]+sum(w[i]*a[i]*(E-G*a)[i] for i in range(4)))
assert s.expand(V2-(a.T*s.diag(*w)*(E-J*a))[0]-(a.T*K*a)[0])==0
ell2=a[p]*(E-J*a)[p]+r*V2-(a.T*M*(E-J*a))[0]
phi=lambda e:(e.T*Gi.T*P*Gi*e)[0]/2
sigma2=s.expand(ell2-phi(E)+phi(E-G*a))
expected=-(a.T*(QQ(PD)+r*(QQ(PV)-K))*a)[0]
assert s.expand(sigma2-expected)==0
print('PASS: exact ambient quadratic storage identity and observer-contact correction.')

# Positive-definite energy matrices, exact backward chart, and observability.
QD=QQ(PD); QV=QQ(PV)-K
assert [QD[:i,:i].det() for i in range(1,5)]==[s.Integer(7),s.Rational(3951,100),s.Rational(290527,2000),s.Rational(15333879,40000)]
assert [QV[:i,:i].det() for i in range(1,5)]==[s.Rational(4397,200),s.Rational(1143956171,4840000),s.Rational(4506212701697,5324000000),s.Rational(905937923038697,1064800000000)]
L=J-G; assert L.det()==-12568
A=s.eye(4)-J.inv()*G; b=J.inv()*ep
B=J*L.inv(); h=-G*L.inv()*ep
assert B==G*A.inv()*G.inv() and h==-G*A.inv()*b
assert B==s.eye(4)+G*L.inv() and h==(s.eye(4)-B)*ep
assert s.Matrix.hstack(b,A*b,A**2*b,A**3*b).det()==s.Rational(1043968,11440338672460347)
assert s.Matrix.vstack(*[h.T*(B.T)**k for k in range(4)]).det()!=0
# Exact real/complex spectral ordering for the adjoint sign theorem.
x=s.symbols('x');f=13611*x**4-54692*x**3+81334*x**2-52832*x+12568
assert s.expand(13611*A.charpoly(x).as_expr()-f)==0
assert s.discriminant(f,x)==-2**11*17*397*2532437821
poly=s.Poly(f,x)
assert poly.count_roots(-s.oo,s.oo)==2
assert poly.count_roots(s.Rational(650,1000),s.Rational(651,1000))==1
assert poly.count_roots(s.Rational(1107,1000),s.Rational(1108,1000))==1
assert s.Rational(12568,13611)/(s.Rational(651,1000)*s.Rational(1108,1000))>s.Rational(113,100)**2
# Full exact five-date baseline matrix and signed tangent.
O=[0,1,3]
constraint=s.Matrix([[int(m==k)*J[i,j]-int(m>=k)*G[i,j] for m in range(5) for j in range(4)] for k in range(5) for i in O]+[[G[i,j] for m in range(5) for j in range(4)] for i in range(4)])
rows=[[1045,775,970,1747],[-4674,-3575,-4373,-7445],[7829,6164,7351,11910],[-5820,-4708,-5464,-8476],[1620,1344,1516,2264]]
tangent=s.Matrix([n for row in rows for n in row])
assert constraint[:,:19].det()==77996937216
assert constraint*tangent==s.zeros(19,1)
assert -sum((s.Matrix(z).T*QD*s.Matrix(z))[0] for z in rows)==-1157984156
assert -sum((s.Matrix(z).T*QV*s.Matrix(z))[0] for z in rows)==-s.Rational(5894461073,11)
print('PASS: energy definiteness; backward map; adjoint observability/spectrum; five-date rank and signed curvature.')
