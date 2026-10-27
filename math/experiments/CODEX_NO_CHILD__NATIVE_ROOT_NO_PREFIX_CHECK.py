"""Exact rational M14 native-root and no-Nash-prefix certificates.
Requires SymPy; uses no floating arithmetic, sampling, or external files.
"""
import sympy as s
Q=s.Rational
Gamma=s.Matrix([[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]])
L=s.Matrix([[0,-4,14,-7],[14,0,-6,-6],[-6,-7,0,14],[-6,14,-6,0]])
A=s.Matrix([[714,1057,810,609],[732,714,672,994],
            [994,609,758,663],[672,810,1132,758]])/6284
assert A*L==s.eye(4) and all(v>0 for v in A)
assert Gamma*s.Matrix([4,5,1,3])==s.Matrix([0,0,11,0])
assert (L+Gamma)*s.Matrix([4,5,1,3])==s.Matrix([-27,32,-6,40])
z,y=s.symbols('z y')
ell,h,c,k=5*(1+z),14-5*z,6+5*z,6*z
d,e,a,b=h*h-ell*k,20*ell,c*c-ell*k,20*k
x0,x1=(k+c*y)/(h-ell*y),(a*y+b)/(d-e*y)
F=s.factor(((4+5*z)*x1+(7+5*z)*y+ell*x1*y-14*z)*(d-e*y))
g=6*x0+7*x1-14*y+5*(x0*x1+x0*y+x1*y+x0*x1*y)
G=s.factor(g*(h-ell*y)*(d-e*y))
R=(33173125*z**8+1623635000*z**7+12936067000*z**6
   -15895969500*z**5-307529649300*z**4-629973729300*z**3
   -333138223960*z**2+40832208960*z+1080998816)
assert s.factor(s.resultant(F,G,y)+10*z*(5*z*z+70*z+84)**3*R)==0
coeff=s.Poly(R,z).all_coeffs()
assert sum(1 for u,v in zip(coeff,coeff[1:]) if u*v<0)==2
assert R.subs(z,Q(3,25))>0>R.subs(z,Q(121,1000))
assert R.subs(z,1)<0<R.subs(z,5)
Az=70*z*z+2980*z-2264
assert Az.subs(z,Q(74,100))<0<Az.subs(z,Q(3,4))
v0,v1,v3=Q(405,379),Q(336,379),Q(566,379)
assert 4*v1-14+7*v3 == -14*v0+6+6*v3 == 6*v0-14*v1+6 == 0
assert 6*v0+7*v1-14*v3==-Q(3142,379)
def phi(z,y):return (6*z+(6+5*z)*y)/(14-5*z-5*(1+z)*y)
def endpoint(positive_z,y,negative_z):
 b=phi(positive_z,phi(positive_z,y))
 return (4+5*positive_z)*b+(7+5*positive_z)*y+5*(1+positive_z)*b*y-14*negative_z
lo,hi=Q(3,25),Q(121,1000)
assert endpoint(hi,Q(133,1000),lo)==-Q(57077215903529,6417899800000000)
assert endpoint(lo,Q(136,1000),hi)==Q(2219971,2087187500)
assert Q(126,1000)<phi(lo,Q(133,1000))<phi(hi,Q(136,1000))<Q(129,1000)
assert Q(122,1000)<phi(lo,phi(lo,Q(133,1000)))<phi(hi,phi(hi,Q(136,1000)))<Q(125,1000)
box=[(Q(126,1000),Q(129,1000)),(Q(122,1000),Q(125,1000)),(Q(120,1000),Q(121,1000)),(Q(133,1000),Q(136,1000))]
caplo=s.Matrix([Q(10000,716319),Q(7750000,89858239),Q(13000,80159),Q(968000,11390481)])
for i in range(4):
 numerator=sum(Gamma[i,j]*box[j][0 if Gamma[i,j]>=0 else 1] for j in range(4))
 assert caplo[i]==numerator/s.prod(1+box[j][1] for j in range(4) if j!=i)
blo=s.Matrix([1,8,16,8])/100
assert all(v>0 for v in caplo-blo)
assert all(v>Q(37,1000) for v in A*blo)
assert all(Q(12,25)<v<1 for v in A*s.ones(4,1))
assert 1-4*Q(36,5)*Q(37,1000)==-Q(41,625)
print('PASS native-Nash uniqueness and strict no-prefix rational certificates',flush=True)
