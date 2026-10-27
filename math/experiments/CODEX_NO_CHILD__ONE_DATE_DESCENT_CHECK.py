from itertools import product
from math import comb
import sympy as s
x=s.symbols('x0:4');t=s.symbols('t0:4')
L=s.Matrix([[0,-4,14,-7],[14,0,-6,-6],[-6,-7,0,14],[-6,14,-6,0]])
D=s.Matrix(4,4,lambda i,j:0 if i==j else L[i,j]-5*(sum(x[k] for k in range(4) if k not in(i,j))+s.prod(x[k] for k in range(4) if k not in(i,j))))
det=s.Poly(D.det(method='domain-ge'),*x)
u=[s.Poly(v,*x) for v in D.adjugate()*s.Matrix([21,52,92,49])]
P=s.prod(1+q for q in x)
S=s.expand(sum(s.prod(1+x[j] for j in range(4) if j!=i)*u[i].as_expr() for i in range(4)))
polys=[det.as_expr(),205*P*det.as_expr()+S,-(P*u[2].as_expr()-x[2]*S)]
box=[(s.Rational(3,25),s.Rational(9,50)),(s.Rational(11,100),s.Rational(19,100)),(s.Rational(3,25),s.Rational(4,25)),(s.Rational(13,100),s.Rational(17,100))]
for label,p in zip(['det D','positive survival gain','negative deficit gain'],polys):
 p=s.Poly(p,*x); d=p.degree_list(); sub={x[i]:lo+(hi-lo)*t[i] for i,(lo,hi) in enumerate(box)}
 q=s.Poly(p.as_expr().subs(sub,simultaneous=True).expand(),*t)
 co=q.terms(); bs=[]
 for k in product(*[range(v+1) for v in d]):
  b=sum(c*s.prod(s.Rational(comb(k[i],m[i]),comb(d[i],m[i])) for i in range(4)) for m,c in co if all(m[i]<=k[i] for i in range(4)))
  bs.append(b)
 assert min(bs)>0, (label,min(bs))
 print(label,'degrees',d,'terms',len(p.terms()),'Bernstein',len(bs),'min',min(bs),'positive',min(bs)>0,flush=True)

# Exact inclusion of the legal positive-cap branch in the four-dimensional box.
z,y,tau=s.symbols('z y tau')
l,h,c,k=5*(1+z),14-5*z,6+5*z,6*z
d,e,a,b=h*h-l*k,20*l,c*c-l*k,20*k
F=s.expand((4+5*z)*(a*y+b)+(7+5*z)*y*(d-e*y)+l*(a*y+b)*y-14*z*(d-e*y))
for endpoint, sign in [(s.Rational(13,100),-1),(s.Rational(17,100),1)]:
 q=s.Poly(F.subs({y:endpoint,z:s.Rational(3,25)+tau/25}).expand(),tau)
 deg=q.degree()
 bs=[sum(q.nth(j)*s.Rational(comb(i,j),comb(deg,j)) for j in range(i+1)) for i in range(deg+1)]
 assert all(sign*v>0 for v in bs)
phi=(k+c*y)/(h-l*y)
phi2=(a*y+b)/(d-e*y)
for z0,y0,side in [(s.Rational(3,25),s.Rational(13,100),0),(s.Rational(4,25),s.Rational(17,100),1)]:
 vals={z:z0,y:y0}
 assert (h-l*y).subs(vals)>0 and (d-e*y).subs(vals)>0
 for expr,index in [(phi,0),(phi2,1)]:
  value=expr.subs(vals)
  assert box[index][0]<value<box[index][1]
print('PASS: exact box inclusion and all three strict descent signs.')
