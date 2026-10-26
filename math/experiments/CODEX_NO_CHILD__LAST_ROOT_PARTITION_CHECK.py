"""Exact polynomial check of the M14 last-root sign partition; requires SymPy."""
import sympy as s

z, y = s.symbols('z y')
L, h, C, K = 5*(1+z), 14-5*z, 6+5*z, 6*z
d, e, a, b = h*h-L*K, 20*L, C*C-L*K, 20*K
x0, x1 = (K+C*y)/(h-L*y), (a*y+b)/(d-e*y)
F = s.factor(((4+5*z)*x1+(7+5*z)*y+L*x1*y-14*z)*(d-e*y))
g2 = 6*x0+7*x1-14*y+5*(x0*x1+x0*y+x1*y+x0*x1*y)
R = (33173125*z**8+1623635000*z**7+12936067000*z**6
     -15895969500*z**5-307529649300*z**4-629973729300*z**3
     -333138223960*z**2+40832208960*z+1080998816)
C0 = 125*z**6+3875*z**5+625*z**4-510200*z**3+936360*z**2+7107160*z-1094208
C1 = 475*z**6+7750*z**5+60245*z**4+97695*z**3+4062*z**2-11916*z+49248
C2 = (3500*z**6+2960500*z**5+120049675*z**4+357877500*z**3
      +421691860*z**2+225435280*z+34281968)
C3 = 2375*z**6+38750*z**5+137825*z**4+320325*z**3-506370*z**2-597660*z+476672
J = 5*z*z+70*z+84
G = s.factor(g2*(h-L*y)*(d-e*y))
assert s.factor(s.resultant(F, G, y)+10*z*J**3*R) == 0
caps = [-x1-z+2*y, -x0+z+y, x0+2*x1-y, x0-x1+z]
factors = [5*z*(z+1)*J**2, -25*z*(z+1)*J,
           50*z*(z+1)**2*J**3, -5*z*(z+1)*J**3]
for cap, factor, poly in zip(caps, factors, [C0,C1,C2,C3]):
    num = s.factor(s.together(cap)).as_numer_denom()[0]
    assert s.factor(s.resultant(F,num,y)-factor*poly) == 0
assert 11916**2-4*4062*49248 == -658190448
assert all(c > 0 for c in s.Poly(C2,z).all_coeffs())
coeffs = s.Poly(R,z).all_coeffs()
assert sum(1 for a,b in zip(coeffs,coeffs[1:]) if a*b < 0) == 2
Q = s.Rational
for p, left, right in [(R,Q(3,25),Q(121,1000)),
                       (C0,Q(3,20),Q(4,25)),
                       (C3,Q(3,5),Q(7,10))]:
    assert p.subs(z,left)*p.subs(z,right) < 0
assert R.subs(z,1)<0<R.subs(z,5)
A = 70*z*z+2980*z-2264
assert A.subs(z,Q(74,100))<0<A.subs(z,Q(3,4))
assert 7107160-1530600 > 0
B = 14250*Q(3,4)**4+193750*Q(3,4)**3+551300*Q(3,4)**2+960975*Q(3,4)-1012740
assert B == Q(13356105,128) and B*Q(3,4)-597660 < 0
v0,v1,v3 = Q(405,379),Q(336,379),Q(566,379)
assert 4*v1-14+7*v3 == -14*v0+6+6*v3 == 6*v0-14*v1+6 == 0
assert 6*v0+7*v1-14*v3 == -Q(3142,379)
assert [-v1-1+2*v3,-v0+1+v3,v0+2*v1-v3,v0-v1+1] == [Q(n,379) for n in [417,540,511,448]]
assert 25*Q(3,4)**2-150*Q(3,4)+116>0
print('PASS: complete M14 admissible and cap-sign partition by exact resultant identities and rational signs.')
