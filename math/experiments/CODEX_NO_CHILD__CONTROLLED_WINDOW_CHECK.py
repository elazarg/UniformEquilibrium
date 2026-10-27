#!/usr/bin/env python3
"""Exact raw matrix, curvature, spectrum, and premium-ray checks; no tolerances."""
import sympy as s
G = s.Matrix([[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]])
J = s.Matrix([[0,-5,13,-5],[13,0,-5,-5],[-5,-5,0,13],[-5,13,-5,0]])
v, w = G.inv()[:,2], s.ones(1,4)*G.inv()
PD = s.Matrix([[-4,2,12,-2],[2,-8,8,8],[12,8,-35,19],[-2,8,19,-17]])/10
PV = s.Matrix([[-183,60,141,97],[60,-49,137,-44],
               [141,137,-282,111],[97,-44,111,-93]])/100
assert v == s.Matrix([4,5,1,3])/11 and w == s.Matrix([[7,10,13,8]])/11
assert PD == PD.T and PV == PV.T
assert PD*v == s.eye(4)[:,2] and PV*v == s.Rational(13,11)*s.eye(4)[:,2]
Q = lambda P: (P*G.inv()*J + J.T*G.inv().T*P - P)/2
K = s.zeros(4)
for i in range(4):
    for j in range(i+1,4):
        K[i,j] = K[j,i] = (w[i]*J[i,j]+w[j]*J[j,i]-1)/2
for matrix, expected in [(Q(PD), [7,s.Rational(3951,100),
    s.Rational(290527,2000),s.Rational(15333879,40000)]),
    (Q(PV)-K,[s.Rational(4397,200),s.Rational(1143956171,4840000),
    s.Rational(4506212701697,5324000000),s.Rational(905937923038697,1064800000000)])]:
    actual = [matrix[:i,:i].det() for i in range(1,5)]
    assert actual == expected and all(a > 0 for a in actual)
A, b = s.eye(4)-J.inv()*G, J.inv()[:,2]
assert A.det() == s.Rational(12568,13611)
assert s.Matrix.hstack(*[A**k*b for k in range(4)]).det() == s.Rational(1043968,11440338672460347)
a = s.Matrix([1045,775,970,1747,-4674,-3575,-4373,-7445,
              7829,6164,7351,11910,-5820,-4708,-5464,-8476,1620,1344,1516,2264])
rows = []
for n in range(5):
    for i in [0,1,3]:
        rows.append([(J[i,j]-G[i,j] if m == n else -G[i,j] if m > n else 0)
                     for m in range(5) for j in range(4)])
rows += [[G[i,j] for m in range(5) for j in range(4)] for i in range(4)]
C = s.Matrix(rows)
assert C[:,:19].det() == 77996937216 and C*a == s.zeros(19,1)
assert all(sum(a[4*n+i] for n in range(5)) == 0 for i in range(4))
t = s.symbols('t')
def trunc(p):
    p = s.Poly(s.expand(p),t)
    return sum(p.nth(k)*t**k for k in range(3))
def compute(perturb):
    def reward(i, mask):
        members = [j for j in range(4) if mask & (1 << j)]
        if len(members) == 1: return G[i,members[0]]
        if len(members) == 2 and i in members:
            return J[i,next(j for j in members if j != i)]
        if len(members) == 2:
            return (i+2*members[0]+3*members[1]+1) if perturb else 0
        return (7*i-3*mask) if perturb else (-5 if i in members else 0)
    e, u, nu = [0]*4, s.Integer(0), s.Integer(1)
    for n in reversed(range(5)):
        q = [t*a[4*n+i] for i in range(4)]; new = []
        for i in range(4):
            H = s.prod(1-q[j] for j in range(4) if j != i)
            P = Qp = s.Integer(0)
            for mask in range(16):
                if mask & (1 << i): continue
                prob = s.prod(q[j] if mask & (1 << j) else 1-q[j]
                              for j in range(4) if j != i)
                if mask: P += reward(i,mask)*prob
                Qp += reward(i,mask | (1 << i))*prob
            new.append(trunc(P+H*e[i]))
            if i == 2: u = trunc(q[i]*Qp+(1-q[i])*(P+H*u))
        e = new; nu = trunc(nu*s.prod(1-z for z in q))
    return trunc(e[2]-u), trunc(nu+sum(w[i]*e[i] for i in range(4))-1)
D, V = compute(False)
assert D == -1157984156*t*t and V == -s.Rational(5894461073,11)*t*t
Dp, Vp = compute(True)
correction = sum(w[i]*(i+2*j+3*k+1)*a[4*n+j]*a[4*n+k]
                 for n in range(5) for j in range(4) for k in range(j+1,4)
                 for i in range(4) if i not in [j,k])
assert Dp == D and Vp == V+correction*t*t
x = s.symbols('x')
f = 13611*x**4-54692*x**3+81334*x*x-52832*x+12568
assert s.expand(13611*A.charpoly(x).as_expr()) == f
h = s.Poly(x**4+2*x**3-2*x*x-x+1,x,modulus=7)
R = s.rem(s.Poly(x**49-x,x,modulus=7),h)
assert R == s.Poly(-2*x**3-x*x+x+1,x,modulus=7)
assert s.Poly((-2*x*x+2*x-2)*R.as_expr()+(3*x+3)*h.as_expr()-1,x,modulus=7).is_zero
pz = s.expand(f.subs(x,1-x))
assert pz.subs(x,s.Rational(1,3)) == -s.Rational(64,3)
assert pz.subs(x,s.Rational(7,20)) == s.Rational(107691,160000)
assert 4785*519 > 13611*33


# Exact alternative certificate for the full premium ray.
M,t,u,y=s.symbols('M t u y', real=True)
G=s.Matrix([[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]])
J=s.Matrix([[0,-5,M-1,-5],[M-1,0,-5,-5],[-5,-5,0,M-1],[-5,M-1,-5,0]])
w=s.ones(1,4)*G.inv()
K=s.Matrix(4,4,lambda i,j:0 if i==j else (w[i]*J[i,j]+w[j]*J[j,i]-1)/2)
xi=2*t*t-2*s.I*t
B=(1+t*t)*G-xi*J
Delta=s.expand(B.det(method='domain-ge'))
n=(xi*B.adjugate()[:,2]).applyfunc(s.expand)
d=[82*M-423,208*M**3-1224*M*M-5646*M+36039,
128*M**5-560*M**4-6576*M**3-66544*M*M-337330*M+3272259,
768*M**6-2304*M**5-21936*M**4-487680*M**3-453096*M*M-11316306*M-95787]
v=[292*M+3183,1216*M**3-18000*M*M+170772*M+559637,
1152*M**5-28032*M**4+123520*M**3+505680*M*M+5247052*M+24384253,
10368*M**5+88832*M**4+738368*M**3+1987104*M*M-34836004*M-149601193]
Dnum=s.expand(s.re(n[2]*s.conjugate(Delta)))
Vnum=s.expand(w[2]*Dnum+(s.conjugate(n).T*K*n)[0])
scale=-2*t*t*(1+t*t)**4
assert s.expand(Dnum-scale*sum(d[j]*t**(2*j) for j in range(4)))==0
assert s.expand(Vnum-scale*sum(v[j]*t**(2*j) for j in range(4))/11)==0
for p in d+v:
 assert all(c>0 for c in s.Poly(p.subs(M,u+14).expand(),u).all_coeffs())
den=(M-11)*(M-1)*(M*M+8*M+41)
assert s.factor(J.det()+den)==0
A=s.eye(4)-J.inv()*G
b=J.inv()[:,2]
assert s.factor(A.det()-(M**4-60*M*M-942*M-900)/den)==0
cols=[b]
for k in range(3): cols.append((A*cols[-1]).applyfunc(s.factor))
assert s.factor(s.Matrix.hstack(*cols).det(method='domain-ge')-(M-6)**3*(M**3+77*M*M-982*M+2029)/den**4)==0
for p in [M**4-60*M*M-942*M-900,M**3+77*M*M-982*M+2029]:
 assert all(c>0 for c in s.Poly(p.subs(M,u+14).expand(),u).all_coeffs())
print('PASS: matrix and curvature certificates, passive/higher rewards, all-power spectrum, entire M>=14 Fourier/rank certificate')
