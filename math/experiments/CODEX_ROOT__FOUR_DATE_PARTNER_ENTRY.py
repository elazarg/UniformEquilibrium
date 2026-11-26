"""Check the four incumbent contacts and the entrant's slope in Q(sqrt(5))."""
import sympy as sp

sqrt5 = sp.sqrt(5)
rho = (3 - sqrt5) / 2
h = 1 - rho
threshold = 3 - rho
mate_value = (1 + sqrt5) / 2
u = sp.symbols("u:4")
J, a, b = sp.symbols("J a b")
pair = (J, a, threshold, b)
G = sp.Matrix([[0, -1, 3, -1], [-1, 0, -1, 3],
               [3, -1, 0, -1], [-1, 3, -1, 0]])
base = sp.Matrix(4, 4, lambda i, k: (0, -h, mate_value, 0)[(i - k) % 4])


def clean(value):
    return sp.simplify(sp.expand(sp.radsimp(sp.expand(value))))


def innovation(i, k):
    value = (G[i, k] - base[i, (k + 1) % 4]) * u[k]
    if k == 0:
        value += rho * G[i, 2] + h * pair[i] - base[i, 0]
    return value


def derivative(i, k):
    return sum(rho**ell * innovation(i, (k + ell) % 4)
               for ell in range(4)) / (1 - rho**4)


contacts = [derivative(i, i) - (J if i == 0 else 0) for i in range(4)]
matrix, rhs = sp.linear_eq_to_matrix(contacts, u)
matrix = matrix.applyfunc(clean)
assert clean(matrix.det() + sp.Rational(49, 90) + 7 * sqrt5 / 30) == 0
changes = matrix.inv().applyfunc(clean) * rhs.applyfunc(clean)
slope = ((derivative(2, 0) - threshold * u[0]) / h).subs(dict(zip(u, changes)))
expected = (-50 + 24 * sqrt5 - 4 * sqrt5 * J
            + (9 * sqrt5 - 20) * a + (20 + 9 * sqrt5) * b) / 105
assert clean(slope - expected) == 0
print("Incumbent determinant and all four slope coefficients verified.")

# Verify the prescribed 02|1|2|3 example on the larger rational interval (13/5,3).
x = sp.symbols("x")
low, high = sp.Rational(13, 5), sp.Integer(3)
z = sp.Rational(1, 100)
t1 = sp.Rational(1, 2)
t0 = 1 / (7 - 2*x)
t3 = sp.cancel(t0*x/(1+t0*x))
T = sp.Rational(95, 99)
t2 = sp.cancel((T+t3-(1-t3)*z)/(3+t3-(1-t3)*z))
t = [t0, t1, t2, t3]
U = sp.cancel((t2/(1-t2)-3*t3)/(1-t3))
V = 3*t1-(1-t1)*t2
a = sp.cancel((U+t0+z)/(t0*z)-2)
b = sp.cancel((t0+z-(1-t0)*(1-z)*V)/(t0*z)-2)
values = sp.Matrix([[z,-sp.Rational(2,99),T,-t3+(1-t3)*z],
                    [U,0,0,t2/(1-t2)], [t0*x,-t1,0,0], [0,V,-t2,0]])
join = sp.Matrix(4,4,lambda i,k: (0,-sp.Rational(9,10),1,
                                 -sp.Rational(11,10))[(k-i)%4])
join[2,0] = x


def positive_on_interval(expression):
    numerator, denominator = sp.fraction(sp.cancel(expression))
    for polynomial in (numerator, denominator):
        poly = sp.Poly(polynomial, x)
        assert not poly.is_zero
        for endpoint in (low, high):
            while poly.eval(endpoint) == 0:
                poly = poly.exquo(sp.Poly(x-endpoint,x))
        assert poly.count_roots(low,high) == 0
    assert expression.subs(x,(low+high)/2) > 0


for tk in t:
    positive_on_interval(tk)
    positive_on_interval(1-tk)

for k in (1,2,3):
    for i in range(4):
        assert sp.cancel(values[i,k]-t[k]*G[i,k]-(1-t[k])*values[i,(k+1)%4]) == 0
        if i != k:
            positive_on_interval(values[i,k]-t[k]*join[i,k])
        else:
            assert values[i,k] == 0

pair = [1, a, x, b]
for i in range(4):
    prescribed = (t0*(1-z)*G[i,0] + (1-t0)*z*G[i,2]
                  + t0*z*pair[i] + (1-t0)*(1-z)*values[i,1])
    assert sp.cancel(values[i,0]-prescribed) == 0
    if i in (0,2):
        forced = z if i == 0 else t0*x
        assert sp.cancel(values[i,0]-forced) == 0
    else:
        forced = t0*(1-z)*join[i,0]+(1-t0)*z*join[i,2]-3000*t0*z
        positive_on_interval(values[i,0]-forced)
print("Full upper-interval contact equations and strict guards verified.")

# Independently compute one column at the four-tie corner from incumbent payoffs.
alpha, beta = sp.symbols("alpha beta")
pair = (threshold, alpha, threshold, beta)
u = sp.symbols("p:4")
eq = [derivative(i,i)-(threshold if i==0 else 0) for i in range(4)]
matrix, rhs = sp.linear_eq_to_matrix(eq,u)
pchanges = matrix.applyfunc(clean).inv().applyfunc(clean)*rhs.applyfunc(clean)
subs = dict(zip(u,pchanges))
column = [210*(rho*derivative((k+2)%4,(k+1)%4)+u[k]).subs(subs)
          for k in range(4)]
reference = sp.Matrix([[65-29*sqrt5,25+11*sqrt5,150-78*sqrt5],
                       [10-4*sqrt5,65-29*sqrt5,150-48*sqrt5],
                       [5+sqrt5,10-4*sqrt5,-45+57*sqrt5],
                       [25+11*sqrt5,5+sqrt5,-45+27*sqrt5]])
assert all(clean(actual-want)==0 for actual,want in
           zip(column,reference*sp.Matrix([alpha,beta,1])))
H = sp.Matrix(4,4,lambda i,k: reference[(i-k)%4,2]/210)
ell = sp.Matrix([1,-sp.Rational(1,10),-sp.Rational(1,10),-sp.Rational(1,10)])
bounds = {(0,1): [(80,81),(140,141),(60,61),(61,62)],
          (0,2): [('0.54','0.55'),('2.70','2.71'),('0.40','0.42'),('0.68','0.70')],
          (0,3): [(70,71),(45,46),(32,33),(31,32)]}
for act, bands in bounds.items():
    quiet = [i for i in range(4) if i not in act]
    active = H.extract(act,act).inv()*ell.extract(act,[0])
    slack = H.extract(quiet,act)*active-ell.extract(quiet,[0])
    for val,(lo,hi) in zip(list(active)+list(slack),bands):
        assert sp.Rational(lo) < clean(val) < sp.Rational(hi)
print("Four-tie response matrix and three distinct strict solutions verified.")

for i in range(4):
    assert clean(H[i,i]) < 0
    for j in range(i):
        assert clean(H[i,j]) > 0 and clean(H[j,i]) > 0
        assert clean(H[i,j]*H[j,i]-H[i,i]*H[j,j]) > 0
print("All four diagonal and six strict pair comparisons for degree -3 verified.")
