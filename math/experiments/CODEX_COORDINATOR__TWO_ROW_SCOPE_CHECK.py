"""Exact two-row scope checks; ordinary mathematics, not a Lean certificate.

Fixture source: math/notes/CODEX_ROOT__TWO_ROW_CONTINUATION.md.
No searches, files, network, generated data, or scratch dependencies.
Requires Python3 and SymPy. All decisions use exact rational/symbolic bounds.
The stationary gap is a separate retained proof/checker, not rerun here.
"""
from fractions import Fraction as F
from itertools import product, combinations, permutations
from math import isqrt
import sympy as s


def literal_table(delta, epsilon):
    """All60 native rewards from CODEX_ROOT__TWO_ROW_CONTINUATION.md."""
    aa = [[0,1,-6,-F(1,100)], [1,0,-F(3,2),-F(2,5)],
          [-delta,-F(3,5),0,1], [-F(7,100),-epsilon,1,0]]
    jj = [[0,F(1,100),F(27,5),F(1,1000)],
          [F(1,100),0,F(3,20),F(9,25)],
          [delta/10,F(27,50),0,F(1,100)],
          [F(63,1000),epsilon/10,F(1,100),0]]
    z = {(i,1<<i): F(0) for i in range(4)}
    for i in range(4):
        for j in range(4):
            if i != j:
                z[i,1<<j] = F(aa[i][j]+jj[i][j])
                z[i,(1<<i)|(1<<j)] = F(jj[i][j])
    for pair, sign in zip(combinations(range(4),2),(1,-1,1,1,-1,-1)):
        mask = sum(1<<j for j in pair)
        for n,i in enumerate(j for j in range(4) if j not in pair):
            contact = sign*(-1 if n else 1)
            z[i,mask] = F(max(0,-contact))
            z[i,mask|(1<<i)] = F(max(0,contact))
    for i in range(4):
        z[i,15^(1<<i)] = F(1)
        z[i,15] = F(0)
    assert len(z) == 60
    return z


Z = literal_table(F(1,8),F(139,200))
Gamma = s.Matrix([[Z[i, 1 << j] for j in range(4)] for i in range(4)])
J = s.Matrix([[0 if i == j else Z[i, (1 << i) | (1 << j)] for j in range(4)] for i in range(4)])
A = Gamma - J
K = Gamma.inv()
assert all(x > 0 for x in K)
assert max(sum(K[i, j] for j in range(4)) for i in range(4)) < 5
v = -K * A[:, 2]
assert list(v) == [s.Rational(x, 10300929979) for x in (75679478400, 87911025000, 44769477730, 13652082000)]
assert min(v) > 1
for size in (2, 3, 4):
    for S in combinations(range(4), size):
        assert Gamma.extract(S, S).det() != 0
assert Gamma.det() > 0
assert all(Gamma[i, i ^ 1] > 0 and all(Gamma[i, j] < 0 for j in range(4) if j not in (i, i ^ 1)) for i in range(4))
assert all(x > 0 for x in K * s.ones(4, 1))

# For EVERY normalized a>=0 with a^T Gamma>=0, put h^T=a^T Gamma.
# Then a^T=h^T K, ||h||_1>1/5, hence J_a({2})=h^T v>1/5.
# All other terms at odds (eta,eta,1,eta) have total magnitude below 1/5.
for i in range(4):
    for B in range(1, 16):
        if B >> i & 1:
            continue
        delta = Z[i, B | (1 << i)] - Z[i, B]
        assert abs(delta) <= (6 if B.bit_count() == 1 else 1)
eta = F(1, 200)
assert 21 * eta + 6 * eta**2 + eta**3 < F(1, 5)
print('PASS: all admissible adaptive ledgers have positive odds polynomial')

# Literal punishment value is one: all participant rewards >=1, and all
# opponents Never cap every response at own-singleton reward one.
assert all(Z[i, B] >= 0 for i in range(4) for B in range(1, 16) if B >> i & 1)

def gain(i, q):
    """Quit minus Continue against continuation vector (1,1,1,1)."""
    out = F(0)
    for B in range(16):
        if B >> i & 1:
            continue
        p = F(1)
        for j in range(4):
            if i != j:
                p *= q[j] if B >> j & 1 else 1 - q[j]
        out += p * (Z[i, B | (1 << i)] - Z.get((i, B), 0))
    return out

# A root with a sure owner has one of 65 patterns in {0,1,mixed}^4.
# The 61 patterns with <=2 mixed owners reduce to rational linear equations.
counts = {'pure': 0, 'one_mixed': 0, 'two_mixed_no_interior': 0, 'two_mixed_failed_inequality': 0}
candidates = []
for pattern in product((0, 1, 'm'), repeat=4):
    if 1 not in pattern:
        continue
    mixed = [i for i in range(4) if pattern[i] == 'm']
    if len(mixed) > 2:
        continue
    q = [F(0) if x == 'm' else F(x) for x in pattern]
    if len(mixed) == 1:
        # This coordinate's own mixing does not enter its gain.
        assert gain(mixed[0], q) != 0
        counts['one_mixed'] += 1
        continue
    if len(mixed) == 2:
        valid = True
        for i, j in (mixed, mixed[::-1]):
            q0 = q[:]
            q0[j] = F(0)
            b = gain(i, q0)
            q0[j] = F(1)
            c = gain(i, q0) - b
            # A flat zero equation would require a different analysis.
            assert b != 0 or c != 0
            if c == 0 or not 0 < -b / c < 1:
                valid = False
                break
            q[j] = -b / c
        if not valid:
            counts['two_mixed_no_interior'] += 1
            continue
        assert all(gain(i, q) == 0 for i in mixed)
    gains = [gain(i, q) for i in range(4)]
    failures = [(i, gains[i]) for i in range(4) if
                (pattern[i] == 0 and gains[i] > 0) or
                (pattern[i] == 1 and gains[i] < 0)]
    assert failures, (pattern, q, gains)
    if mixed:
        counts['two_mixed_failed_inequality'] += 1
        candidates.append((pattern, q, failures))
    else:
        counts['pure'] += 1
assert sum(counts.values()) == 61
print('PASS: all61 lower-dimensional sure-root patterns', counts)
for candidate in candidates:
    print('Rejected candidate:', candidate)

# Four full-support patterns remain. Verify all algebraic identities used
# in the accompanying scope review.
q = s.symbols('q0:4')
g = [s.factor(gain(i, q)) for i in range(4)]
assert s.expand(g[1].subs(q[0], 1) - (2*q[3]*(1-q[2])-1)) == 0
assert s.expand(8*g[2].subs(q[0], 1) - (7*q[1]*(1-q[3])-9*q[3]+1)) == 0
assert s.expand(g[0].subs(q[1], 1) - (2*q[2]*(1-q[3])-1)) == 0
assert s.expand(200*g[3].subs(q[1], 1) - (339*(1-q[0])*(1-q[2])-200)) == 0
assert s.Rational(200,339) > s.Rational(1,2)
x = s.symbols('x')
assert s.expand(g[3].subs(q[2], 1) - (2*q[0]*(1-q[1])-1)) == 0
assert s.expand(2*g[1].subs(q[2], 1) - (q[0]*q[3]-5*q[0]-q[3]+3)) == 0
sub2 = {q[0]: x, q[1]: 1-1/(2*x), q[2]: 1, q[3]: (3-5*x)/(1-x)}
poly2 = 9*x*x+5*x-5
assert s.factor(g[0].subs(sub2) + poly2/(x*(x-1))) == 0
assert s.factor(g[1].subs(sub2)) == 0
assert s.factor(g[3].subs(sub2)) == 0
num, den = map(s.factor, s.together(g[2].subs(sub2)).as_numer_denom())
assert s.expand(den + 80*x*(x-1)) == 0
assert s.rem(num, poly2, x) == (176290*x-92572)/81
assert poly2.subs(x, s.Rational(1,2)) < 0
assert poly2.subs(x, s.Rational(13,25)) > 0
assert 176290*s.Rational(13,25)-92572 < 0
# poly2 has exactly one positive root, in (1/2,13/25); its sure gain is negative.
assert s.expand(g[2].subs(q[3], 1) - (2*q[1]*(1-q[0])-1)) == 0
assert s.expand(100*g[0].subs(q[3], 1) - (101*(1-q[1])*(1-q[2])-100)) == 0
assert s.Rational(100,101) > s.Rational(1,2)
print('PASS: all4 full-support sure-root patterns; no sure punishment root')

# One finite date with independent half hazards, then Never, defeats every
# universal strict payoff-deficit selector. Each nonempty B has probability1/16.
surplus = [F(sum(Z[i, B] for B in range(1, 16)), 16)-F(1,16) for i in range(4)]
assert surplus == [F(2203,4000), F(157,800), F(11,40), F(11,50)]
assert min(surplus) > 0
print('PASS: one-date profile strictly exceeds every own level', surplus)

# Every proper child has an exact pure child Nash law with a profitable
# omitted join. With a date-zero quitter, only Quit/Continue at that date
# affects a deviator; a sole quitter against Never gets own1 or Never0.
badpairs = {0: 6, 1: 9, 2: 10, 3: 5}
quiet_rows, margins = [], []
for child in range(1, 15):
    players = [i for i in range(4) if child >> i & 1]
    if len(players) == 1:
        B = child
    elif len(players) == 2:
        B = 1 << players[0] if child in (3, 12) else child
    else:
        B = badpairs[next(i for i in range(4) if not child >> i & 1)]
    assert B & child == B and B
    for i in players:
        if B >> i & 1:
            others = B ^ (1 << i)
            margins.append(Z[i,B]-Z[i,others] if others else 1+Z[i,B])
        else:
            margins.append(Z[i,B]-Z[i,B|(1<<i)])
    outsider = next(i for i in range(4) if not child >> i & 1
                    and Z[i,B|(1<<i)] > Z[i,B])
    joining = Z[outsider,B|(1<<outsider)]-Z[outsider,B]
    quiet_rows.append((child,B,outsider,joining))
    margins.append(joining)
assert len(quiet_rows) == 14 and min(margins) == F(1,100)
assert all(J[i,j] > 0 for i in range(4) for j in range(4) if i != j)
assert all(Z[i,B] >= 0 for i in range(4) for B in range(1,16)
           if B.bit_count() >= 2)
for S in combinations(range(4),3):
    principal = Gamma.extract(S,S)
    assert principal.det() > 0 and all(principal.inv()[i,i] < 0 for i in range(3))
print('PASS: all14 universal quiet-child obstructions, margin>=1/100; triple inverses')

# Positive-P cone obstruction is independent of reference-grand choices.
assert [Z[i,3] for i in range(4)] == [F(1,100),F(1,100),0,1]
# All positive matrices send this nonzero nonnegative vector into their
# strict inner cone, contradicting the required outside-coordinate collar.

# Symbolic triple spectral factors, for the complete literal parameter family.
d,e,t = s.symbols('d e t')
AA = s.Matrix([[0,1,-6,-s.Rational(1,100)],
               [1,0,-s.Rational(3,2),-s.Rational(2,5)],
               [-d,-s.Rational(3,5),0,1],[-s.Rational(7,100),-e,1,0]])
JJ = s.Matrix([[0,s.Rational(1,100),s.Rational(27,5),s.Rational(1,1000)],
               [s.Rational(1,100),0,s.Rational(3,20),s.Rational(9,25)],
               [d/10,s.Rational(27,50),0,s.Rational(1,100)],
               [s.Rational(63,1000),e/10,s.Rational(1,100),0]])
point = {d:s.Rational(1,8),e:s.Rational(139,200)}
assert (AA+JJ).subs(point) == Gamma
weights = [(s.Rational(18,5),3*d/2),(s.Rational(7,250),e/100),
           (s.Rational(21,50),d/100),(s.Rational(6,25),3*e/2)]
for S,(kh,kl) in zip(combinations(range(4),3),weights):
    determinant = (t*AA.extract(S,S)+JJ.extract(S,S)).det()
    factor = (t+s.Rational(1,100))*(kh*(t-s.Rational(9,10))**2+kl*(t-s.Rational(1,10))**2)
    assert s.expand(determinant-factor) == 0
    assert kh.subs(point)>0 and kl.subs(point)>0
assert Gamma.det() == s.Rational(10300929979,16000000000)
assert min(K) == s.Rational(84234000,10300929979)
assert F(139,200) < F(737,1000)+F(3,50)*F(1,8) == F(1489,2000)
# Necessary reciprocal cone-ratio bounds for the two crossing matchings.
assert F(1,8)*F(139,200) < 1
assert F(1,100)*F(3,2) < 1
assert Z[2,14] == Z[3,13] == Z[0,7] == Z[1,11] == 1
assert 1 > F(1,8)/8 and 1 > F(1,100)/8
print('PASS: four spectral factors, positive inverse, pair-cone bounds, old frontier')

# All24 conditional-average roles. Positive recipient scales of control
# rows are absorbed into alpha,shift. This tests the stronger raw class,
# whose special case is the dominated-row producer.
reference = literal_table(F(8,5),F(0))
clock = F(7,50)
survivors = []
for perm in permutations(range(4)):
    def w(i,mask):
        mapped = sum(1<<perm[j] for j in range(4) if mask >> j & 1)
        return Z.get((perm[i],mapped),F(0))
    valid, parameters = True, []
    for i in (0,1):
        denom = clock*reference[i,(1<<i)|4]-reference[i,4]
        assert denom > 0
        alpha = (clock*w(i,(1<<i)|4)-w(i,4))/denom
        shift = w(i,4)-alpha*reference[i,4]
        parameters.append((alpha,shift))
        valid = valid and alpha > 0
        for T in range(16):
            if T & (4|(1<<i)):
                continue
            active = (1-clock)*w(i,T|1<<i)+clock*w(i,T|1<<i|4)
            active_ref = alpha*((1-clock)*reference[i,T|1<<i]+clock*reference[i,T|1<<i|4])+shift
            passive = (1-clock)*w(i,T)+clock*w(i,T|4)
            passive_ref = alpha*((1-clock)*reference.get((i,T),F(0))+clock*reference[i,T|4])+shift*(1-(1-clock)*int(T==0))
            valid = valid and active == active_ref and passive == passive_ref
    if valid:
        survivors.append((perm,parameters))
assert survivors == [((0,1,2,3),[(F(1),F(0)),(F(1),F(0))])]
assert reference[2,8]/Z[2,8] == 1
assert reference[2,1]/Z[2,1] == F(64,5) > 1
print('PASS: all24 conditional-average roles; unique identity has incompatible row2 scales')


class Iv:
    """Minimal exact rational interval arithmetic for the fixed-tube check."""
    def __init__(self,lo,hi=None):
        if isinstance(lo,Iv):
            self.lo,self.hi = lo.lo,lo.hi
        else:
            self.lo,self.hi = F(lo),F(lo if hi is None else hi)
        assert self.lo <= self.hi
    def __add__(self,other):
        other=Iv(other); return Iv(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self): return Iv(-self.hi,-self.lo)
    def __sub__(self,other): return self+-Iv(other)
    def __rsub__(self,other): return Iv(other)+-self
    def __mul__(self,other):
        other=Iv(other)
        corners=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return Iv(min(corners),max(corners))
    __rmul__=__mul__
    def __truediv__(self,other):
        other=Iv(other); assert other.lo*other.hi>0
        return self*Iv(1/other.hi,1/other.lo)
    def sqrt(self):
        assert self.lo>=0
        scale=10**60
        lower=isqrt(self.lo.numerator*scale*scale//self.lo.denominator)
        upper=isqrt(self.hi.numerator*scale*scale//self.hi.denominator)+1
        result=Iv(F(lower,scale),F(upper,scale))
        assert result.lo**2<=self.lo and self.hi<=result.hi**2
        return result


# Every role in the actual fixed-tube criterion of REPEATED_PAIR_RAW_REWARD,
# Sections3–4. Fixed endpoint y=12/25 suffices to reject a universal tube guard.
counts = {}
for perm in permutations(range(4)):
    G=[[Z[perm[i],1<<perm[j]] for j in range(4)] for i in range(4)]
    if not all(G[i][i^1]>0 and all(G[i][j]<0 for j in range(4) if j not in (i,i^1)) for i in range(4)):
        counts['singleton signs']=counts.get('singleton signs',0)+1
        continue
    pair=[[F(0) if i==j else Z[perm[i],(1<<perm[i])|(1<<perm[j])] for j in range(4)] for i in range(4)]
    P=[Z[perm[i],sum(1<<perm[j] for j in ([1,2] if i in (0,3) else [0,3]))] for i in range(4)]
    beta={0:(pair[3][0]-G[3][0])/pair[3][0],3:(pair[0][3]-G[0][3])/pair[0][3]}
    D=(1+beta[0])*(1+beta[3])
    p=[pair[0][3]/(1+beta[3]),pair[1][2],pair[2][1],pair[3][0]/(1+beta[0])]
    pp=P[:]
    for i in (1,2):
        pp[i]=((1+beta[0]*beta[3])*P[i]+beta[3]*G[i][0]+beta[0]*G[i][3])/D
    guards=[G[0][1]>=p[0],G[0][2]<=P[0]<=G[0][1],G[3][2]>=p[3],
            G[3][1]<=P[3]<=G[3][2],G[2][0]<=pp[2]<=G[2][3],G[2][3]>=p[2]]
    if not all(guards):
        counts['M0']=counts.get('M0',0)+1
        continue
    failure=None
    for endpoint,t in enumerate((F(1856348,10**7),F(1856349,10**7))):
        y=F(12,25); H=(1-y)*(1-t)
        R={i:G[i][1]*y*(1-t)+G[i][2]*t*(1-y)+P[i]*y*t for i in (0,3)}
        if min(R.values())<=0:
            failure='R positivity'; break
        c=[p[i]-G[i][3-i] for i in range(4)]
        def response(i):
            d=Iv(c[i]+R[i]-p[i]*H)
            return 2*Iv(R[i])/(d+(d*d+4*p[i]*H*R[i]).sqrt())
        r=[response(3),Iv(y),Iv(t),response(0)]
        assert all(0<q.lo<=q.hi<1 for q in r)
        val=G[2][0]*r[0]*(1-r[3])+G[2][3]*r[3]*(1-r[0])+pp[2]*r[0]*r[3]+p[2]*r[1]*(1-r[0])*(1-r[3])-c[2]*r[1]/(1-r[1])
        if endpoint==0 and val.hi<0:
            failure='lower endpoint G2 negative'; break
        if endpoint==1 and val.lo>0:
            failure='upper endpoint G2 positive'; break
    assert failure is not None,(perm,'unclassified fixed-tube role')
    counts[failure]=counts.get(failure,0)+1
assert counts == {'singleton signs':16,'M0':3,'R positivity':2,
                  'upper endpoint G2 positive':2,'lower endpoint G2 negative':1}
print('PASS: all24 repeated-pair fixed-tube roles and positive row scalings',counts)
print('PASS: complete exact scope checker')
