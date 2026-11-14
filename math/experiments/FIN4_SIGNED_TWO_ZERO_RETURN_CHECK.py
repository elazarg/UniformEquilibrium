"""Exact shallow and deep nonpositive-pair returns, with all behavioral caps.

Run: python math/experiments/FIN4_SIGNED_TWO_ZERO_RETURN_CHECK.py
Requires SymPy. The complete fixed reward table is below. Exact polynomial
identities and Bernstein coefficients certify the example; this is not a
search over arbitrary tables or controllers. The literal game has absorbing
Nash (checked below), so it is not a positive-gap or new UE-class witness.
Proofs: SIGNED_TWO_ZERO_CONTINUATION_REDUCTION.md and
NONPOSITIVE_PAIR_BOUNDARY_RESET_REDUCTION.md in the export queue.
The final guard-gap example is an internal method control described in
math/notes/CODEX_ROOT__ACTUAL_MINIMUM_AND_MIXED_ENDPOINT.md. It is excluded
from small-penalty selected sources by the general bound there.
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


def check_deep_nonzero_cross_fixture():
    """Check the deep-pair fixture independently by coalition enumeration."""
    from fractions import Fraction as F
    from math import prod

    gamma = [[0, 5, -1, -1], [-2, 0, 1, 1], [2, -1, 0, -1], [2, -1, -1, 0]]
    reward = {mask: [F(0)] * 4 for mask in range(1, 16)}
    for j in range(4):
        reward[1 << j] = [F(gamma[i][j]) for i in range(4)]
    entries = [(5, 2, 8), (9, 3, 8), (12, 2, -8), (12, 3, -10),
               (12, 0, 1000), (12, 1, -1000), (3, 0, -512), (3, 1, 1),
               (6, 2, -8), (10, 3, -8), (9, 1, -1000), (9, 2, 100),
               (13, 2, 200), (5, 3, -300), (13, 3, 400)]
    for mask, player, value in entries:
        reward[mask][player] = F(value)

    def root(q, tail):
        """Enumerate opponent coalitions; retain the full response maximum."""
        assert all(0 <= hazard <= 1 for hazard in q)
        u, cap, end, never = tail
        passive, quit, survival = [], [], []
        for i in range(4):
            pp = qq = F(0)
            for mask in range(16):
                if mask & (1 << i):
                    continue
                mass = prod(q[j] if mask & (1 << j) else 1 - q[j]
                            for j in range(4) if j != i)
                pp += mass * (reward[mask][i] if mask else 0)
                qq += mass * reward[mask | (1 << i)][i]
            passive.append(pp)
            quit.append(qq)
            survival.append(prod(1 - q[j] for j in range(4) if j != i))
        joint = prod(1 - x for x in q)
        return ([q[i] * quit[i] + (1 - q[i]) * passive[i] + joint * u[i]
                 for i in range(4)],
                [max(quit[i], passive[i] + survival[i] * cap[i]) for i in range(4)],
                [passive[i] + survival[i] * end[i] for i in range(4)],
                [(1 - q[i]) * never[i] for i in range(4)])

    def diffuse(rates, base_survival, tail):
        """Exact equal-hazard-block limit, including both head-query endpoints."""
        u, cap, end, never = tail
        total = sum(rates)
        drift = [sum(gamma[i][j] * rates[j] for j in range(4)) for i in range(4)]
        joint = base_survival ** total
        surv = [base_survival ** (total - rates[i]) for i in range(4)]
        passive = [F(drift[i], total - rates[i]) * (1 - surv[i])
                   if total != rates[i] else F(0) for i in range(4)]
        return ([F(drift[i], total) * (1 - joint) + joint * u[i] for i in range(4)],
                [max(F(0), passive[i], passive[i] + surv[i] * cap[i]) for i in range(4)],
                [passive[i] + surv[i] * end[i] for i in range(4)],
                [base_survival ** rates[i] * never[i] for i in range(4)])

    all_never = ([F(0)] * 4, [F(0)] * 4, [F(0)] * 4, [F(1)] * 4)
    q0 = diffuse([1, 0, 2, 2], F(9, 10),
                 diffuse([1, 1, 1, 1], F(1, 2), all_never))
    assert q0[0] == [F(2802569, 32000000), F(40951, 250000), 0, 0]
    assert q0[1] == q0[2] == [F(3683, 16000), F(40951, 250000), 0, 0]
    assert q0[3] == [F(9, 20), F(1, 2), F(81, 200), F(81, 200)]
    f = q0[1][1] / (q0[1][1] + 3)
    source = root([f, 2 * f / (1 + f), F(0), F(0)], q0)
    u, cap, end, never = source
    assert cap == end == [F(4657205, 6655216), F(40951, 790951), 0, 0]
    assert u == [F(-10886684947367, 5263949750416), cap[1], 0, 0]
    assert never == [F(337500, 790951), F(187500, 415951), F(81, 200), F(81, 200)]
    t = (15 * cap[1] - 6) / (-1984 + 282 * cap[1])
    assert t == F(4131441, 1557698602) and 0 < t < 1
    entry = diffuse([1, 0, 0, 0], 1 - t, source)
    assert entry[0] == [(1 - t) * u[0], (1 - t) * cap[1] - 2 * t, 2 * t, 2 * t]
    assert entry[1] == entry[2] == [cap[0], *entry[0][1:]] and entry[1][1] > 0
    assert entry[3] == [(1 - t) * never[0], *never[1:]]
    z, y, v = t / 3, 8 * t / (3 - 100 * t), 8 * t / (3 + t)
    assert z > 0 and y > 0 and v > 0
    inner = root([z / (1 + z), F(0), F(0), y / (1 + y)], entry)
    assert all(inner[0][i] == inner[1][i] == inner[2][i] for i in (1, 2, 3))
    assert inner[1][2:] == [0, v] and inner[1][0] == inner[2][0] > 0
    output = root([F(0), F(0), v / (1 + v), F(0)], inner)
    assert all(output[0][i] == output[1][i] == output[2][i] == cap[i] for i in (1, 2, 3))
    assert output[1][0] == output[2][0] > 0 and output[1][0] < cap[0]
    assert output[0][0] > u[0] and all(x > 0 for x in output[3])
    assert prod(output[3]) == (1 - t) * prod(never) / ((1 + z) * (1 + y) * (1 + v))
    assert prod(output[3]) < prod(never)
    pure = root([F(0), F(1), F(1), F(1)], all_never)
    assert pure[0] == pure[1] == [0, 0, 0, 0] and prod(pure[3]) == 0
    print('PASS deep/nonzero-cross source, full-cap reset, strict gain, Never, and absorbing Nash.')

    # Reuse the full coalition and diffuse maps for the disconnected-guard fixture.
    reward = {mask: [F(0)] * 4 for mask in range(1, 16)}
    for j in range(4):
        reward[1 << j] = [F(gamma[i][j]) for i in range(4)]
    b = F(40951, 790951)
    entries = [(5, 2, 8), (9, 3, 8), (12, 2, -8), (12, 3, -10),
               (3, 0, -512), (3, 1, 1), (6, 2, -8), (10, 3, -8),
               (9, 1, -1000), (10, 1, (2247 * b - 1) / 8),
               (11, 1, -1000 - 140625 * b)]
    for mask, player, value in entries:
        reward[mask][player] = F(value)
    source = root([f, 2 * f / (1 + f), F(0), F(0)], q0)
    u, cap, end, never = source
    assert cap == end == [F(4657205, 6655216), b, 0, 0]
    assert u[0] == F(-10886684947367, 5263949750416)

    def excursion(t):
        entry = diffuse([1, 0, 0, 0], 1 - t, source)
        z, y, v = t / 3, 8 * t / 3, 8 * t / (3 + t)
        inner = root([z / (1 + z), F(0), F(0), y / (1 + y)], entry)
        out = root([F(0), F(0), v / (1 + v), F(0)], inner)
        return entry, inner, out

    t0 = F(4131441, 1569983902)
    assert F(1, 500) < t0 < F(1, 250)
    _, bad_inner, bad_out = excursion(t0)
    assert bad_inner[1][1] > bad_inner[0][1]
    assert bad_out[0][1] == b and bad_out[1][1] > b
    assert 6 - 15 * b > 0 and 16 - 18 * b > 0  # Other orientation never returns.

    t = F(1, 200)
    entry, inner, out = excursion(t)
    assert entry[1][1] == F(6567347, 158190200) > 0
    assert all(inner[0][i] == inner[1][i] == inner[2][i] for i in (1, 2, 3))
    assert all(out[0][i] == out[1][i] == out[2][i] for i in (1, 2, 3))
    x = out[1][1]
    assert x == F(1523528233, 36608376084) and 0 < x < b < F(2, 5)
    assert out[1][2:] == [0, 0] and out[1][0] == out[2][0] < cap[0]
    assert out[1][0] == F(67292453077, 102676672448) > 0
    rho = (b - F(2, 5)) / (x - F(2, 5))
    assert rho == F(63739871748, 65599111003) and 0 < rho < 1
    assert F(2, 5) + rho * (x - F(2, 5)) == b
    gain = -F(4, 5) + rho * (out[0][0] + F(4, 5)) - u[0]
    assert gain == F(16611716006668623, 218288126566470824) > F(3, 40)
    assert rho * prod(out[3]) / prod(never) == F(61661756925, 65599111003) < 1
    # For the corrective clock the full pivot cap is max(0,-1+(out_cap+1)*rho^(4/5));
    # 0<rho<1 and out_cap>=0 prove it is <=out_cap<old_cap exactly.
    fp = b / (b + 3)
    pin = [fp, 2 * fp / (1 + fp), F(0), F(0)]
    old_head = root(pin, source)
    direct_clock = diffuse([1, 0, 2, 2], F(1, 2), source)
    changed_head = root(pin, direct_clock)
    assert all(old_head[0][i] == old_head[1][i] for i in (1, 2, 3))
    assert changed_head[1][1] - changed_head[0][1] == (
        (1 - fp) * pin[1] * (direct_clock[1][1] - b)) > 0
    pure = root([F(0), F(1), F(1), F(1)], all_never)
    assert pure[0] == pure[1] == [0, 0, 0, 0]
    print('PASS guard gap, outward correction, >3/40 gain, active-head pin, and Nash boundary.')


check_deep_nonzero_cross_fixture()
