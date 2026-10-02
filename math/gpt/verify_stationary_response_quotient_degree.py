#!/usr/bin/env python3
"""Exact algebraic checks for STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE.md.

Requires Python 3.10+ and SymPy. Run:
    python verify_stationary_response_quotient_degree.py

No numerical solver is used. This checks the finite matrix, polynomial,
interval-sign, and Farkas certificates. It does not mechanize Brouwer degree,
the intermediate value theorem, or the infinite-game proof in the manuscript.
Coalitions are bitmasks; the table contains only nonempty coalitions.
"""
from itertools import combinations
import sympy as sp


def require(condition: bool, message: str) -> None:
    if not bool(condition):
        raise AssertionError(message)


def eq(lhs, rhs, message: str) -> None:
    require(sp.expand(lhs - rhs) == 0, message)


def main() -> None:
    R = sp.Rational
    players = tuple(range(4))
    rows = {
        1: (1, 4, 0, 0), 2: (4, 1, 0, 0), 3: (2, 2, 3, 2),
        4: (0, 0, 1, 4), 5: (1, 1, -1, 1), 6: (1, 1, -1, 1),
        7: (-2, -2, 0, 1), 8: (0, 0, 4, 1), 9: (1, 0, -1, 3),
        10: (0, 1, -1, 3), 11: (-2, -2, 2, 1), 12: (3, 3, 4, -1),
        13: (-1, 2, 2, -1), 14: (2, -1, 2, -1), 15: (1, 1, 4, 4),
    }
    reward = {mask: tuple(map(sp.Integer, row)) for mask, row in rows.items()}
    swap = (1, 0, 2, 3)
    def image(mask):
        return sum(1 << swap[i] for i in players if mask & (1 << i))
    for mask in reward:
        for i in players:
            require(reward[image(mask)][swap[i]] == reward[mask][i],
                    f"Whole-table automorphism fails at {(mask, i)}")
    s = sp.Matrix([reward[1 << i][i] for i in players])
    require(s == sp.ones(4, 1), "Own singletons")
    G = sp.Matrix(4, 4, lambda i, j: reward[1 << j][i] - s[i])
    require(G == sp.Matrix([[0,3,-1,-1],[3,0,-1,-1],
                           [-1,-1,0,3],[-1,-1,3,0]]), "Singleton matrix")
    E = sp.Matrix([[1,0,0],[1,0,0],[0,1,0],[0,0,1]])
    A = sp.Matrix([[3,-1,-1],[-2,0,3],[-2,3,0]])
    require(G*E == E*A, "Orbit-sum intertwining")
    require(G.det() == 45 and A.det() == -15, "Determinants")
    require(G.inv() == sp.Matrix([[2,7,3,3],[7,2,3,3],
                                 [3,3,2,7],[3,3,7,2]])/15, "Full inverse")
    require(A.inv() == sp.Matrix([[9,3,3],[6,2,7],[6,7,2]])/15, "Quotient inverse")
    require(all(z > 0 for z in G.inv()) and all(z > 0 for z in A.inv()),
            "Strict inverse positivity")
    require(G.inv()*sp.ones(4,1) == sp.ones(4,1), "Full positive test root")
    require(A.inv()*sp.ones(3,1) == sp.ones(3,1), "Quotient positive test root")
    print("PASS: paired recipient symmetry; orbit-sum matrix; exact inverses and determinants.")

    # Count freedoms for the new two-recipient condition, not full-table symmetry.
    pair_coordinates = {(mask, i) for mask in reward if mask.bit_count() >= 2 for i in (0,1)}
    count = 0
    while pair_coordinates:
        mask, i = next(iter(pair_coordinates))
        pair_coordinates.discard((mask, i))
        pair_coordinates.discard((image(mask), swap[i]))
        count += 1
    outsider_count = 2*sum(mask.bit_count() >= 2 for mask in reward)
    require(count == 11 and outsider_count == 22 and count+outsider_count == 33,
            "Thirty-three free nonsingleton coordinates")
    # Alter just an outsider coordinate: the paired condition survives, full symmetry fails.
    changed = dict(reward)
    changed[5] = (sp.Integer(1),sp.Integer(1),sp.Integer(17),sp.Integer(1))
    require(changed[5][2] != changed[image(5)][2], "Whole-table symmetry is destroyed")
    require(all(changed[image(mask)][1]-s[1] == changed[mask][0]-s[0] for mask in reward),
            "Centered two-recipient identity survives the arbitrary outsider change")

    # Exact unilateral endpoints, without treating the whole orbit as one player.
    q = sp.symbols("q0:4", real=True)
    C = sp.prod(1-z for z in q)
    alphas, Qs, Hs, Ds = [], [], [], []
    for i in players:
        alpha = sp.prod(1-q[j] for j in players if j != i)
        Q, H = sp.Integer(0), sp.Integer(0)
        for mask in range(16):
            if mask & (1 << i):
                continue
            weight = sp.prod(q[j] if mask & (1 << j) else 1-q[j]
                             for j in players if j != i)
            Q += weight*reward[mask | (1 << i)][i]
            if mask:
                H += weight*reward[mask][i]
        alphas.append(alpha)
        Qs.append(sp.expand(Q)); Hs.append(sp.expand(H))
        Ds.append(sp.expand((1-alpha)*Q-H))

    # The direct, undiscounted stationary identity and origin linearization.
    zero = {z: 0 for z in q}
    shift = sp.symbols("shift", real=True)
    for i in players:
        Rlive = q[i]*Qs[i]+(1-q[i])*Hs[i]
        eq((1-C)*(Qs[i]-Hs[i])-alphas[i]*Rlive, Ds[i],
           f"Direct stationary Bellman identity, player {i}")
        eq(Ds[i].subs(zero), 0, f"Origin value, player {i}")
        for j in players:
            eq(sp.diff(Ds[i],q[j]).subs(zero), -G[i,j], f"Origin derivative {(i,j)}")
        eq((1-alphas[i])*(Qs[i]+shift)-(Hs[i]+(1-alphas[i])*shift), Ds[i],
           f"Terminal-row-shift cancellation in residual {i}; not strategic equivalence")
    xx, yy, zz = sp.symbols("xx yy zz", real=True)
    fixed_sub = {q[0]:xx,q[1]:xx,q[2]:yy,q[3]:zz}
    eq(Ds[0].subs(fixed_sub),Ds[1].subs(fixed_sub),"Full three-variable raw partition identity")
    print("PASS: 33-coordinate raw class; whole-table symmetry unnecessary; exact partition identity.")

    x, y = sp.symbols("x y", real=True)
    sub = {q[0]: x, q[1]: x, q[2]: y, q[3]: 0}
    Dsub = [sp.expand(z.subs(sub)) for z in Ds]
    f = 3*x**3-10*x**2+12*x-2
    F = 4*x**2*y**2-5*x**2*y+x**2-4*x*y**2+3*x*y-3*x+y
    D3 = (9*x**4*y**2-13*x**4*y+4*x**4-22*x**3*y**2+34*x**3*y
          -12*x**3+15*x**2*y**2-18*x**2*y+5*x**2+4*x*y+2*x-2*y**2-3*y)
    for i, expected in enumerate([F, F, -x*f, D3]):
        eq(Dsub[i], expected, f"Stationary residual {i}")
    eq(Qs[0].subs(sub), 1+x-4*x*y, "Active payoff 0")
    eq(Qs[1].subs(sub), 1+x-4*x*y, "Active payoff 1")
    eq(Qs[2].subs(sub), (x-1)*(3*x-1), "Active payoff 2")
    eq(Hs[3].subs(sub), 4*y-6*x*y+x*x*y+2*x*x, "Passive absorbing contribution")
    print("PASS: direct stationary identity, singleton linearization, all stationary residuals and payoffs.")

    # Rational sign bounds imply the two IVT roots and uniqueness on this box.
    xl, xu, yl, yu = R(197,1000), R(1,5), R(1,2), R(3,5)
    require(f.subs(x,xl) < 0 < f.subs(x,xu), "Cubic endpoint signs")
    # f'=9x^2-20x+12 >= -20*xu+12 = 8.
    require(-20*xu+12 == 8, "Cubic derivative lower bound")
    F_low = R(1,2)-R(5,2)*x-R(1,2)*x*x
    F_high = R(3,5)-R(66,25)*x-R(14,25)*x*x
    eq(F.subs(y,yl), F_low, "Lower y endpoint formula")
    eq(F.subs(y,yu), F_high, "Upper y endpoint formula")
    require(F_low.subs(x,xl) < 0 and F_high.subs(x,xu) > 0,
            "Endpoint sign bounds (both polynomials decrease for x>0)")
    Fy = sp.diff(F,y)
    eq(Fy, -8*x*(1-x)*y-5*x*x+3*x+1, "F_y identity")
    Fy_lower = -8*R(4,25)*yu-5*xu*xu+3*xl+1
    require(Fy_lower > 0, "F_y rectangle lower bound")

    # Discard specified negative monomials and bound retained terms monotonically.
    positive = sum(term for term in sp.Add.make_args(D3)
                   if term.as_coeff_Mul()[0] > 0)
    negative_discarded = sp.expand(D3-positive+2*y*y+3*y)
    require(all(c <= 0 for c in sp.Poly(negative_discarded,x,y).coeffs()),
            "Discarded D3 monomials are nonpositive for x,y>=0")
    D3_upper = positive.subs({x:xu,y:yu})-2*yl*yl-3*yl
    require(D3_upper == R(-8269,15625) and D3_upper < -R(1,2),
            "Inactive endpoint strict upper bound")

    A0 = 6*x**3-15*x*x+12*x-1
    B0 = 8*x*x*y-5*x*x-8*x*y+3*x+1
    C0 = 8*x*y*y-10*x*y+2*x-4*y*y+3*y-3
    J = sp.Matrix([[sp.diff(Ds[i],q[j]).subs(sub) for j in range(3)]
                   for i in range(3)])
    require(J.applyfunc(sp.expand) == sp.Matrix([[0,C0,B0],[C0,0,B0],[-A0,-A0,0]]),
            "Full individual active-coordinate Jacobian")
    eq(J.det(), -2*A0*B0*C0, "Active Jacobian determinant")
    require(-15*xu*xu+12*xl-1 > 0, "A0 lower bound")
    eq(B0,Fy,"B0 equals F_y")
    require(8*xu*yu*yu+2*xu+3*yu-3 < 0,"C0 upper bound")
    print("PASS: rational IVT sign bounds; inactive slack < -1/2; nonsingular full active Jacobian.")

    # Pure-profile and named raw-class checks.
    movers = [3,3,0,0,2,2,0,0,2,2,0,3,0,1,0]
    gains = [3,3,2,1,1,1,3,1,3,3,2,5,4,4,1]
    for mask, i, gain in zip(range(1,16),movers,gains):
        changed = mask ^ (1 << i)
        require(changed != 0, "All leaving moves retain a nonempty coalition")
        require(reward[changed][i]-reward[mask][i] == gain > 0,
                f"Pure profile toggle certificate at {mask}")
    require(reward[3][0] > s[0] and reward[3][1] > s[1], "Product-low fails at pair 01")
    for i in players:
        require(sum(reward[1 << j][i] for j in players)/4 == R(5,4),
                "Small-hazard singleton-average limit")
    for S in combinations(players,3):
        T = G.extract(S,S)
        require(T.det() != 0 and any(z < 0 for z in T.inv()), "Triple inverse test fails")
    require(not any(G[i,j] <= 0 and G[j,i] >= 0 for i in players for j in players if i != j),
            "No singleton escort edges")

    def row_F(k,mask):
        child = [i for i in players if i != k]
        require(mask != 0 and mask & (1 << k) == 0, "Legal child coalition")
        return sp.Matrix([s[i]-reward[mask][i] for i in child]), s[k]-reward[mask][k]
    def row_J(k,mask):
        child = [i for i in players if i != k]
        require(mask != 0 and mask & (1 << k) == 0, "Legal child coalition")
        return (sp.Matrix([reward[mask | (1 << i)][i]-reward[mask][i] for i in child]),
                reward[mask | (1 << k)][k]-reward[mask][k])
    for k,masks in [(0,[8,10,12]),(1,[8,9,12])]:
        V = sp.zeros(3,1); b = sp.Integer(0)
        for weight,mask in zip([R(4,9),sp.Integer(1),R(2,9)],masks):
            rv,rb = row_F(k,mask); V += weight*rv; b += weight*rb
        require(V == sp.Matrix([0,0,-R(14,9)]) and b == 1, f"Farkas certificate for deletion {k}")
    require(row_J(2,9) == (sp.Matrix([0,-2,0]),sp.Integer(3)), "Farkas deletion 2")
    require(row_J(3,1) == (sp.Matrix([0,-2,-1]),sp.Integer(3)), "Farkas deletion 3")
    print("PASS: all pure profiles fail; product-low/triple/escort tests fail; four exact deletion-LP duals.")
    # Literal canonical single-pivot table; no assertion of general strategic equivalence.
    shifts = sp.Matrix([0,1,1,1])
    canonical = {mask:tuple(row[i]-shifts[i] for i in players) for mask,row in reward.items()}
    sc = sp.Matrix([canonical[1 << i][i] for i in players])
    require(sc == sp.Matrix([1,0,0,0]), "Canonical own singleton vector")
    require(sp.Matrix(4,4,lambda i,j:canonical[1 << j][i]-sc[i]) == G,
            "Canonical singleton comparison matrix")
    require(all(canonical[image(mask)][1]-sc[1] == canonical[mask][0]-sc[0] for mask in reward),
            "Canonical centered paired-recipient identity")
    require(canonical[1][0] != canonical[2][1], "Canonical table is not swap-symmetric")
    for i in players:
        Qnew = Qs[i]-shifts[i]
        Hnew = Hs[i]-(1-alphas[i])*shifts[i]
        eq((1-alphas[i])*Qnew-Hnew,Ds[i],f"Canonical stationary residual {i}")
        eq(q[i]*Qnew+(1-q[i])*Hnew,
           q[i]*Qs[i]+(1-q[i])*Hs[i]-(1-C)*shifts[i],f"Canonical absorbing payoff {i}")
    for k in players:
        for mask in reward:
            if mask & (1 << k):
                continue
            require(sc[k]-canonical[mask][k] == s[k]-reward[mask][k],"Outside F bound invariant")
            require(canonical[mask | (1<<k)][k]-canonical[mask][k]
                    == reward[mask | (1<<k)][k]-reward[mask][k],"Outside J bound invariant")
            for i in players:
                if i == k:
                    continue
                require(sc[i]-canonical[mask][i] == s[i]-reward[mask][i],"Child F row invariant")
                require(canonical[mask | (1<<i)][i]-canonical[mask][i]
                        == reward[mask | (1<<i)][i]-reward[mask][i],"Child J row invariant")
    require(canonical[3][0] > sc[0] and canonical[3][1] > sc[1],"Canonical product-low failure")
    require(max(abs(z) for row in canonical.values() for z in row) == 4,"Canonical scaling bound")
    print("PASS: literal canonical single-pivot fixture; all residuals, deletion duals, and scaling bound.")
    print("All finite exact checks passed. See the manuscript for the topological and behavioral proofs.")


if __name__ == "__main__":
    main()
