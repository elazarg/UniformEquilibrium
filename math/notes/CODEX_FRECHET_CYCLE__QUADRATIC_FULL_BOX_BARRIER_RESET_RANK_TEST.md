# Quadratic full-box barriers: an exact reset-rank limitation

Identity: CODEX_FRECHET_CYCLE.

Status: bounded negative-route test completed. The general lemma and its
two-parameter application below are proved in ordinary mathematics; neither
has been independently reviewed or checked in Lean. No positive gap table
or counterexample-search progress is claimed. The original table proposed
for this test was discarded because it has a pure terminal equilibrium.

## 1. Exact bounded question and production interface

There are four players. A reward table r assigns a vector r(S) to every
nonempty coalition S. Nonabsorption pays zero. All stopping laws are
private and independent across players. B_i is the supremum against every
complete unilateral behavioral replacement, including Never; it is not
a stationary or finite-response cap.

For a reward bound R>0 use the FULL independent-coordinate box

    Z_R=[−R,R]^4 × [−R,R]^4,
    z=(u,b),       d(z)=max_i(b_i−u_i).

Let T_x be the exact semantic prefix map for every product root
x∈[0,1]^4. Its payoff coordinate is the prescribed root expectation with
continuation u. Its cap coordinate is the maximum of immediate Quit and
Continue with the unrestricted tail cap b_i. Let

    e_Never=(0,(max(s_i,0))_i),       s_i=r_i({i}).

The tested ansatz allows an ARBITRARY real quadratic, including every
linear payoff/cap coefficient, offset, and cross term:

    h(z)=c+ℓ·z+zᵀHz,       H=Hᵀ.

The complete synthesis obligations are

    h(z)≤d(z)                          for every z∈Z_R;
    h(z)≤h(T_x z)                      for every z∈Z_R and x∈[0,1]^4;
    h(e_Never)>0.                                                (Q)

A polynomial is bounded and upper semicontinuous on Z_R. Thus these are
the actual target-free function-barrier obligations, not selected-root
or stationary necessary conditions. A solution of (Q) would give a
positive unrestricted behavioral gap via finite-prefix density.

The exact inspected production home is
`QuittingControllerUpperSemicontinuousBarrier` in
`UniformEquilibrium/Quitting/ControllerTester/FunctionBarrierDuality.lean`.
Its `value` is defined on `QuittingControllerRewardBox`, and `le_prefix`
is universal over that entire box and every `QuittingRootSimplex`.
`quittingControllerTesterValue_functionBarrierDuality` supplies the
target-free consumer. The prefix formula is
`quittingTerminalSemanticPrefix` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.

By contrast, `QuittingControllerClosedInvariantBarrier` in
`UniformEquilibrium/Quitting/ControllerTester/BarrierDuality.lean` asks
for invariance ONLY at points of its chosen closed set. The theorem
below does not apply to a quadratic description of such a set unless
the stronger global function monotonicity in (Q) is separately proved.
The SUM-debt `Certificate.ofPotential` interface in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`
also has a global potential inequality, but is not silently identified
with the MAX-debt closed-set interface.

## 2. General reset-rank lemma

Call a map T:Z_R→Z_R a reset if T(z)=p for every z∈Z_R. Suppose a
collection of permitted resets has points p_0,…,p_m such that:

1. one of these points lies in the ordinary interior of Z_R in R^8;
2. the affine span of the reset points is all of R^8.

### Lemma

Every quadratic h satisfying h(z)≤h(Tz) for every z∈Z_R and every
permitted reset T is constant on the ambient space R^8. In particular,
if it also obeys h≤d on Z_R, its constant value is at most −2R and
it cannot satisfy h(e_Never)>0.

### Proof

For each reset point p_j and every z∈Z_R, monotonicity says

    h(z)≤h(p_j).

Thus every p_j is a global maximizer of h on the entire box, and their
values coincide. Choose an interior reset point p. Since h is quadratic,
its gradient vanishes at p, and its symmetric quadratic part H is
negative semidefinite: small two-sided displacements in every ambient
direction remain in the box. Consequently

    h(p+v)=h(p)+vᵀHv.

Every other reset point has the same value, so

    (p_j−p)ᵀH(p_j−p)=0.

For a negative semidefinite symmetric matrix, vᵀHv=0 implies Hv=0
(diagonalize −H, or use its positive semidefinite square root). Hence
H annihilates every difference p_j−p. These differences span R^8,
so H=0. The already vanishing gradient at p then gives ℓ=0.

Finally evaluate h≤d at u_i=R and b_i=−R for every i. There d=−2R,
so the constant h is at most −2R. QED.

Only one reset point needs to be interior. Boundary reset points still
have the same global maximum value, and the negative-semidefinite kernel
argument applies to their differences. Without an interior point, affine
spanning alone is insufficient: ||z||² has equal global maxima at all
vertices of a centered box but is not constant.

This is a restriction on the full all-root quadratic certificate from
the outset. It is not an argument from a failure to find an equilibrium
or from a finite collection of local reward signs.

## 3. Exact two-parameter application

Let β>0 and a>max(1,β). Indices are cyclic modulo four. Put
ε=(1,1,1,−1), and write t_i(S)=2·1_(i∈S)−1. Define all rewards by

    r_i({j}) = 1                  if i=j=0;
               0                  if i=j≠0;
               a                  if (i,j)=(1,0);
              −a                  for every other i≠j;

    r_i(S) = β ε_i t_i(S)t_(i+1)(S)      if |S|≥2.             (T)

This is a fully specified canonical-singleton family. All rewards lie
in [−a,a], so any R≥a is valid, including the canonical production
reward bound. The all-Never semantic seed is (0,(1,0,0,0)).

For every coalition S with at least two members, its deterministic root
has two or more sure quitters. One unilateral replacement cannot remove
all quitters, so the ENTIRE semantic output is tail-independent:

    p_S=(r_i(S), max(r_i(S),r_i(S△{i})))_i.                  (R)

Formula (R) is the full behavioral cap: both current actions terminate
immediately, not merely a stationary comparison.

Here are nine reset points, with all eight coordinates divided by β and
ρ=a/β>1. Coordinates are ordered (u_0,u_1,u_2,u_3,b_0,b_1,b_2,b_3).

| S | u/β | b/β |
|---|---|---|
| 01 | (1,−1,1,1) | (1,ρ,1,1) |
| 02 | (−1,−1,−1,1) | (−1,1,−1,1) |
| 03 | (−1,1,−1,−1) | (−1,1,1,−1) |
| 12 | (−1,1,−1,−1) | (1,1,−1,1) |
| 13 | (−1,−1,−1,1) | (1,−1,1,1) |
| 23 | (1,−1,1,1) | (1,1,1,1) |
| 012 | (1,1,−1,1) | (1,1,1,1) |
| 013 | (1,−1,−1,−1) | (1,1,1,1) |
| 023 | (−1,−1,1,−1) | (1,1,1,1) |

The eight-row matrix formed by subtracting p_01 from the other rows in
the displayed order has exact determinant

    −256 β^7(a−β) ≠ 0.                                      (D)

Thus these reset points affinely span R^8. The point p_23 has every
coordinate equal to ±β, so is interior to Z_R because β<a≤R.
The lemma therefore excludes EVERY quadratic full-box barrier (Q) for
EVERY table in (T), not merely a bounded coefficient search.

An exact symbolic reproduction of (D), requiring only SymPy, is:

```python
import sympy as s
a, b = s.symbols('a b', positive=True)
U = s.Matrix([
    [1,-1,1,1], [-1,-1,-1,1], [-1,1,-1,-1],
    [-1,1,-1,-1], [-1,-1,-1,1], [1,-1,1,1],
    [1,1,-1,1], [1,-1,-1,-1], [-1,-1,1,-1]
]) * b
B = s.Matrix([
    [b,a,b,b], [-b,b,-b,b], [-b,b,b,-b],
    [b,b,-b,b], [b,-b,b,b], [b,b,b,b],
    [b,b,b,b], [b,b,b,b], [b,b,b,b]
])
Z = U.row_join(B)
D = s.Matrix.vstack(*[Z[i,:] - Z[0,:] for i in range(1,9)])
assert s.factor(D.det()) == -256*b**7*(a-b)
```

The matrix entries come directly from (T) and (R), using a>β>0.
The symbolic determinant was evaluated exactly; no numerical search,
grid, floating-point inequality, or stationary approximation is used
in (D) or in the impossibility proof.

## 4. The rejected fixture and the honest applicability boundary

The first table proposed for this test instead had r_1({0})=−a, with
all singleton outsiders treated identically. It was rejected immediately
after exact coalition enumeration: at S={0,1}, both quitters prefer
their current ±β reward to −a, and outsiders 2 and 3 receive β and
would receive −β by joining. Thus that profile is an exact pure
terminal Nash equilibrium. Its quadratic infeasibility would not be
table-level negative evidence, and no such evidence is claimed.

In the one-sign-changed family (T), player 1 gains a+β by leaving that
coalition. There is in fact no deterministic absorbing-coalition Nash
profile: every pair in the table has some strict positive cap debt;
for |S|≥3, the product of the four signs ε_i t_i t_(i+1) is −1, so
some player has reward −β and can toggle to obtain β. At singleton
0, outsider 2 can join; at singleton 1, 2, or 3, outsider 0 can join.
Their payoff rises from −a to ±β. All-Never is also not Nash because
player 0 can obtain its singleton reward 1.

These elementary checks only remove the initial pure-equilibrium error.
They do NOT prove that (T) lacks a mixed stationary, periodic, or other
behavioral equilibrium, nor that it has a positive gap. No such
classification was attempted. The applicability result is exactly the
quadratic-certificate limitation, independent of the value's sign.

The narrow comparison inspected
`CODEX_HAHN__WEIGHTED_DEBT_AFFINE_BARRIER_NOGO.md` and
`CODEX_HAHN__RAW_MAX_DEBT_SUPERLEVEL_BARRIER_NOGO.md` in full, and the
contact-cone and moment-tight ansatz statements. The weighted-debt result
explicitly leaves arbitrary separate payoff/cap coefficients and offsets
open; the raw-superlevel result concerns a different closed-set grammar.
The reset-kernel observation in
`CODEX_SPINOZA__UNIVERSAL_RESET_KERNEL_AND_POSITIVE_BARRIER_TOPOLOGY_NOGO.md`
already identifies tail-independent nonsingleton roots, but not the
quadratic global-maximizer restriction proved here. These are ordinary
conference mathematics, not substituted for a production certificate.
The exact-source inspection and bounded search found no prior version of
the reset-rank quadratic lemma; no exhaustive novelty claim is made.

## 5. Checkpoint and stop

The tested all-root quadratic inequalities are infeasible with positive
seed value on the explicit family (T), by an exact ambient-space argument.
This neither refutes nor proves the Fin4 conjecture. It does not obstruct
barriers defined only on a constrained invariant set, and it does not
exclude piecewise or higher-degree functions whose global maximum sets
can have the required reset geometry.

The necessary change of expressive power is precise: a successful
certificate for this family cannot be one globally monotone quadratic
on the full independent payoff/cap box. It must change that function
class or use the genuinely different restricted-set invariance contract.
No degree-raising search, coefficient optimization, new interface,
export, Lean edit, or commit follows from this checkpoint.
