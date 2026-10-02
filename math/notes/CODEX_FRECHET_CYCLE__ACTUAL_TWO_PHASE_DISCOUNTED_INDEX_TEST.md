# Actual two-phase discounted equilibria: the collapsing index remains one

Author: CODEX_FRECHET_CYCLE.

Status: completed bounded ordinary-mathematical test, not independently
reviewed or Lean-checked. The calculation uses alternating actual play,
not a two-cycle of a static best-response map. On the Solan–Vieille
boundary completion, nine genuine discounted two-phase branches approach
all Continue and have total local integer index +1. The simplest
two-phase index-count argument therefore forces no new macroscopic exit.
This note stops that argument; no export or higher-period catalogue is
proposed.

## 1. Literal two-phase Bellman system

Fix four players, arbitrary signed rewards r_i(S) at each nonempty first
Quit coalition, and zero live/Never rewards. Before absorption, a public
clock alternates phases 0 and 1. At phase p each player independently
Quits with probability q_i^p. The complete strategy repeats these two
rows; a deviation may instead use ANY history-dependent behavioral law,
including different actions at the two phases and Never.

Let s_i=r_i({i}), Γ_ij=r_i({j})−s_i. For the intended contrary source
use the SAME actual punishment anchor

    c_i=min(0,P_i),       r'_i(S)=r_i(S)−c_i,
    a_i=s_i−c_i≥0,

where P_i is the full terminal punishment value and no original UE
supplies P_i≤s_i. If all s_i≤0, all Never already gives original UE;
otherwise a≠0. The paired benchmark has

    Γ=[0 3 −1 −1; 3 0 −1 −1; −1 −1 0 3; −1 −1 3 0],
    B=Γ⁻¹>0,                   det Γ=45.

For each phase separately, π_i^p(T) is the independent opponent Quit-set
law. Define

    C_p=∏_j(1−q_j^p),           α_i^p=∏_(j≠i)(1−q_j^p),
    Q_i^p=Σ_T π_i^p(T) r'_i(T∪{i}),
    A_i^p=Σ_(T≠∅) π_i^p(T) r'_i(T),
    R_i^p=q_i^p Q_i^p+(1−q_i^p)A_i^p.

For discount complement λ∈(0,1), write d=1−λ. The TWO actual discounted
live values, with the phase index taken modulo two, are

    u^p=d(R^p+C_p u^(1−p)),
    L=1−d²C_0C_1>0,
    N^p=dR^p+d²C_p R^(1−p),        u^p=N^p/L.             (1)

The phase-p pure live endpoints are dQ_i^p and
d(A_i^p+α_i^p u_i^(1−p)). Define the polynomial displacement

    E_i^p=L(Q_i^p−A_i^p)−α_i^p N_i^(1−p).               (2)

Its sign is the sign of the actual Quit-minus-Continue gap. Thus the
complete Bellman conditions are E_i^p≤0 if q_i^p=0, equality if
0<q_i^p<1, and E_i^p≥0 if q_i^p=1, at BOTH phases. Equivalently,

    F_λ(q)=clip_[0,1]^8(q+E(λ,q))=q.                    (3)

Brouwer supplies such a fixed point for every λ. Conversely, (1)–(3)
give Bellman equalities and all pure inequalities for the actual
two-live-state discounted control problem faced by any deviator. Iterating
these inequalities along any complete response leaves a bounded remainder
multiplied by d^n, which tends to zero. Therefore every fixed point is an
actual discounted equilibrium from either starting phase against full
behavioral deviations. No continuation annotation was chosen independently
of the two played rows.

Extend the SAME polynomial E and clipped F to the ambient space ℝ⁸.
For Ω=(-1,2)^8, the image of F lies inside Ω and every fixed point is
in the physical cube. Homotopy to a constant interior point gives

    deg(Id−F_λ,Ω,0)=+1.                                  (4)

This is an eight-dimensional actual equilibrium map. It is NOT
F_onephase composed with itself.

## 2. Contrary-source localization and the surviving phase allocation

At a fixed auxiliary reward bound M', both values in (1) have absolute
value at most M'. This follows directly from discounted expectation, or
by bounding the numerator by
M'[d(1−C_p)+d²C_p(1−C_(1−p))]≤M'L.

Under no original UE every sequence of fixed points with λ→0 has
(q^0,q^1)→(0,0). Otherwise compactness gives a nonzero limiting pair
and bounded limiting values. Its product C_0C_1 is strictly below one.
Passing (1) and the phase-wise inequalities to the limit gives exact
two-phase Nash–Bellman equations. Translation by c gives those equations
for the ORIGINAL reward table. The checked predicate
IsQuittingCyclePunishmentAdmissible holds at every owner because P_i≤s_i,
including a sole owner and its signed Never branch. The exact theorem
`isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle` then gives
original UE, contradiction. This finite-dimensional limit needs no
replacement of the specified endpoint by another germ.

The first-order expansion of (2), identical at both phases, is

    E^p(λ,q)=2λa−Γ(q^0+q^1)
                +O((|λ|+Σ_i,p |q_i^p|)²).              (5)

R0 of Γ excludes unbounded (q^0+q^1)/λ exactly as in the one-phase
source proof: normalize a putative unbounded sequence by its total hazard.
All coordinates are eventually below one, so E^p≤0; a positive limiting
owner uses at least one phase, where equality holds. Formula (5) yields
a nonzero homogeneous complementary vector, contradiction.

For the paired Γ, B>0 further forces every bounded scaled limit to have

    (q^0+q^1)/(2λ)→h=Ba>0.                              (6)

Indeed the limit m satisfies Γm≥a≥0 and m_i(Γm−a)_i=0.
Because a≠0, Γm is nonzero; m=BΓm>0 forces Γm=a. Thus some
coordinates of a may be zero without deleting an owner from (6).

The phase difference is not fixed at first order. Write

    q^0=λ(m+x),       q^1=λ(m−x),        m→h,
    K_ij=r_i({i,j})−r_i({j})   (i≠j),     K_ii=0,
    A=K+Γ/2,
    A_ij=r_i({i,j})−(s_i+r_i({j}))/2,      A_ii=0.        (7)

Here A is a collision-membership matrix, not the phase absorbing
contribution A_i^p in Section 1. The notation is distinguished by indices.
For clarity, let g_i^p=E_i^p/L be the undiscounted endpoint difference
against its actual discounted successor value. Since u^p→a, expansion
of (1) gives

    u^0−u^1=(Γ/2)(q^0−q^1)+O(λ²),
    g^0−g^1=A(q^0−q^1)+O(λ²).                          (8)

One can first obtain u^p−a=O(λ) from an active phase at each owner,
the phase policy difference, and (6); hence the remainders are uniform
along the fixed-point sequences in question.

Every limiting x is in the box [−h,h] and satisfies

    |x_i|<h_i ⇒ (Ax)_i=0,
    x_i=h_i ⇒ (Ax)_i≥0,
    x_i=−h_i ⇒ (Ax)_i≤0.                                (9)

For example, at the upper face phase 0 is used and has g_i^0=0,
whereas g_i^1≤0. Equation (8) gives the upper sign. Thus (9) is the
box fixed-point relation x=clip_[−h,h](x+Ax). It is a consequence
of an actual two-phase system, but its sufficiency still needs the lift
below; a static allocation game alone would not finish this test.

## 3. Actual lift and orientation at a regular allocation

Let x* satisfy (9). Suppose every boundary inequality is strict and the
principal A_JJ is nonsingular for J={i:|x*_i|<h_i}. Empty J is allowed.
Set the unused phase hazard of each boundary owner identically to zero.
Use variables m∈ℝ⁴ and x_J; at a boundary owner set x_i=±m_i,
with the sign of x*_i. Then q^p=λ(m±x) as above.

At each owner choose one active phase and impose E there equal to zero.
Divide these four equations by λ. At each j∈J impose in addition
(E_j^0−E_j^1)/λ²=0. These divided functions extend analytically to
λ=0: (5) is independent of phase, so the difference has no first-order
term. At λ=0 their equations and derivatives have triangular form

    2(a−Γm)=0,
    4(1+Σ_i h_i)(Ax)_J=0          when m=h,

    derivative = [ −2Γ                   0             ]
                 [  *        4(1+Σ_i h_i) A_JJ        ]. (10)

The ordinary implicit-function theorem supplies a unique analytic
solution near (h,x*). Active hazards are positive and below one for small
positive λ. Equation (8) and the strict boundary inequalities make every
unused phase's gain strictly negative. Therefore this is a genuine branch
of fixed points of (3), with both literal values given by (1), not merely
a formal root of (9).

Its local integer fixed-point index is

    sign det Γ · sign det(−A_JJ),                       (11)

where the empty principal contributes +1. Here is the orientation check.
Inactive phase coordinates contribute identity rows to Id−F and can be
removed by simultaneous row/column reordering. At each owner with two
active phases, transform BOTH input coordinates and output rows to their
mean and difference. Each such transform has negative determinant; their
signs cancel. The remaining factors λ, 2 and L/λ tend through positive
values. For the active part of Id−F=−E, divide the mean rows by λ
and difference rows by λ². The limiting Jacobian has diagonal blocks
2Γ and −2(1+Σ_i h_i)A_JJ. Its determinant has precisely sign (11).
There is no extra sign from the number of boundary phase coordinates.

The lift uses the full reward table in (1)–(2), including triples and
the grand coalition. Those coordinates affect the analytic corrections;
they have not been discarded from the equilibrium system.

## 4. Nine actual collapsing branches on the boundary completion

Now use the literal `SolanVieilleBoundary.boundaryReward`. It has
s=(1,1,1,1), the paired Γ, and r_i({i,j})=1 for each member i.
Its ACTUAL auxiliary anchor is c=0: choosing Never gives every owner a
nonnegative payoff against any opponents, since every coalition omitting
that owner pays it 0, 1 or 4. Thus P_i≥0; all-Never opponents give
P_i≤1. Consequently a=h=(1,1,1,1), not a convenient substitute anchor.
Equation (7) becomes

    A=−Γ/2,                   box=[−1,1]^4.

The complete allocation solution set has just the following nine points.
Here ε,η range independently over {−1,+1}.

| Allocation x | Number | Free coordinates J | Local index (11) |
| --- | ---: | --- | ---: |
| (0,0,0,0) | 1 | all four | +1 |
| (ε,−ε,η,−η) | 4 | none | +1 |
| (ε,−ε,0,0), (0,0,η,−η) | 4 | one whole pair | −1 |

At each boundary coordinate, (Ax)_i=(3/2)x_i, so the required
inequality is strict. The full determinant is det A=45/16>0.
Each free pair principal has determinant −9/4. Every displayed point
therefore satisfies the actual-lift hypotheses, giving nine exact
two-phase discounted branches for all sufficiently small positive λ.
Phase labels are retained; phase shifts are distinct points of the
eight-dimensional strategy cube and must both be counted.

The complete 81-face inventory below checks weak boundary inequalities,
then verifies they are all strict. Singular free faces are inconsistent.
Thus no degenerate or extra allocation root was lost from the list.

```python
import itertools
import sympy as S
G=S.Matrix([[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]])
A=-G/2
roots=[]
for state in itertools.product((-1,0,1),repeat=4):
 J=[i for i in range(4) if state[i]==0]
 T=[i for i in range(4) if state[i]!=0]
 x=S.Matrix(state)
 if J:
  M=A.extract(J,J)
  rhs=-A.extract(J,T)*S.Matrix([state[i] for i in T]) if T else S.zeros(len(J),1)
  if M.det()==0:
   assert M.row_join(rhs).rank()>M.rank()
   continue
  z=M.inv()*rhs
  if not all(-1<t<1 for t in z): continue
  for i,t in zip(J,z): x[i]=t
 y=A*x
 if not all(state[i]*y[i]>=0 for i in T): continue
 assert all(state[i]*y[i]>0 for i in T)
 index=S.sign((-A.extract(J,J)).det()) if J else 1
 roots.append((tuple(x),len(J),index))
expected={(0,0,0,0)}
expected.update((e,-e,f,-f) for e in (-1,1) for f in (-1,1))
expected.update((e,-e,0,0) for e in (-1,1))
expected.update((0,0,e,-e) for e in (-1,1))
assert {x for x,_,_ in roots}==expected
assert len(roots)==9
assert sum(index==1 for _,_,index in roots)==5
assert sum(index==-1 for _,_,index in roots)==4
assert sum(index for _,_,index in roots)==1
assert G.det()==45 and A.det()==S.Rational(45,16)
```

Every family of fixed points approaching all Continue has a scaled
subsequence satisfying (6)–(9). Since all nine allocation solutions are
regular with strict unused-phase signs, the local uniqueness in (10)
captures every such fixed point for small λ. Thus the collapsing
cluster's total local degree is

    1+4−4=+1,                                           (12)

exactly the entire ambient degree (4). Any other root set, separated from
this cluster, has total degree zero, not a forced nonzero index.
This does not say no other roots exist: this particular table already
has an exact macroscopic period-two original equilibrium.

## 5. Scope, inspected sources and exact stopping boundary

The actual source bridge is valid: no original UE plus the same-table
normality field excludes every nonzero limiting two-phase root through
`isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle` in
`UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean`. Its exact
predicate `IsQuittingCyclePunishmentAdmissibleAt` is opponent-cycle
contraction OR P_i≤s_i. There is no missing signed sole-owner premise.
The phase-wise translation follows the endpoint shift identity
`isεQuittingRootEndpointNash_zero_shift_iff` and its policy algebra in
`UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`.

The table and pair-member entries were read at `boundaryReward` and
`boundaryReward_pair_eq_one` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`.
Its already-solved macroscopic alternative is
`periodTwo_isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`.
[NOETHER's paired diagnostic](CODEX_NOETHER_SUPPORT__PAIRED_SINGLETON_CYLINDER_AND_GLOBAL_TWO_PHASE_TEST.md)
and [CEDAR's radial-debiasing account](CODEX_CEDAR__DISCOUNTED_RADIAL_DEBIASING.md)
were read to avoid repeating their fixed-family or stationary claims.

The maintained general finite-period warning was checked at
`no_isQuittingBlockCertificate_solanPassivePaddedReward_one` and its
parametric theorem in
`UniformEquilibrium/Quitting/Boundary/Analytic/SolanPassivePaddingBlockNoGo.lean`.
It excludes exact finite absorbing admissible block certificates of every
period for one explicit rational Fin4 table. It is not a no-UE theorem or
a positive approximate-exploitability floor. No universal period-two or
finite-period claim is being made here.

Exact failed implication: enlarging the actual discounted equilibrium
system from one phase to two does NOT, merely by the extra phase freedom
and total-index bookkeeping, create an index deficit forcing a nonzero
zero-discount endpoint on the paired benchmark. The four phase-allocation
directions produce extra actual branches, but their signed contribution
is zero beyond the original +1. A count of the center alone, or a count
of the four pure allocations alone, would be incorrect.

No new raw-matrix exclusion or collision-cylinder consumer has been proved.
The genuinely new input needed would be a global restriction excluding or
connecting some of these ACTUAL branches to a macroscopic usable cycle;
it is not supplied by (4), (9), normality, or the signed count (12).
This bounded degree test is stopped. No further local Taylor-order or
higher-period root inventory is proposed.
