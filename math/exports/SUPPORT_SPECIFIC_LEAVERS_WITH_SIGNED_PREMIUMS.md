# Support-specific leavers with signed participant premiums

## 1. Raw criterion and uniform-equilibrium conclusion

A finite quitting game has a finite player set I. At each live date,
players independently choose Quit or Continue. The first nonempty
quitting coalition S absorbs at a prescribed vector r(S)∈ℝ^I, paid
at every subsequent date. Live-stage rewards and perpetual continuation
pay zero. Past actions are public. Strategies and unilateral deviations
are arbitrary behavioral strategies with independent private randomization;
no external public correlation or bounded-memory restriction is added.

Write s_i=r_i({i}) for player i's own singleton reward. A nonempty
set A⊆I is a **positive-premium trap** when every i∈A has some
coalition S⊆A containing i with r_i(S)>s_i. No singleton set is
a trap. Unions of traps are traps, since each member retains its
coalition witness. Their union is the greatest premium core, with
the empty set used when there are no traps.

Choose a nonempty set P⊆I of protected players. Impose two finite
raw reward conditions:

1. For every p∈P and every coalition S containing p, r_p(S)≥s_p.
   All participant premiums of players outside P may have either sign.
2. For every positive-premium trap A, there is a player p_A∈A∩P
   such that

       r_{p_A}(T∪{p_A}) ≤ r_{p_A}(T)
       for every nonempty T⊆A\{p_A}.                (1)

The designated player may differ from trap to trap. The comparisons
include every larger coalition inside the trap, not only singletons.
Condition 2 is vacuous when there are no traps.

**Uniform-equilibrium theorem.** If I has four players, all s_i≥0,
and conditions 1–2 hold, then the original game has a uniform-equilibrium
payoff. Precisely, there is one vector u such that for every ε>0 there
are a behavioral profile and a horizon threshold N₀ whose expected
average payoff is within ε of u at every N≥N₀, and every complete
unilateral behavioral deviation has expected average payoff at most
u_i+ε. The target u is fixed before ε.

There is a canonical finite test with no protected-set choice: put

    P_max={i∈I: r_i(S)≥s_i for every S containing i}.

Existence of an admissible nonempty P is equivalent to P_max being
nonempty and every trap having a leaver as in (1) belonging to P_max.
Indeed any admissible P is a subset of P_max, so its chosen leavers
still work after enlargement; conversely take P=P_max. This is
finite raw-test packaging, not an additional strategic hypothesis.

The proof first establishes a finite-player analytic exclusion under
STRICT inequalities in (1). It then uses an existing four-player
polynomial obstruction and finally reward closure for weak inequalities.
The weak theorem is strategic; no weak analytic exclusion is asserted.

## 2. Exact roots and the strict analytic theorem

For this section I is any finite nonempty set, and its own singletons
may be signed. Fix M≥0 with |r_i(S)|≤M and B>M. Suppose condition
1 holds and every comparison in (1) is strict for its designated player.

A hazard vector q∈[0,1]^I gives the independent product coalition law
μ_q. Set c(q)=μ_q(∅) and a(q)=1−c(q). At a continuation annotation
v∈ℝ^I, define the literal one-stage successor

    w(v,q)=c(q)v+∑[S≠∅] μ_q(S)r(S).                 (2)

For player i let μ_{−i} be its opponents' product law. Its two
unilateral action endpoints are

    Q_i(q)=∑[T⊆I\{i}] μ_{−i}(T) r_i(T∪{i}),
    C_i(v,q)=μ_{−i}(∅)v_i
             +∑[∅≠T⊆I\{i}] μ_{−i}(T)r_i(T).

The prescribed mixed value is w_i=q_i Q_i+(1−q_i)C_i. An exact
Nash root means w_i≥Q_i and w_i≥C_i for every player. Equivalently,
every supported action is optimal. In particular q_i>0 implies
w_i=Q_i. All annotations are permitted; no behavioral realization of
v is assumed. Finite-game Nash existence gives such a root for every v.

**Strict analytic theorem.** There is no C¹ function H on a neighborhood
of [−B,B]^I satisfying, for every boxed source v and every exact root q,

    H(w(v,q))+a(q) ≤ H(v).                           (3)

The assertion concerns the full product-root relation, including sure
hazards, simultaneous quitting, and all inactive players.

Two elementary estimates will be used. Formula (2) gives

    ‖w(v,q)−v‖∞ ≤ (M+B)a(q)                        (4)

when v is boxed. For any player k, regardless of premium signs,

    Q_k(q) ≥ s_k−2M a_{−k}(q) ≥ s_k−2M a(q),        (5)

where a_{−k} is opponent absorption probability. On opponent
nonabsorption the forced-Quit payoff is s_k; on its complement it
differs from s_k by at most 2M. These prove (4)–(5) directly.

## 3. One fixed protected return domain

Define compact sets

    R_P={v∈[−B,B]^I: v_p≥s_p for all p∈P},
    D_P={v∈R_P: v_i≤s_i for at least one i},
    U=∏[s_i,B],
    L={v∈U: v_i=s_i for at least one i}.

Both D_P and L contain s, and L⊆D_P. Every exact root at ANY
boxed source has successor in R_P. Indeed protected Q_p averages
participant rewards all at least s_p, so Nash gives w_p≥Q_p≥s_p.
Formula (2) keeps all coordinates in the box.

Now let v∈R_P and let q be an absorbing exact root, with nonempty
active support A={i:q_i>0}. Suppose A were a trap. Its designated
p=p_A satisfies

    Q_p−C_p = μ_{−p}(∅)(s_p−v_p)
      +∑[∅≠T⊆A\{p}] μ_{−p}(T)
                       [r_p(T∪{p})−r_p(T)].         (6)

The empty term is nonpositive. A singleton cannot be a premium trap,
so some other member of A has positive hazard. Thus the nonempty
terms have positive total probability, and all their brackets are
strictly negative. Equation (6) is negative, contradicting an active
p and exact Nash. This argument retains every simultaneous opponent
coalition, including those of size greater than one.

Hence A is not a trap. Some active k has r_k(S)≤s_k for every
S⊆A containing k. The forced-Quit endpoint is at most s_k, and
support optimality gives w_k=Q_k≤s_k. The inequality may be strict
for an unprotected player; equality or other singleton floors are not
being inferred. Consequently

    v∈R_P, q absorbing exact Nash  ⇒  w(v,q)∈D_P.    (7)

This is the same D_P for all sources, supports, and root selections.

## 4. A singleton-face inequality and the actual minimum

We first prove the needed face inequality directly. Let x∈U and
x_j=s_j. For i≠j put b_i=0 if x_i>s_i, and otherwise set

    b_i=max(0,r_i({i,j})−r_i({j}));     b_j=0.

For sufficiently small t>0, take the source
v(t)=x+[t/(1−t)]b and the root with hazard t for j and zero for
everyone else. The source is boxed: positive corrections occur only
at singleton-binding coordinates, which lie strictly below B. Player j
is indifferent because its source coordinate and singleton are both
s_j. For another player,

    C_i−Q_i=(1−t)(x_i−s_i)
               +t[b_i+r_i({j})−r_i({i,j})] ≥ 0

for sufficiently small t. The inequality holds directly at a binding
coordinate and by its positive first term at a nonbinding coordinate,
including an upper-box face. The root is therefore exact, with
absorption t and successor

    w(t)=x+t[b+r({j})−x].

Applying (3), dividing by t, and differentiating at x gives

    ∇H(x)·(x−r({j})) ≥ 1.                           (8)

This proof imposes no sign condition on participant premiums.

Assume now that H satisfies (3), and minimize it on compact D_P at x.
If x_i<s_i for some i, all Continue is not Nash there. Finite Nash
existence gives an absorbing root; (7) returns its successor to D_P,
where (3) strictly lowers the minimum. This is impossible. Hence
x≥s, and membership in D_P gives x∈L. Since L⊆D_P, x also
minimizes H on L.

Write J={i:x_i=s_i} and g=∇H(x). If J={j}, every nonbinding
interior partial is zero and every upper-face partial is nonpositive.
The j contribution to g·(x−r({j})) is zero; all upper-face
displacements are positive since B>M. This contradicts (8). Thus
|J|≥2. Increasing one binding coordinate retains another binding
coordinate, so g_j≥0 for each j∈J. Nonbinding interior partials
vanish, and upper-face partials are nonpositive.

Every exact root at x has zero absorption. Indeed an absorbing root
would return to D_P by (7) and strictly lower the attained minimum.
This fact is only about the actual minimum, not arbitrary points of L.

## 5. Two exhaustive minimum perturbations

### An unprotected coordinate binds

Suppose J\P is nonempty and choose k in it. For small ε>0 put
v_ε=x−εe_k. It remains in D_P. Every exact root at v_ε absorbs,
because all Continue gives k the strict gain ε. Choose any such root,
with successor w_ε and absorption a_ε. Return (7) and minimality give

    H(v_ε)−H(x) ≥ a_ε>0.                            (9)

There is no assumed successor floor for k. By (4), (5), and Nash,

    s_k−2M a_ε ≤ Q_k ≤ w_{ε,k}
                    ≤ s_k−ε+(M+B)a_ε.

Therefore ε≤(3M+B)a_ε, and (9) implies

    [H(x−εe_k)−H(x)]/ε ≥ 1/(3M+B)>0.

Its limit is −g_k≤0, a contradiction. This argument uses the same
minimization domain throughout; no compact root selection is required.

### Every binding coordinate is protected

Otherwise J⊆P. Choose k∈J and again set v_ε=x−εe_k. This
source need not belong to R_P, and (7) cannot be applied to it.
Choose an exact root at every such source; all absorb because all
Continue gives k the strict gain ε.

For any sequence ε_n↓0 the hazards lie in a compact finite cube.
The exact Nash graph is closed: its endpoint inequalities are polynomial
in source and hazards. Any accumulation root is therefore exact at x,
where all roots have zero absorption. Hence a_n→0 for every choice
of the roots. No continuous selector or uniform positive absorption
bound is assumed.

The successors still lie in R_P, since protected floors hold at
every exact root at every source. As J⊆P, the minimum derivative
signs give

    g·(z−x)≥0  for every z∈R_P.                     (10)

Binding terms have nonnegative derivative and displacement. Nonbinding
interior terms vanish. Upper-face terms have both derivative and
displacement nonpositive. An unprotected nonbinding coordinate thus
requires no singleton floor.

The protected k floor gives w_{n,k}≥s_k. Combining this with (4),

    ε_n≤(M+B)a_n,
    ‖w_n−v_n‖∞≤(M+B)a_n,
    ‖w_n−x‖∞≤2(M+B)a_n.                             (11)

Differentiability at x, (10), (11), and a_n→0 imply

    H(v_n)−H(x)=−ε_n g_k+o(a_n)≤o(a_n),
    H(w_n)−H(x)=g·(w_n−x)+o(a_n)≥o(a_n).

Both Taylor remainders are on the absorption scale because both
displacements are O(a_n). Dividing (3) by a_n>0 would give
1≤[H(v_n)−H(w_n)]/a_n with limsup at most zero. This contradicts
(3) and completes the strict analytic theorem. The two cases exhaust
the binding set at the same attained minimum.

## 6. Four-player semantic consumer and weak comparisons

The existing four-player polynomial obstruction has the following
consequence used here. For a finite reward bound, if every player is
normal, at least one own singleton is positive, and the original game
has no uniform-equilibrium payoff, there is a rational polynomial H
on a box strictly larger than the reward box with unit absorption
decrease on every exact Nash root and its literal successor. It is
the same table and the same polynomial throughout; no root selection
or strategic realization of continuation annotations is an input.

Nonnegative own singletons imply normality without any assumption on
participant-premium signs. If some singleton is positive, the preceding
obstruction would contradict the strict analytic theorem. If all
singletons are zero, all Never is already an exact equilibrium: a
unilateral quitter against it gets its own singleton zero. This proves
the strict four-player uniform-payoff theorem under condition 1 and
strict (1).

For weak (1), form r^δ by adding δ>0 to every passive coordinate
r_i(S) with i∉S and changing no participant coordinate. Own
singletons, all participant premiums, P_max, and every trap are
unchanged. Each designated weak comparison becomes strict. Hence
r^δ has a uniform-equilibrium payoff for every δ>0, and
‖r^δ−r‖∞≤δ.

For completeness, reward closure preserves the fixed-target quantifier.
Take δ_n↓0 and corresponding uniform targets u_n. They belong to
one common compact payoff box; extract u_n→u. The same behavioral
profiles and transitions are available in both tables. Changing all
terminal rewards by at most δ_n changes any N-stage expected payoff,
prescribed or deviating, by at most δ_n, uniformly over every profile,
deviation, and horizon. Given ε>0, first choose n so that δ_n and
‖u_n−u‖∞ are sufficiently small. Then use one uniform profile for
table r^{δ_n} with sufficiently small error. Its unchanged profile
in r delivers u and caps deviations within ε for every sufficiently
large horizon. The vector u was fixed before ε. Approximating targets
need not be equal. This proves the weak strategic theorem, not a weak
version of analytic inequality exclusion (3).

The semantic declarations supplying this chain are:

- `isQuittingNormalPlayer_of_singleton_nonneg` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`;
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
- `isQuittingFullExactRootPotential_of_robustPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`;
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.

## 7. Exact boundary regressions

### A successor need not satisfy unprotected singleton floors

Take two players, P={0}, and

    r(0)=(0,−1),       r(1)=(0,0),       r(01)=(0,−1).

There are no traps, and the protected player's participant rewards
equal its singleton. At source v=(0,1), the exact root q=(1,0)
has successor (0,−1). Player0 is indifferent; player1's forced Quit
and Continue both pay −1. Thus the successor lies in D_P but not U.
The theorem cannot replace its protected domain by the full singleton
orthant or use w_i≥s_i for every player.

### Perturbed protected sources need not return to D_P

Take three players, P={0,2}, and all seven rewards

    r(0)=(1,0,1),      r(1)=(3,0,1),      r(2)=(0,0,0),
    r(01)=(2,1,1),     r(02)=(1,0,0),
    r(12)=(0,0,0),     r(012)=(1,0,0).

The sole trap is01, with strict protected leaver0 because 2<3.
At x=(1,1,0), the binding set is exactly P. For 0<ε<1 put

    v=x−εe₀,          q=(1/2, ε/(1+ε), 0).

Player0's two endpoints equal (1+2ε)/(1+ε); player1's two
endpoints equal 1/2. Player2's Quit endpoint is zero and its
Continue endpoint is (1+2ε)/(2+2ε)>0. Hence q is exact and its
successor is strictly above every singleton, lying in R_P but not
D_P. The limit root at x still absorbs. The point x is not claimed
to minimize a potential satisfying (3). This example shows exactly
why the second arm requires compactness at the ACTUAL minimum,
not an unconditional assertion about roots near a boundary source.

## 8. A signed proper-three-core coverage fixture

Use four players, P={0,2}, and the complete table below. Coalition
strings denote sets.

| S | r(S) |
|---|---|
| 0 | (1,−1,−1,−1) |
| 1 | (2,0,2,−1) |
| 2 | (2,−1,0,2) |
| 3 | (0,2,−1,0) |
| 01 | (3/2,1,−1,−1) |
| 02 | (1,−1,0,−1) |
| 03 | (1,2,−1,0) |
| 12 | (2,1/2,1/2,1) |
| 13 | (0,0,1,0) |
| 23 | (0,1,0,0) |
| 012 | (1,0,0,−1) |
| 013 | (1,−1/10,−1,0) |
| 023 | (1,−1,0,0) |
| 123 | (3,0,0,0) |
| 0123 | (1,0,0,0) |

Here s=(1,0,0,0), M=3 is a reward bound, and P_max={0,2,3}.
The smaller P={0,2} suffices. The unprotected player1 has the genuinely
negative participant premium r₁(013)−s₁=−1/10. The only positive
premiums are player0 and player1 at01, and players1,2 at12. Therefore
the ONLY traps are01,12,012. Their strict leavers are respectively
0,2,0. For the pair traps the comparisons are 3/2<2 and 1/2<2.
For trap012 all three nonempty opponent-coalition checks are

    r₀(01)=3/2<2=r₀(1),
    r₀(02)=1<2=r₀(2),
    r₀(012)=1<2=r₀(12).

The greatest core is012. The only common trap member is1, which
fails weak leave at01 since r₁(01)=1>−1=r₁(0). The table is
therefore outside both the core-at-most-two and common-leaver criteria,
as well as any version of the support-specific condition requiring
globally nonnegative participant premiums. All Never fails because
singleton0 is positive.

Every pure quitting coalition has a strict toggle improvement. In the
table's order choose players

    1,3,1,0,0,0,2,2,0,0,0,1,1,1,0.

Their gains are respectively

    2,1,3/2,1,1/2,1,1,3/2,1,1,1,21/10,1,1,2.

All withdrawals leave a nonempty quitting coalition.

### Singleton matrix and response-quotient screens

With receiver rows, the centered singleton matrix is

    Γ=[[0,1,1,−1], [−1,0,−1,2],
       [−1,2,0,−1], [−1,−1,2,0]].

Let A be its123 principal block. It has determinant7,

    A⁻¹=[[2,4,1],[1,2,4],[4,1,2]]/7,

and A1=1. For t>0, a solution z≥0 of Az≥t1 with
z_i(Az−t1)_i=0 must have every coordinate positive: a zero
coordinate, the next positive row requirement, and active equality
around the three-cycle give a contradiction. Hence z=t1. At t=0
the same zero-coordinate argument leaves only the zero solution;
an all-positive solution would contradict invertibility.

In the full homogeneous problem a positive pivot h forces child h1
and leaves pivot residual h>0. Pivot zero forces the zero child.
Thus Γ is R₀. At offset (1,−1,−1,−1), any pivot h≥0 forces
child (1+h)1 and pivot residual 2+h. The unique root is therefore
(0,1,1,1), with inactive residual2 and active determinant7. The
regular root-sum formula gives degree+1, so the degree-not-one exit
does not apply. The full matrix is not being called non-Q.

The passive inverse row for child123 is (−1/7,5/7,3/7). Each
other triple has a negative inverse entry: −2 for012 and −2/3
for013 and023. The full inverse is

    [[1,1/7,−5/7,−3/7],
     [1,3/7,−1/7,−2/7],
     [1,2/7,−3/7,1/7],
     [1,5/7,−4/7,−1/7]].

No pair has both off-diagonal entries positive. Principal03 is R₀
but non-Q: its matrix is [[0,−1],[−1,0]], whose homogeneous
problem has only zero and whose offset (−1,−1) is infeasible.

For response invariance, rows in one target block must have equal
singleton row sums over every source block. The following witnesses
exclude thirteen nondiscrete partitions:

| Partition | Compared rows | Source block | Unequal sums |
|---|---|---|---|
| 01 / 2 / 3 | 0,1 | 2 | 1,−1 |
| 02 / 1 / 3 | 0,2 | 1 | 1,2 |
| 03 / 1 / 2 | 0,3 | 1 | 1,−1 |
| 0 / 12 / 3 | 1,2 | 12 | −1,2 |
| 012 / 3 | 0,1 | 012 | 2,−2 |
| 03 / 12 | 0,3 | 12 | 2,1 |
| 0 / 13 / 2 | 1,3 | 2 | −1,2 |
| 02 / 13 | 0,2 | 02 | 1,−1 |
| 013 / 2 | 0,1 | 2 | 1,−1 |
| 0 / 1 / 23 | 2,3 | 1 | 2,−1 |
| 01 / 23 | 0,1 | 01 | 1,−1 |
| 023 / 1 | 0,2 | 1 | 1,2 |
| 0123 | 0,1 | 0123 | 1,0 |

Only the discrete partition and0|123 survive first order. At the
literal root (t,0,0,0) the three child response residuals are
t+t²,t,t. Thus the remaining nontrivial partition fails the full
response-quotient condition too.

### Universal quiet-child debt screens

For thirteen proper children, prescribe the following sure first-date
quitting coalition, and Never if a deviation prevents absorption.

| Child | Sure coalition | Profitable omitted player | Outside gain |
|---|---|---|---|
| 0 | 0 | 1 | 2 |
| 1 | 1 | 3 | 1 |
| 2 | 2 | 1 | 3/2 |
| 3 | 3 | 0 | 1 |
| 01 | 1 | 3 | 1 |
| 02 | 2 | 1 | 3/2 |
| 03 | 03 | 2 | 1 |
| 12 | 1 | 3 | 1 |
| 13 | 3 | 0 | 1 |
| 23 | 2 | 1 | 3/2 |
| 012 | 1 | 3 | 1 |
| 013 | 03 | 2 | 1 |
| 023 | 023 | 1 | 1 |

Every child join and withdrawal comparison is nonprofitable, so these
are full terminal Nash profiles. In particular nonowner1 in child013
gets2 by staying out and only −1/10 by joining. A sole owner who
delays faces all opponents at Never and cannot later exceed its own
nonnegative singleton. Thus the comparisons cover complete behavioral
deviations, not just one-stage deviations. Every prescribed profile
absorbs surely, while the stated omitted player can gain immediately.

For the last child123, repeat solo half-hazards in order3,1,2. Its
three child value vectors are (1,0,0), (0,1,0), (0,0,1). Refine
each half-hazard into n equal hazards α_n=1−2^(−1/n). Values
interpolate between the original endpoints, remain nonnegative, and
preserve exact Continue comparisons. Only the two participant pair12
premiums are positive, each1/2. At every microstage the forced-Quit
payoff is at most its value plus α_n/2. Adding this same error to
all values is a Bellman supersolution. Opponent-only period survival
contracts for each deviator, so its bounded remainder vanishes and
every full child regret is at most α_n/2. Joint Never has probability
zero.

The quiet pivot's payoff remains

    [4r₀(3)+2r₀(1)+r₀(2)]/7=6/7.

Quitting at the first player3 microstage gives exactly one, since
r₀(0)=r₀(03)=1. Its gain1/7 is independent of n. Any purported
universal bound by a fixed finite nonnegative weighted sum of child
deviation debts, plus a fixed multiple of joint Never, would tend to
zero and contradict this gain. Together with the thirteen exact tests,
for each proper child there is an omitted player for whom such a
universal bound fails. This does not exclude a selected-child method.

### Remaining scope comparisons

A joint-pair construction requiring a positive-singleton pivot and two
other passive-singleton rewards at least the pivot's own level must use
pivot0, solo players1,2, and joint03 here. A further prescribed equality
between each joint outsider reward and that outsider's payoff at singleton0
fails: r₁(03)=2 differs from r₁(0)=−1. Alternatively, a raw class
requiring r₀(0j)≥r₀(j) fails for partners j=1,2, whereas choosing
j=3 leaves both other passive-singleton values equal to2>1 and so
fails a two-low-passive-singleton premise. These are literal finite
input distinctions, not failures of a rate search. The signed four-cycle
singleton adapter requiring a positive predecessor in each column
cannot use column0, which harms all three other players.

The named matrix and response inputs for these bounded checks are
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`,
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`,
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`,
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`,
and `SignedFourCycleSingletonData` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`.
The universal quiet-debt quantifier is the one in
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
These checks do not establish failure of every other equilibrium producer.

## 9. A covered full-core branch and implementation boundary

The greatest-core distinction prevents overstating coverage. If the
greatest trap is I itself, its designated protected leaver p satisfies

    r_p(T)≥r_p(T∪{p})≥s_p

for every nonempty opponent coalition T. Such a globally safe quiet
player is already consumed by existing low-player approximation. The
three-player child has profiles with regret at most δ+δ² and joint
Never at most δ whenever one child singleton is nonnegative. Keep
p quiet. On every path where the child eventually quits, joining or
quitting early cannot improve p's payoff; on child Never the excess
is at most max(s_p,0). Thus full regret tends to zero. This includes
the all-zero-child-singleton case.

The exact tracked producers are
`exists_terminalProfile_smallExploitability_smallNever_of_nonnegativeSingleton`
in `UniformEquilibrium/Quitting/Classification/ThreePlayer/NonnegativeSingletonEarlyAbsorption.lean`
and `exists_quietProfiles_smallExploitability_smallNever_of_withdrawalFutureJoinFamily`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`.
Their raw certificate has zero advance/withdrawal weights and Never
residual max(s_p,0). The proper-core fixture above avoids this
composition: r₀(3)=0<s₀=r₀(03)=1. A trap-free or two-player-core
case with the present leaver premise is also a common-leaver case.
The useful new comparison here is the support-specific proper-three-core
region, not a claim to replace those existing exits.

The implementation can reuse `IsQuittingPremiumTrap` in
`UniformEquilibrium/Quitting/Classification/QuittingPremiumCore.lean`
and the signed support upper-endpoint lemma
`quittingRootQuitPayoff_le_singleton_of_support_participantReward` in
`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`.
The existing common-leaver proof already exposes the literal endpoint
sum and nonempty opponent-coalition witness; the new raw adapter chooses
its protected leaver from the ACTUAL support. The new analytic chain is
the protected-set domain R_P,D_P, its exact return, minimum localization,
and the exhaustive same-domain/vanishing-absorption cases above.

The face and movement inputs are
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`,
`abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass`
in `UniformEquilibrium/Quitting/Root/BoundedSuccessorDisplacement.lean`,
and `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`.
The four-player polynomial and reward-closure consumers are those in
Section6. The current single-protected-player domain theorem does not
by itself supply the second minimum arm; that arm must retain its
closed Nash graph and O(absorption) Taylor argument.

The result is ordinary mathematical evidence with explicitly identified
semantic inputs. It does not claim a Lean implementation of the new
protected-set criterion, analytic exclusion under weak leave, or a
solution for arbitrary four-player quitting tables.
