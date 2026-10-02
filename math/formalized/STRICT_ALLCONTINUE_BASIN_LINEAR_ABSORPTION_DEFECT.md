# Linear absorption price in a strict all-Continue basin

Author: `CODEX_RAMSEY`

Independent review:

- [ordinary-mathematics falsification by CODEX_EULER](../feedback/CODEX_RAMSEY__STRICT_ALLCONTINUE_BASIN_LINEAR_DEFECT__BY_CODEX_EULER.md)
- [successor-linked path addendum review by CODEX_EULER](../feedback/CODEX_RAMSEY__STRICT_ALLCONTINUE_BASIN_LINEAR_DEFECT__BY_CODEX_EULER__PROPOSITION_3.md)
- [whole-packet gate by CODEX_EULER](../feedback/STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT__BY_CODEX_EULER__PACKET_GATE.md)

## Exact statement

Let `I` be a nonempty finite player type and let

```text
reward : {S : Finset I // S.Nonempty} -> Payoff I
```

be a quitting reward table.  Fix `M>=0` such that

```text
|reward(S)_i| <= M
```

for every nonempty coalition `S` and player `i`.  For a product root `q`,
write

```text
q_i = (q i true).toReal,
A(q) = quittingRootAbsorptionMass q
     = 1 - product_i (1-q_i).
```

For a tail payoff vector `V`, put

```text
Def(V,q) = quittingRootTotalNashDefect reward V q.
```

Let `K` be a nonempty compact set of payoff vectors.  Assume:

1. there is `delta>0` such that, for every `V in K` and every `i`,

   ```text
   reward({i})_i + delta <= V_i;                    (1)
   ```

2. for every `V in K`, the all-Continue root is the unique exact product-root
   Nash equilibrium against `V`:

   ```text
   IsεQuittingRootNash reward V 0 q
     -> q = quittingAllContinueRoot.                (2)
   ```

Then there are an open payoff set `N`, with `K subset N`, and a constant
`c>0` such that, for every `V in N` and every independent Boolean product
root `q`,

```text
c * A(q) <= Def(V,q).                               (3)
```

Consequently, for `epsilon>=0`,

```text
IsεQuittingRootNash reward V epsilon q
  -> A(q) <= (Fintype.card I / c) * epsilon          (4)
```

whenever `V in N`.

For any finite row family `t=0,...,L-1`, if every `V_t in N`, every
`epsilon_t>=0`, and every `q_t` is an `epsilon_t`-Nash root against `V_t`,
then

```text
sum_t A(q_t) <= (Fintype.card I / c) * sum_t epsilon_t.   (5)
```

If, in addition, every reward and displayed tail coordinate is bounded in
absolute value by one common `C>=0`, then for every player `i`,

```text
sum_t |quittingRootSuccessorPayoff reward V_t q_t i - V_t i|
  <= (2*C*Fintype.card I/c) * sum_t epsilon_t.       (6)
```

The length `L` is arbitrary.  The controlled quantity is the aggregate
declared error, not the maximum row error.

The assumption in (5) that every tail is already in `N` can be bootstrapped
from the terminal node when the rows form an exact-successor path.  The set
`N` may be chosen bounded.  Then there are `C>0` and `rho>0` such that `C`
bounds every reward coordinate and every payoff coordinate on `N`, and

```text
dist_infinity(V,K)<rho -> V in N.                    (P1)
```

Let `V_0,...,V_L` be payoff vectors and suppose that, for `0<=t<L`,

```text
epsilon_t>=0,
IsεQuittingRootNash reward V_{t+1} epsilon_t q_t,
V_t = quittingRootSuccessorPayoff reward V_{t+1} q_t.   (P2)
```

Put `E=sum_{t<L} epsilon_t`.  If

```text
dist_infinity(V_L,K)<rho/2,
E < c*rho/(4*C*Fintype.card I),                      (P3)
```

then every `V_t` lies in `N` and

```text
sum_{t<L} A(q_t) <= (Fintype.card I/c)*E,
max_{t<=L} ||V_t-V_L||_infinity <= (2*C*Fintype.card I/c)*E < rho/2.  (P4)
```

Equivalently, any such path which reaches a node outside `N` pays the fixed
aggregate-error toll

```text
E >= c*rho/(4*C*Fintype.card I).                    (P5)
```

Thus for arbitrary path lengths, terminal distance to `K` and aggregate
error tending to zero force both the whole path diameter and aggregate
absorption to tend to zero.

## Conjecture-facing change

The maintained exact-basin boundary in
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md)
explicitly stopped at approximate roots whose absorption tends to zero.  A
fixed positive-incidence moat does not see that regime.  Inequality (3)
closes precisely this local scalar gap: throughout a smaller strict
all-Continue neighborhood, *every* amount of absorption, including vanishing
absorption, is charged linearly by literal root Nash defect.

Thus an arbitrary-length approximate stack wholly inside this neighborhood
cannot carry a fixed absorption charge or fixed total Bellman motion while
its aggregate root error tends to zero.  Moreover, (P1)--(P5) show that an
exact-successor stack ending near the compact basin cannot hide a nonlocal
excursion under a vanishing aggregate error budget.  The surviving
Finite-four route must enter from nonlocal data not covered by such a path or
must spend the fixed aggregate toll.  An isolated incoming row whose
continuation tail is already outside `N` remains possible.

## Probability, information, and agency

Each `q` is an ordinary independent product of private Boolean Quit/Continue
marginals at one quitting row.  No public correlation is introduced.
`A(q)` is the probability that at least one player Quits at that row.  The
root Nash defect compares the displayed mixture with both pure date-zero
endpoint actions for each player; the checked endpoint/root equivalence gives
the stated `epsilon`-Nash convention.

Different rows in (5) need not be probabilistically independent.  The proof
only sums deterministic one-row inequalities.  Nor does (5) assume that the
rows form an executable Bellman path.  When they do, (6) is the corresponding
sum of absolute one-edge motions.  Statements (P1)--(P5) add the exact Bellman
successor relation as an explicit hypothesis; they do not infer it from the
root Nash inequalities.

The abstract theorem is a root-level statement, not an unrestricted
behavioral equilibrium theorem.  In the Finite-four adapter below, the tail
vectors come from terminal-semantic pairs whose envelope coordinates already
use unrestricted behavioral deviations.  That all-behavior semantic meaning
does not enlarge the one-stage root conclusion.

## Proof

For player `i`, define opponent absorption

```text
O_i(q) = 1 - product_{j != i} (1-q_j).
```

Let `s_i=reward({i})_i` and let `Delta_i(V,q)` be the pure
Quit-minus-Continue endpoint difference.  The checked outsider-Never identity
and joining bound give

```text
Delta_i(V,q) = (1-O_i(q))*(s_i-V_i) + J_i(q),
|J_i(q)| <= 2*M*O_i(q).                            (7)
```

The exact coordinate-defect identity is

```text
Def_i(V,q)
 = (1-q_i)*max(Delta_i(V,q),0)
   + q_i*max(-Delta_i(V,q),0).                     (8)
```

### Low absorption

By (1), there is an open neighborhood `G` of `K` on which

```text
V_i-s_i >= delta/2                                 (9)
```

for every player.  Set

```text
a0 = delta / (2*(delta+4*M)).                       (10)
```

The denominator is positive and `0<a0<=1/2`.  If `V in G` and `A(q)<=a0`,
then `O_i(q)<=A(q)<=a0`.  Equations (7), (9), and (10) imply

```text
Delta_i(V,q)
 <= -(1-O_i)*delta/2 + 2*M*O_i
 =  -delta/2 + O_i*(delta/2+2*M)
 <= -delta/4,                                      (11)
```

because

```text
a0*(delta/2+2*M)=delta/4.
```

Using (8), summing over players, and applying the product-union bound
`A(q)<=sum_i q_i` gives

```text
Def(V,q) >= (delta/4)*sum_i q_i
         >= (delta/4)*A(q).                         (12)
```

This argument permits any number of simultaneously active marginals.

### High absorption

Identify the product-root space with the compact cube `X=[0,1]^I`.  On

```text
H = K x {q in X : A(q)>=a0},                        (13)
```

the continuous function `(V,q) |-> Def(V,q)` is strictly positive.  A zero
would be an exact root at a point of `K`; by (2) it would be all-Continue and
would have absorption zero, contradicting (13).  Since `H` is nonempty and
compact,

```text
m = min_{(V,q) in H} Def(V,q) > 0.                  (14)
```

For completeness, the bound persists uniformly off `K` as follows.  The set

```text
B = {(V,q) : A(q)>=a0 and Def(V,q)<=m/2}
```

is closed.  Its projection to the payoff coordinate is closed because the
root factor `X` is compact.  This projection misses `K`; let `G1` be its open
complement.  If `V in G1` and `A(q)>=a0`, then

```text
Def(V,q)>m/2 >= (m/2)*A(q),                         (15)
```

using `A(q)<=1`.

Take

```text
N = G intersect G1,
c = min(delta/4,m/2)>0.
```

Equations (12) and (15) prove (3).

The checked bound

```text
Def(V,q) <= Fintype.card I * epsilon
```

for an `epsilon`-Nash root proves (4).  Summing (4) proves (5).  Finally the
checked one-edge estimate

```text
|Succ(V,q)_i-V_i| <= 2*C*A(q)
```

and (5) prove (6).

### Successor-linked first-exit bootstrap

Intersect `N` with a bounded open neighborhood of the compact set `K`; (3)
remains true on the smaller set.  Choose `C` as in (P1).  Compactness of `K`
and openness of `N` give `rho>0` satisfying (P1).

Assume (P2)--(P3).  Proceed backward from `V_L`.  The terminal node belongs to
`N` by (P1).  Suppose `V_{t+1},...,V_L` have already been admitted to `N`.
For every already admitted edge `k`, equations (4) and the one-edge movement
bound give

```text
A(q_k) <= (Fintype.card I/c)*epsilon_k,
||V_k-V_{k+1}||_infinity
  <= (2*C*Fintype.card I/c)*epsilon_k.               (16)
```

The current edge `t` is also covered because its continuation tail
`V_{t+1}` is admitted before its head.  Hence

```text
||V_t-V_L||_infinity
 <= (2*C*Fintype.card I/c)*sum_{k=t}^{L-1} epsilon_k
 <= (2*C*Fintype.card I/c)*E < rho/2.                (17)
```

Together with `dist_infinity(V_L,K)<rho/2`, the triangle inequality yields
`dist_infinity(V_t,K)<rho`, so (P1) admits `V_t`.  This completes the backward
induction without presupposing locality of the head.  Summing (16) proves
(P4), and the contrapositive gives (P5).

## Actual-data adapter and semantic consumer

### Checked selected-minimum adapter

For a literal four-player reward table with no uniform-equilibrium payoff,

```text
exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`
supplies an executable terminal-semantic carrier pair `(U,B)` with positive
minimum total debt and

```text
reward({i})_i < U_i
```

for all four players.  The same file's

```text
minimumTerminalSemantic_exactNash_eq_allContinue_of_strictSingleton
```

makes all-Continue the unique exact root at `U`.  Taking the compact singleton
`K={U}` and `delta=min_i(U_i-reward({i})_i)>0` therefore supplies the exact
hypotheses above directly from arbitrary data in the no-uniform branch.

### Reviewed whole-minimum-fiber adapter

The independently reviewed Proposition 4 now archived in
[`FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md`](../formalized/FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md)
strengthens the source to the compact prescribed-payoff projection `K` of
*all* global-minimum carrier pairs, with one uniform strict singleton gap and
unique all-Continue exact roots on all of `K`.  The theorem therefore gives a
single `N,c` uniform over the whole minimum fiber.

The consumer is the approximate, vanishing-incidence obligation named in
`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`: equations (4)--(6) show
that a local approximate connector has absorption and total movement bounded
by its aggregate declared root error.  Equations (P1)--(P5) additionally
remove the prior assumption that every path node is already local: terminal
proximity plus a sufficiently small aggregate budget prevents the first
exit.  At zero error, every row is literally all-Continue, recovering the
checked exact-basin path rigidity.

## Source and novelty audit

The proof uses the following checked declarations.

- `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` and
  `quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean` give (8) and the
  `epsilon` conversion.
- `quittingRootEndpointDifference_eq_outsiderNever` and
  `abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass` in
  `UniformEquilibrium/Quitting/Paths/OutsiderNeverGluing.lean` and
  `UniformEquilibrium/Quitting/Boundary/Repair/FixedTailUniformAbsorption.lean`
  give (7).
- `continuous_quittingRootEndpointDifference_simplex` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean` and
  `continuous_quittingRootTotalNashDefect_simplex` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauNashMoat.lean`
  supply the compactness step.
- `abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass` in
  `UniformEquilibrium/Quitting/Debt/Marked/TimeAdvance.lean` gives (6).

The existing `exists_eventually_totalNashDefect_moat_of_unique_allContinue`
and its opponent-incidence variant charge every *fixed positive* incidence
floor, but explicitly provide no linear modulus as incidence tends to zero.
The new content is the low-absorption estimate (10)--(12), composed with the
compact high-absorption moat to produce one linear constant valid at every
scale.  No paper result is invoked or strengthened.

## Boundary tests

### Exact positive test

Take one player, singleton payoff `s=0`, and `K={1}`.  For a root with Quit
probability `q`,

```text
A(q)=q,
Delta=-1,
Def(1,q)=q.
```

All-Continue is the unique exact root and (3) holds with `c=1`.

### Uniqueness is necessary

For two players, set

```text
reward({1})=(0,2),
reward({2})=(2,0),
reward({1,2})=(2,2),
V=(1,1).
```

Both coordinates have strict singleton gap one.  Nevertheless the all-Quit
root is exact: against a surely quitting opponent, each player's Quit and
Continue endpoints both pay two.  Thus `A=1` and `Def=0`, so no positive `c`
can satisfy (3).  This is exactly the failure of hypothesis (2).

### Compact uniform separation is necessary

In the one-player table with singleton payoff zero, take the noncompact tail
set `K=(0,1]`.  All-Continue is the unique exact root at every `V in K`, but

```text
Def(V,q)=V*q,
A(q)=q.
```

No common positive linear constant exists as `V` tends to zero.  This tests
both compactness and the uniform positive gap.

The fixed-table diffuse and cap-defect regressions in
`TerminalSemanticFixedTableDiffuseIncidenceRegression.lean` and
`TerminalSemanticFixedTableCapDefectRegression.lean` have the same relevant
boundary behavior: their smallest singleton-to-tail gap is
`1/(n+2)->0`.  They therefore do not satisfy (1) with one positive `delta` and
do not contradict the theorem.

## Lean handoff

The narrowest useful formalization is an abstract theorem over a compact
`K : Set (Payoff I)`:

```text
exists_open_linearAbsorptionDefect_of_compact_strictAllContinue
  (hKcompact : IsCompact K)
  (hKnonempty : K.Nonempty)
  (hdelta : 0 < delta)
  (hgap : forall V in K, forall i,
      delta <= V i - reward (quittingSingletonTerminal i) i)
  (hunique : forall V in K, forall q,
      IsεQuittingRootNash reward V 0 q -> q=quittingAllContinueRoot) :
  exists N c, IsOpen N /\ K subset N /\ 0<c /\
    forall V in N, forall q,
      c*quittingRootAbsorptionMass q <=
        quittingRootTotalNashDefect reward V q
```

Useful dependencies are exactly the declarations listed in the source audit,
plus `quittingRootOpponentAbsorptionMass_le_absorptionMass`,
`quittingRootAbsorptionMass_le_sum_quitRates`, and the closed-projection
pattern already used in `TerminalSemanticPlateauNashMoat.lean`.  The high
branch should use `QuittingRootSimplex I`, not raw PMFs, for compactness.

Then add a short `epsilon` corollary and a Finite-four corollary instantiated
first at the checked singleton minimum `K={U}`.  The whole-minimum-fiber
corollary should wait on formalization of the corresponding source adapter in
`../formalized/FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md`; it must not be assumed as a
structure field.

The successor-linked corollary should be a separate theorem over finite
arrays or lists.  Its hypotheses must store both `IsεQuittingRootNash` against
`V_{t+1}` and the exact equality `V_t=Succ(V_{t+1},q_t)`.  Formalize the
backward induction from the terminal index; do not put prior membership
`V_t in N` into the path structure.

Finite sanity tests should include the one-player identity and the two-player
nonunique all-Quit table above.

## Checked Lean realization

The generic open-basin theorem is
`exists_open_linearAbsorptionDefect_of_compact_strictAllContinue` in
`UniformEquilibrium/Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`.
That file also checks the bounded thickening, one-root and finite-family
absorption estimates, aggregate successor-motion estimate, and vanishing-
error limit. The successor-linked first-exit bootstrap and its fixed error
toll are respectively
`successorPath_mem_and_absorptionSum_le_of_linearDefect` and
`sum_error_ge_of_successorPath_exists_not_mem_linearBasin` in
`UniformEquilibrium/Quitting/Paths/StrictAllContinueBasinSuccessorPath.lean`.

The same-table no-uniform `Fin 4` adapter is
`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`.
It applies one modulus to the complete compact prescribed-payoff projection
of the global minimum carrier fiber. The result has `M`, `L`, `A`, and `C`:
the consumer is the checked root/path obstruction, not a uniform-payoff
construction. It still requires local continuation tails and aggregate
declared error tending to zero; it produces no path and does not control a
nonlocal incoming tail.

## Scope and nonclaims

- The theorem produces no root, Bellman edge, or chronological path.
- It does not exclude an incoming edge whose continuation tail is outside
  `N`, even if that edge's head lies in `N`.  The path bootstrap applies only
  when the terminal node is near `K` and the entire aggregate error satisfies
  (P3).
- It controls aggregate one-stage absorption, not a selected marginal,
  player-deleted clock, terminal atom, orientation, or conditioned posterior.
- The free row-family conclusion (5) assumes every displayed tail lies in
  `N`.  The successor-linked conclusion (P1)--(P4) instead derives locality
  from terminal proximity and the aggregate-error threshold (P3).  Both
  conclusions control charge by the *sum* of declared errors; a nonvanishing
  or nonsummable aggregate error budget is not excluded.
- Terminal-semantic carrier and unrestricted behavioral-deviation meaning
  enter only through the Finite-four adapter.  The abstract root theorem is
  neither a behavioral equilibrium nor a uniform-equilibrium theorem.
- No nonlocal payoff return, paid-row repayment, or full conjecture closure is
  claimed.
