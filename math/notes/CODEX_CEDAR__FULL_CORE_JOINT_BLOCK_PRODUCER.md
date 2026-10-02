# Full-core joint-block producer

Author: `CODEX_CEDAR`
Status: `FIRST-ORDER BARRIER PROVED; MINIMUM-FACE ROUTE ALREADY DISPATCHED TO ATOM/DELETION`

Tested conjecture-closing thesis, now killed at the current source boundary:
in a hypothetical four-player counterexample, the
checked LCP gate and three-core elimination force a full normal core whose
normalized singleton matrix is standard Q and has no homogeneous simplex
solution.  The proposed route was to use the positive minimum terminal-semantic debt face
to force a **nonperturbative joint-quitter block**: one reached block whose
conditional face-gap map has a common zero at hazards bounded away from the
all-Continue corner, or a finite sequence of such blocks whose exact semantic
carrier endpoint returns with smaller debt.  The checked stationary or
periodic consumer would then contradict the assumed absence of a uniform
equilibrium payoff.  Section 6 explains why the checked source instead
dispatches this face directly to atomic handoff/player deletion.

Precise universal obligation changed by the next work: derive, from the actual
minimum terminal-semantic carrier and the arbitrary nonsingleton reward rows,
an exact annular face-sign/degree datum or an exact Bellman return.  It must
work for every four-player reward table in the counterexample-facing
standard-Q/no-homogeneous branch.  Independently selected hazard rows and a
certificate for a special completion do not meet this obligation.

Kill criterion: abandon this joint-block/face-degree route if the literal
minimum-debt hypotheses admit a finite reward table for which every compact
hazard rectangle separated from all-Continue has zero degree for the face
numerator and every finite joint-block Bellman word either leaves the
terminal-semantic carrier or returns with debt at least its starting debt.
Failure of shrinking rectangles alone is not a kill criterion; Proposition
3.1 below proves that such failure is unavoidable on the hard branch.

Next concrete question after the source audit in Section 6 is no longer an
annular stationary root.  The checked minimum-face iteration already turns
the only collision-essential solo-owner branch into an atomic handoff or
strict player deletion.  The live universal work is therefore the
chronological atom producer recorded in
`CODEX_CEDAR__VANISHING_ATOM_CHRONOLOGY.md`, or a genuinely different endpoint
route.  I retain the first-order barrier because it rules out a tempting
shrinking stationary shortcut.

Everything below is ordinary mathematics unless a named Lean declaration is
explicitly described as proved in Lean.  No Lean file or export is proposed.

## 1. Self-contained question and semantic contract

Let `I` be a nonempty finite player set and

`r : {S subset I | S nonempty} -> R^I`

be a finite quitting-game reward table.  The desired conclusion is the
existence of one fixed payoff target such that, for every positive accuracy,
some behavioral profile delivers that target and caps every unilateral
behavioral deviation over every sufficiently long finite horizon.  Neither a
stationary Nash calculation nor a supplied finite block is by itself that
conclusion; a named checked consumer must provide the unrestricted-deviation
and fixed-target bridge.

The present route aims first at either:

1. a positive fully mixed stationary face-numerator zero, consumable by the
   conditional-face-gap stationary compiler; or
2. an exact terminal-semantic carrier edge or finite return, consumable by the
   existing periodic/chronological compiler.

The two outcomes are alternatives.  I do not identify a stationary hazard
root with an exact chronological return.

## 2. Refreshed source boundary

The following declarations and definitions were inspected directly.

- `quittingFaceNumerator`, `sigmaValue`, `excludedValue`, and
  `continueMassExcl` are in
  `UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean` and
  `UniformEquilibrium/Quitting/Cycles/CyclicWeightRowDichotomy.lean`.
  The numerator is

  `(1-c_i(p))*sigma_i(p)-excluded_i(p)`.

- `weightOfReward` in
  `UniformEquilibrium/Quitting/Bellman/Finite/HazardRowBridge.lean` extends the
  nonempty reward table by zero at the empty coalition.
- `normalizedSoloMatrix` in
  `UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean` has
  entries

  `M_ij = r({j})_i-r({i})_i`.

- `HasHomogeneousSimplexSolution` in
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`
  abbreviates the normalized singleton-LCP feasibility predicate from
  `MathUE/LinearProgramming/SingletonLCP.lean`.
- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` and
  `exists_uniformEquilibriumPayoff_of_normalCore_card_three` are proved in
  Lean in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`.
  Thus a hypothetical four-player counterexample has full normal core; the
  formerly pursued three-owner cycle is already eliminated in a stronger
  ambient theorem.
- `exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff` is
  proved in Lean in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`.
  It supplies the counterexample-facing positive minimum-debt face used by the
  thesis, but it does not itself supply a joint-block face zero.
- `exists_uniformEquilibriumPayoff_of_conditionalFaceGap` and its arbitrary
  coordinatewise-box hypotheses are in
  `UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGap.lean`.
  This is a checked consumer for a supplied sign datum, not a universal
  producer.

The full-core example files were also checked narrowly.  The literal
`deadlockMatrix` completion has an exact positive-debt return orbit in
`DeadlockChargedReturn.lean`; reduced singleton lassos retain positive debt in
`DeadlockReducedSingletonLassoBarrier.lean`; and special nonsingleton
completions admit exact joint blocks in `DeadlockJointBlockEquilibrium.lean`
and `DeadlockRationalPolyhedralBlock.lean`.  These are evidence that joint
rows are the missing mechanism in that example, not a universal adapter from
arbitrary full-core data.

No narrow symbol or phrase search found an existing declaration giving the
first-order expansion below.

## 3. Universal small-hazard barrier

Fix a player `i`.  For a hazard vector `p in [0,1]^I`, put

```text
q_i = sum_{j != i} p_j,
A_i = 1 - product_{j != i}(1-p_j),
s_i = r({i})_i,
b_ij = r({j})_i,
M_ij = b_ij-s_i.
```

Let `B >= 0` bound the absolute value of every terminal reward coordinate.
Write `N_i(p)` for `quittingFaceNumerator (weightOfReward r) p i`.

### Proposition 3.1: exact quadratic remainder bound

For every hazard vector in the unit cube,

```text
|N_i(p) + sum_{j != i} M_ij p_j| <= 4 B q_i^2.        (3.1)
```

In particular, the complete first-order term at all-Continue depends only on
the normalized singleton matrix.  Every nonsingleton reward row enters at
quadratic order.

#### Proof

The quantities in the source definitions have direct independent-clock
interpretations.  `A_i` is the probability that at least one opponent quits;
`sigma_i` is the expected payoff when `i` quits; and `excluded_i` is the
unconditional contribution from nonempty opponent quitting coalitions when
`i` continues.  Add and subtract `A_i s_i` and the linear singleton sum:

```text
N_i(p) + sum_j M_ij p_j
 = A_i (sigma_i-s_i)
   + s_i(A_i-q_i)
   + (sum_j p_j b_ij-excluded_i).
```

All sums in this proof are over opponents of `i`.

First, conditioning on the nonempty opponent event and using the reward bound
gives

```text
|sigma_i-s_i| <= 2 B A_i.
```

Since `0 <= A_i <= q_i`, the first term is at most `2 B q_i^2`.

Second, the first two Bonferroni bounds give

```text
0 <= q_i-A_i <= sum_{j<k} p_j p_k <= q_i^2/2,
```

so the second term has absolute value at most `B q_i^2/2`.

For the third term, the exact singleton mass of owner `j` is

```text
w_j = p_j product_{k != i,j}(1-p_k).
```

The union bound yields

```text
sum_j (p_j-w_j)
 <= sum_j p_j sum_{k != i,j} p_k
 <= q_i^2.
```

The probability of at least two opponent quitters is at most
`sum_{j<k}p_jp_k <= q_i^2/2`.  Hence the difference between the linear
singleton sum and the exact excluded contribution is at most
`3 B q_i^2/2`.  Adding the three estimates proves (3.1).  This proof uses no
sign assumption on any reward row.  ∎

### Corollary 3.2: no common face zero near all-Continue

Assume there is no simplex vector `lambda` with `M lambda=0`.  Define the
compact separation constant

```text
kappa = min_{lambda in simplex(I)} max_i |sum_j M_ij lambda_j|.
```

Then `kappa>0`.  If all face numerators vanish at a nonzero hazard vector `p`
and `t=sum_j p_j`, Proposition 3.1 gives

```text
kappa <= 4 B t.
```

Consequently `t >= kappa/(4B)` and, when `n=|I|`,

```text
max_j p_j >= kappa/(4Bn).                              (3.2)
```

Here `B>0` follows automatically: if `B=0`, then `M=0` and a simplex kernel
exists.

#### Proof

Normalize `lambda_j=p_j/t`.  From `N_i(p)=0`, (3.1), and `q_i<=t`,

```text
|sum_j M_ij lambda_j| <= 4 B t
```

for every `i`.  Minimize the left maximum over the simplex.  Compactness and
the assumed absence of a zero give `kappa>0`; the pigeonhole estimate gives
(3.2).  ∎

### Corollary 3.3: application to the counterexample-facing full core

If the normal core is all players and the checked gate supplies
`not HasHomogeneousSimplexSolution M`, then no simplex vector satisfies
`M lambda=0`: such a vector would have zero, hence nonnegative,
singleton-LCP residual and would satisfy complementarity identically.  Thus
Corollary 3.2 applies to every hypothetical four-player counterexample.

This is a genuine universal obstruction.  A stationary common-zero producer
on the hard branch cannot be obtained by sending every hazard to zero and
treating joint collisions as a vanishing perturbation.  It must make a
nonperturbative jump into the hazard cube.  The result does **not** say that a
root exists there, and it does not obstruct a chronological block whose
hazards are small at different reached times.

## 4. Proved and unproved separation

Proved here in ordinary mathematics:

- the explicit quadratic expansion bound (3.1);
- the quantitative exclusion radius (3.2);
- no homogeneous simplex-LCP solution implies the stronger absence of a
  simplex kernel needed for the exclusion radius; and
- the arbitrary nonsingleton reward table affects a stationary face numerator
  only at second and higher order at all-Continue.

Checked Lean facts used as source boundaries are listed in Section 2.  The
ordinary propositions above have not been formalized in Lean.

Unproved:

- the positive minimum terminal-semantic debt face supplies a nonzero degree
  or coordinate face signs outside the exclusion radius;
- arbitrary full-core nonsingleton rewards admit a joint-block Bellman edge;
- such an edge returns exactly to its tail or decreases terminal debt; and
- either construction reaches a checked fixed-target, all-behavior consumer.

## 5. Objections and current interpretation

1. `No homogeneous simplex solution` is used only to rule out `M lambda=0`.
   The converse is neither asserted nor needed.
2. The separation constant depends on the actual singleton matrix and need
   not be uniform across games.  This is sufficient to forbid a shrinking
   root sequence for one fixed alleged counterexample.
3. The face numerator is independent of player `i`'s own hazard, but the
   common-zero system still involves all opponent coordinates.  The proof
   keeps `q_i` separate from total mass `t` until the final bound.
4. The special deadlock joint-block completions are diagnostic only.  Their
   nonsingleton inequalities are not consequences of standard Q, full core,
   or the terminal semantic minimum currently inspected.

The next useful source-level question is therefore not another small-hazard
ansatz.  It is whether the positive minimum-debt face fixes the sign or degree
of the quadratic collision tensor on the annulus `t >= kappa/(4B)`.

## 6. Minimum-face source audit and pivot

The proposed next step in the preceding sentence is not the closest available
source interface.  A refreshed narrow search found the dedicated checked
module
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonTightMinimumFaceIteration.lean`.
It already develops the collision-essential branch of
`quittingTerminalSemantic_face_stratum_alternative` much further than the
generic face numerator does.

For a singleton-tight unique positive-debt owner `o`, that module proves in
Lean:

- `isZeroQuittingRootNash_solo_of_singletonTightMinimumFace`: a controlled
  positive solo-owner rate is exact Nash against the prescribed coordinate;
- `quittingSingletonTightMinimumFace_iterate`: every finite fixed-row prefix
  stays on the same minimum face and preserves every debt coordinate;
- `tendsto_quittingSingletonTightMinimumFace_iterate`: the prescribed vector
  washes out to the owner's singleton reward vector;
- `singletonTight_debt_eq_punishmentGap` and
  `singletonTight_soloReward_neg`: the surviving debt is exactly the owner's
  punishment-value moat, and its own singleton reward is strictly negative;
  and
- `QuittingTerminalExploitabilityWitness.singletonTight_atomicHandoff_or_playerDeletion`:
  the whole face yields either a strict atomic owner toggle with an outsider
  deviation or the same positive terminal exploitability gap on a strictly
  smaller nonempty player type.

The exact outsider inequality behind the iteration is, for solo-owner hazard
`h` and outsider `j`,

```text
(1-h) r({j})_j + h r({o,j})_j
  <= (1-h) t_j + h r({o})_j.
```

Thus the minimum face does expose genuine pair-coalition data.  But the
checked iteration consumes it as a solo deterrence row and dispatches the
remaining obstruction to atomic handoff/player deletion; it does not produce
an annular common face-numerator zero.  Replacing this exact dispatch by an
unmotivated four-coordinate degree argument would move away from the current
universal boundary.

This kills the minimum-face/annular-degree route as the main thesis at the
current source boundary.  Proposition 3.1 remains useful negative structure:
even if a later atomic or paid-row construction tries to close through a
stationary face zero, it must enter the hazard cube nonperturbatively.  No
universal producer is claimed in this note.
