# Capped-clock domination: mathematical review

## Claim and verdict

For a finite quitting game, choose a nonempty proper set of surviving players
S and prescribe Never to every outsider. For each outsider k, choose fixed
nonnegative weights on S. The packet's Never, future-coalition, and joining
inequalities imply that every unilateral outsider gain is bounded by the
weighted gains of separate legal unilateral child deviations. Each child
deviation replaces its stopping time by the minimum of its original time and
an independent clock with the outsider's proposed law.

The core theorem passes independent mathematical review. It gives an actual
strategy extension for an explicitly checkable reward-table class, not merely
a verifier requiring a strategically safe child profile as input. In Fin4,
unconditional three-player existence supplies the child equilibrium. This
does not prove that an arbitrary four-player table satisfies the criterion.

Independent reviews:

- [Strategy and evaluation proof](CAPPED_CLOCK_DEVIATION_DOMINATION__BY_CODEX_DYNKIN_CLOCK.md).
- [Raw class, exact comparisons, and balanced-spine sharpness](CAPPED_CLOCK_DEVIATION_DOMINATION__BY_CODEX_SCHUR_CLOCK.md).

These are ordinary mathematical reviews, not Lean compilation evidence for
the new domination theorem.

## Exact scope

The three families of raw inequalities are necessary and sufficient for the
specified universal pathwise capped-clock gain comparison. Necessity is not
claimed for equilibrium existence or for domination using arbitrary other
child deviations.

For a three-player child there are fifteen scalar payoff inequalities, in
addition to nonnegativity of the three weights. Feasibility is a linear
program for a fixed table. Its dual certifies failure of this particular
compiler, not failure of uniform equilibrium.

The proof covers independent private stopping laws, infinitely many finite
dates, Never, and unattained full best-response suprema. A common clock used
to integrate the pathwise comparison is a proof coupling; the terms on the
right are separate unilateral experiments, not correlated play by several
children. No external randomization is introduced into the game.

With all fifteen inequalities, regret transfers for terminal payoff and
every nonincreasing absorption weight, including each finite horizon and
discounted evaluation. The original child uniform-equilibrium family can
therefore be quietly lifted. Compact selection fixes the outsider payoff
coordinates while preserving the specified child target.

With the Never inequality omitted, the correction is the joint Never mass
times the positive unpaid singleton premium. A positive child singleton
bounds that mass by the corresponding child's terminal regret. Thus fourteen
inequalities suffice for terminal approximate-equilibrium transfer and uniform
payoff existence. This also preserves a specified child target using
target-aware approximation and selection. It is not the same as an
evaluation-by-evaluation bound on the original arbitrary child family.

## What the criterion adds

Setting every weight to zero recovers exactly the existing block-deletion
gate: the outsider's singleton is no larger than zero or any passive child
coalition reward, and joining any child coalition is unprofitable. Nonzero
weights allow a positive outsider gain to be controlled by a child gain
instead. The supplied fixture passes the new criterion and fails the exact
gate for every one-player deletion.

The paired-singleton family is a genuine family conclusion, not the mere
solution of its displayed fixture. It allows arbitrary child nonsingleton
rewards and constrains the outsider coordinates by explicit linear bounds.
The fixed singleton matrix has no escort edge, excluding every balanced
singleton cycle. The raw certificate also survives a reward neighborhood of
the fixture. These comparisons distinguish the family from the named exact
deletion and balanced-singleton criteria; they are not a literature-wide
novelty claim or an exhaustive comparison with all existence theorems.

## Corrections and attribution

1. The finite-search description must specify consecutive calendars starting
   at zero, or explicitly include representatives of gaps in a sparse
   calendar. Testing only supported dates and one final late date can miss
   a profitable intervening response. The supplied script uses consecutive
   response dates; the universal domination proof is unaffected.
2. A balanced spine can start partway through an owner block. The claim that
   merged hazards are uniquely determined applies to complete
   vertex-to-vertex blocks. The initial partial block has at least the
   corresponding complete-block survival, which suffices for the stated
   one-revolution lower bound.
3. The positive-singleton joint-Never debt bound is an existing dependency,
   not new theorem credit. The three-player existence theorem and
   target-preserving terminal selection are dependencies as well.

## Declaration evidence

The coordinator inspected the following declarations at source revision
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`:

- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`).
- `QuittingBlockDispensable` and
  `exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable`
  (`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`).
- `quittingBlockJoinCap` and the quantitative deletion comparison in
  `UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`.
- `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime`
  (`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`).
- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
  (`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`).
- `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`
  and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
- `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`).

The independent class review records the exact finite tests separately from
the universal proof. No Lean build or axiom audit supports the new theorem
in this review.
