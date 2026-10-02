# CODEX_CEDAR — ergodic recurrence in the punishment-floor Nash--Bellman relation

## Current best attempt

**Status: CLOSED as a distinct frontier route.**  Proposition 1C is a valid,
independently reviewed recurrence adapter, but Proposition 4 shows that its
positive-mean hypothesis already gives unbounded exact punishment-floor
prefix charge and is therefore consumed by the existing checked finite-prefix
compiler.  Under a terminal exploitability witness the checked common prefix
bound forces every invariant law to have zero absorption mean.  Moreover, the
state-local bounded capacity potential sought in the original thesis already
exists in checked form; its documented unresolved seam is semantic boundary
calibration, not recurrence.  The reusable mathematics is retained below.

**Exact reviewable claim.**  Proposition 1C below is an exact recurrent-law
producer.  If the compact punishment-floor exact Nash--Bellman path space has
one ergodic shift-invariant law with positive mean one-row absorption, then the
game has a uniform-equilibrium payoff.  A typical deterministic path has
positive average joint hazard.  Every player-deleted hazard also has positive
average except possibly one owner.  With no exception, the checked path
compiler applies.  With one exception, all opponents Continue almost surely,
the stored value is the owner's singleton column, and any positive-hazard root
is an exact period-one Nash--Bellman cycle.  The checked punishment-completed
solo-cycle compiler applies because the floor carrier supplies the owner's
punishment inequality.  Proposition 1B shows why that punishment completion
is indispensable: the bare selected infinite path can still give a negative
owner a profitable Never deviation.  Proposition 2 identifies the maximal
invariant mean with the subadditive limit of maximal finite-prefix charge.
Proposition 3 gives the exact bounded lower-semicontinuous path bias in the
finite-total-charge branch.  The results are ordinary mathematics, not
checked in Lean.

**Original conjecture-closing thesis (now exhausted).**  Work with the entire compact
punishment-floor predecessor relation rather than a chosen orbit.  Any
nontrivial recurrent invariant law closes the game by Proposition 1C.  If all
invariant laws are supported on all-Continue phantom states, use ergodic
optimization to extract one continuous
Lyapunov/bias function whose strict drift prices every absorbing edge; combine
that bias with exact Nash and the terminal exploitability gap to rule out the
phantom-only alternative.  This is distinct from Simon `F_epsilon` finite
orbits and from the finite-depth floor-admissible chain/source-matching route:
the proposed producer is recurrent occupation of the universal exact
relation, and its negative alternative is a global bias certificate.

**Honest status and main gap.**  The compact floor carrier, closed exact edge
graph, predecessor seriality, and exact-spine deviation compiler are checked
inputs.  Proposition 1C is proved here in ordinary mathematics, using the
standard Birkhoff ergodic theorem and two named checked consumers.  The first
draft incorrectly claimed that the punishment floor is nonnegative;
Proposition 1B falsifies that step.  The later source audit found that
`isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`
handles exactly this negative-owner branch, so the earlier harmed-outsider
seam is now closed.  Noether independently reviewed the corrected base
Propositions 1/1B/2/3 before this Proposition 1C sharpening.  Noether then
independently falsification-audited Proposition 1C and found it valid.
Propositions 2--3 are proved by
the empirical-measure/Fekete argument and an exact tail sum.  The universal
existence of a strategically usable positive-absorption ergodic law is not
proved and cannot hold under the counterexample hypothesis: Proposition 4
reduces it to the already excluded unbounded-prefix branch.  A relation can
have positive transient edges while every invariant law lives on zero-cost
fixed points; seriality alone does not exclude this.

**Universal obligation exposed.**  Under a fixed positive terminal
exploitability gap, every exact floor path has bounded total charge and every
invariant law is all-Continue.  The remaining universal obligation is to
calibrate the canonical capacity potential's surviving boundary against the
positive exact terminal-debt boundary.  This is recorded in the repository as
the capacity/debt boundary-mismatch seam and is pursued, if at all, as a
separate thesis rather than as an ergodic positive producer.

**Kill criterion reached.**  The counterexample interface itself supplies a
common finite bound on every exact floor prefix.  Hence all invariant laws are
all-Continue and the positive recurrent branch cannot be the missing
universal producer.  The canonical state-local bounded potential also already
exists, while its boundary comparison is explicitly open.  Continuing under
the original thesis would duplicate that named obstruction.

**Sections to check.**  Sections 2 (exact source declarations), 3 (path-space
quantifiers), 4 (ergodic producer and necessity of punishment completion), 5
(precise phantom-only obstruction), 6 (finite-prefix identity and bias), and
7 (source overlap and closure verdict).

## 1. Scope

This notebook seeks the positive semantic endpoint for an arbitrary finite
quitting game.  All strategies delivered by the intended compiler are
ordinary behavioral strategies.  The payoff target is the initial terminal
payoff of one deterministic typical path and is fixed before the accuracy.
No stationary, periodic, or bounded-controller completeness assumption is
made.

The route begins only after fixing a finite player type and a reward table.
Rewards, continuation values, and punishment values use the project's
terminal semantics, in which all players Never yields zero.  A single
player's Never deviation need not yield zero when opponents may absorb at a
negative row; punishment values can therefore be negative.  Proposition 1B
keeps this distinction explicit.

## 2. Bounded source and declaration ledger

The narrow lookup inspected only the following declarations and their local
definitions.

- `QuittingNashBellmanPoint`, `IsQuittingNashBellmanEdge`,
  `quittingNashBellmanBox_isCompact`,
  `isClosed_quittingNashBellmanEdgeGraph`, and
  `exists_quittingNashBellmanPredecessor`
  (`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`).
  They give the compact closed predecessor relation from exact one-stage
  mixed Nash existence.
- `quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge` and
  `quittingPunishmentFloor_le_forwardValue`
  (`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`).
  The first fact is the source-relevant invariant-carrier statement: an exact
  Nash predecessor of a tail above the punishment floor remains above it.
- `IsCanonicalExactQuittingNashBellmanSpine` and
  `uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine`
  (`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`).
  The positive clock branch covers unrestricted behavioral deviations; the
  same file's canonical phantom regression shows why arbitrary spine
  selection is insufficient.
- `divergent_opponentClocks_or_positive_exceptionalSuffix` and
  `infinitePath_isUniformEquilibriumPayoff_of_survival_tendsto_zero`
  (`UniformEquilibrium/Quitting/Paths/OpponentClockDichotomy.lean` and its
  imports).  The latter is the checked no-exception consumer used below.
- `QuittingNormalNoHarmSingletonOwner` and
  `exists_uniformEquilibriumPayoff_of_normalNoHarmSingletonOwner`
  (`UniformEquilibrium/Quitting/Classification/LCP/ProjectiveQBarBehavioralDecoder.lean`).
  This checked producer dispatches the exceptional negative owner whenever
  its singleton row weakly dominates every player's own singleton payoff.
- `isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`
  (`UniformEquilibrium/Quitting/Punishment/SoloCycleCompletion.lean`).  This
  checked period-one compiler is the decisive exceptional-owner adapter: a
  positive solo hazard, exact endpoint Nash against the singleton column, and
  the owner's punishment-floor inequality suffice even when that singleton
  payoff is negative and harms outsiders.
- `exists_infiniteChain_of_budgetedFinitePrefixes`
  (`MathUE/Topology/CompactBudgetedPrefixRelation.lean`).  It records the
  stronger cumulative-budget route but does not produce the required finite
  budgets.
- `quittingGame_exists_uniformPayoff_of_unbounded_floorPrefixCharge`
  (`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorFinitePrefix.lean`)
  and `QuittingTerminalExploitabilityWitness.prefixCharge_le`
  (`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean`).
  These checked declarations subsume the positive-invariant-mean branch and
  bound it away under a counterexample witness.
- `quittingPunishmentFloorReachablePotential_isBoundedPotential` and
  `quittingPunishmentFloorReachablePotential_predecessor_decrement`
  (`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorChargedPotential.lean`),
  together with `killedCapacityInitialMismatch_eq_zero_iff`
  (`UniformEquilibrium/Diagnostics/Quitting/Debt/KilledCapacityPotential.lean`).
  They already supply the state-local bounded charge potential and name the
  missing semantic-boundary calibration.

A narrow search for `invariant measure`, `ergodic`, `Birkhoff`, and
`occupation` found finite `PhaseOccupationDuality`, but no existing invariant-
measure producer for the compact Nash--Bellman relation.  The argument below
therefore uses the standard Birkhoff theorem as ordinary mathematics and
makes no Lean-availability claim.

## 3. Exact compact path space

Let `M` be the canonical reward bound and let `X` be the closed subset of the
canonical Nash--Bellman box consisting of points `(v,q)` with

\[
 v_i\ge\chi_i\quad\hbox{for every player }i,
\]

where `chi_i` is the behavioral punishment value.  Let `R(x,y)` mean
`IsQuittingNashBellmanEdge reward x y`; its orientation is current state to
chronological tail state.  The punishment-floor predecessor theorem and
one-stage mixed Nash existence give

\[
 \forall y\in X\ \exists x\in X,\quad R(x,y).       \tag{3.1}
\]

The set `X` is nonempty, compact, and the restricted edge graph is closed.
Define the one-sided path space

\[
 \Omega=\{\omega\in X^{\mathbb N}:R(\omega_t,\omega_{t+1})
          \text{ for every }t\}.
\]

It is nonempty compact.  The left shift `S` is continuous and, by (3.1),
surjective: every path can be prepended by an exact floor predecessor.  Thus
`Omega` admits shift-invariant Borel probability measures and ergodic ones.

For `x=(v,q)` write `p_j(x)` for player `j`'s Quit probability in the stored
root, and set

\[
 a(x)=1-\prod_j(1-p_j(x)),                          \tag{3.2}
\]

\[
 a_{-i}(x)=1-\prod_{j\ne i}(1-p_j(x)).              \tag{3.3}
\]

These are continuous and nonnegative.  They are respectively the one-row
joint absorption charge and the charge after deleting player `i`'s clock.

## 4. Recurrent-law dichotomy and the negative-solo seam

### Proposition 1 (proved, ordinary mathematics; corrected intermediate dichotomy)

Assume there is an ergodic shift-invariant Borel probability `mu` on `Omega`
such that

\[
 \int_\Omega a(\omega_0)\,d\mu(\omega)>0.           \tag{4.1}
\]

Then a typical deterministic exact floor spine has one of the following two
outputs:

1. its initial terminal payoff is a uniform-equilibrium payoff against
   arbitrary behavioral deviations; or
2. there is a unique owner `i` such that every opponent of `i` always
   Continues along the spine, `d_i=r({i})_i<0`,
   `chi_i<=d_i`, and some outsider `j` satisfies

   \[
   r(\{i\})_j<d_j:=r(\{j\})_j.                     \tag{4.2}
   \]

   Moreover, at every root of the selected path, if `p` is owner `i`'s
   hazard and `b_j=r({i,j})_j`, then

   \[
   d_j-b_j>0,\qquad
   p\ge {d_j-r(\{i\})_j\over d_j-b_j}>0.            \tag{4.3}
   \]

The second alternative is the only recurrent deleted-clock seam.

### Proof

Apply Birkhoff simultaneously to the finitely many functions `a` and
`a_{-i}`.  Choose one deterministic path `omega` for which all time averages
equal their integrals.  Equation (4.1) makes

\[
 \sum_t a(\omega_t)=\infty,
\]

so joint survival tends to zero.  For each player whose integral of
`a_{-i}` is positive, the same conclusion holds for the player-deleted
survival product.

There cannot be two distinct players `i,k` with both deleted-clock integrals
zero.  Nonnegativity gives `a_{-i}=a_{-k}=0` almost surely.  The first equality
forces every opponent of `i` to Continue almost surely; the second also
forces `i` to Continue.  Hence every player Continues and `a=0` almost surely,
contrary to (4.1).  Thus there are two cases.

If every deleted-clock integral is positive, the selected deterministic path
is an exact bounded Nash--Bellman spine with vanishing joint and every-player-
deleted survival.  The named infinite-path compiler gives its initial value
as a uniform-equilibrium payoff, with unrestricted behavioral deviations.

Otherwise there is a unique exceptional owner `i`.  Along the selected
typical path, `a_{-i}=0` at every date after discarding a null set before the
path is chosen, so every opponent of `i` always Continues.  Positive average
joint absorption is therefore positive average hazard of `i`; player `i`
quits alone almost surely.  Its prescribed terminal payoff is

\[
 d_i:=r(\{i\})_i.
\]

Exact Bellman transport together with vanishing joint survival identifies the
initial stored value with this actual terminal payoff.  Every pure finite
quit time of player `i` also pays exactly `d_i`, while Never pays zero.  If
`d_i>=0`, no behavioral stopping law of `i` improves on prescribed play.

For every other player `j`, the opponent clock includes `i` and has positive
average charge, so its deleted survival tends to zero.  The usual exact
Bellman telescope caps every pure quit time of `j`; pure-time extremality then
caps every behavioral deviation.  The joint survival limit delivers the
fixed initial payoff.  When `d_i>=0`, the standard terminal-to-uniform bridge
therefore gives a uniform-equilibrium payoff.

Suppose `d_i<0`.  Vanishing joint survival from every suffix shows that every
stored value equals the literal singleton column `r({i})`.  Since the path is
in the floor carrier, its owner coordinate gives `chi_i<=d_i`.  If

\[
 d_j\le r(\{i\})_j\quad\hbox{for every }j,
\]

then `i` is exactly a `QuittingNormalNoHarmSingletonOwner`, and the named
checked producer supplies a uniform-equilibrium payoff (not necessarily the
payoff of this recurrent path).

Otherwise choose `j` satisfying (4.2).  At a typical root only `i` can Quit.
Player `j`'s prescribed Continue payoff is `r({i})_j`, while forced Quit pays

\[
 p\,r(\{i,j\})_j+(1-p)d_j.
\]

Exact root Nash makes the latter no larger.  Rearrangement gives

\[
 p(d_j-r(\{i,j\})_j)\ge d_j-r(\{i\})_j>0,
\]

which proves (4.3) and alternative 2.  Thus the surviving negative-solo seam
is automatically a uniform-hazard, harmful-collision component.

### Proposition 1C (proved, ordinary mathematics; strict sharpening)

If there is an ergodic shift-invariant Borel probability `mu` on `Omega` with

\[
 \int_\Omega a(\omega_0)\,d\mu(\omega)>0,
\]

then the quitting game has a uniform-equilibrium payoff.  No sign or no-harm
hypothesis is needed.

### Proof

Apply Proposition 1.  Its first output already gives the conclusion.  In its
second output, fix any root on the selected deterministic path.  Only owner
`i` can Quit there, and (4.3) in particular gives its hazard `p>0`.  Let `h`
be the corresponding Bernoulli law.  Every stored continuation value is the
singleton column

\[
 c=\operatorname{quittingSoloReward}(r,i).
\]

By the definition of `IsQuittingNashBellmanEdge`, the root is exact endpoint
Nash against `c`.  The floor carrier gives

\[
 \chi_i\le c_i=r(\{i\})_i.
\]

These are exactly the three hypotheses of
`isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`:
positive solo rate, exact endpoint Nash against the singleton vector, and the
owner's punishment individual rationality.  That checked theorem constructs a
long finite period-one prefix followed, only after the owner's refusal, by a
near-minmax punishment.  It therefore controls the negative owner's Never
deviation and supplies the same fixed singleton payoff target against all
behavioral deviations.  This proves the conclusion.

The no-harm dispatch and harmful-collision inequality in Proposition 1 remain
valid local information, but they are not needed for Proposition 1C.

The punishment floor does **not** by itself price the bare selected spine: a player's min--max
can be negative because hostile opponents may absorb before Never protects
the player.  The following exact test is why the first draft was corrected.

### Proposition 1B (proved: the bare floor spine need not price Never)

There is a two-player quitting table and a constant positive-absorption
ergodic floor spine in alternative 2.  Let

```text
r({0})   = (-1, 1),
r({1})   = (-2, 2),
r({0,1}) = (-2,-2).
```

Fix `p=1/2`.  At every date player `0` Quits with probability `p`, player `1`
Continues, and the continuation/current value is `v=(-1,1)`.
This is an exact constant Nash--Bellman edge in the punishment-floor carrier,
with mean absorption `p`; nevertheless player `0` gains one by switching to
Never in the infinite path.

### Proof

Player `0` gets `-1` from either Quit or Continue at the root.  Player `1`
gets one from Continue, while forced Quit gives
`(1/2)*(-2)+(1/2)*2=0<=1`.  The Bellman expectation is exactly `(-1,1)`, so
the edge is exact Nash--Bellman.

To punish player `0`, let player `1` Quit surely.  Both of player `0`'s root
actions then pay `-2`, hence `chi_0<=-2`; the reward bound gives equality.
To punish player `1`, let player `0` Quit surely; its best reply is Continue,
with payoff one, rather than joint Quit at `-2`, so `chi_1<=1`.  Thus
`v>=chi` coordinatewise.
The constant path absorbs at singleton `{0}` almost surely and pays player
`0` value `-1`; Never against the prescribed always-Continue opponent pays
zero.  Here player `1` is genuinely harmed by owner `0`'s singleton row:
`r({0})_1=1<2=d_1`, and (4.3) reads `p>=1/4`.  This falsifies only the bare
selected-path compiler.  In fact the root itself meets Proposition 1C's
punishment-completed solo-cycle hypotheses: `p=1/2>0`, endpoint Nash is exact,
and `chi_0=-2<=-1`.  Thus the checked compiler repairs precisely this Never
deviation.  The table is not a counterexample to the conjecture.

## 5. The exact remaining obstruction

Define the maximal invariant mean joint charge

\[
 \beta=\sup_{\mu\in\mathcal I(S)}
       \int a(\omega_0)\,d\mu.                     \tag{5.1}
\]

The invariant-measure set is nonempty compact convex, so the supremum is
attained; an ergodic maximizing component also attains it.  Proposition 1C
closes the game whenever `beta>0`.  Thus the only remaining recurrent
obstruction is `beta=0`.  Since `a>=0`, every invariant law is then supported
on all-Continue roots.  This
is much sharper than the existence of the canonical phantom self-loop: it
says **all recurrent punishment-floor dynamics are phantom**.

For an arbitrary compact serial relation this conclusion does not bound total
transient charge.  A path may have `sum_t a(omega_t)=infinity` while its time
average tends to zero, which is already enough for the checked clock compiler;
or it may carry only finite charge while converging to the phantom set.  The
universal next dichotomy is therefore:

1. construct one floor path whose every player-deleted charge diverges
   (positive endpoint); or
2. from `beta=0` and bounded transient charge, construct a bounded continuous
   bias `Phi` with the checked reversed-relation drift inequality

   \[
   a(x)\le \Phi(y)-\Phi(x)\qquad(R(x,y)),           \tag{5.2}
   \]

   then show that exact Nash plus a positive terminal exploitability gap
   forbids (5.2) on the floor carrier.

Equation (5.2) is not asserted here.  Ergodic optimization generally supplies
approximate subactions under additional regularity, and exact continuous
subactions can fail on an arbitrary closed relation.  The immediate concrete
check is the smallest actual residual-hard table: compute whether its full
punishment-floor edge relation has a nontrivial exact two-cycle (the known
period-two completion suggests yes) and verify that its invariant law meets
Proposition 1's exceptional-owner analysis.  This is a source test of the new
producer, not a claim that one example proves the universal step.

## 6. Finite-prefix characterization of the invariant mean

The invariant-law hypothesis has an exact finite-path formulation.  For
`N>=1` put

\[
 A_N=\max_{\omega\in\Omega}\sum_{t=0}^{N-1}a(\omega_t).             \tag{6.1}
\]

The maximum exists by compactness.  These are not independently chosen
prefix stacks: every term is the prefix of one literal infinite exact floor
spine.

### Proposition 2 (proved: ergodic optimization identity)

With `beta` from (5.1),

\[
 \beta=\lim_{N\to\infty}{A_N\over N}
      =\inf_{N\ge1}{A_N\over N}.                                \tag{6.2}
\]

Consequently positive linear growth produces a positive-mean ergodic law and
Proposition 1C gives a uniform-equilibrium payoff.  Any unresolved game must
therefore satisfy `A_N=o(N)`.

### Proof

The suffix of a path in `Omega` is again in `Omega`, so

\[
 A_{N+K}\le A_N+A_K.
\]

Fekete's lemma gives the limit and infimum in (6.2).  For every invariant law
`mu`, invariance and (6.1) give

\[
 N\int a\,d\mu
 =\int\sum_{t<N}a\circ S^t\,d\mu\le A_N.
\]

Thus `beta<=inf_N A_N/N`.

For the reverse inequality, choose a maximizing path `omega^N` and its
empirical law

\[
 \nu_N={1\over N}\sum_{t=0}^{N-1}\delta_{S^t\omega^N}.
\]

Compactness of the probability laws on compact metrizable `Omega` gives a
weakly convergent subsequence.  For every continuous test function `f`,

\[
 \int(f\circ S-f)\,d\nu_N
 ={f(S^N\omega^N)-f(\omega^N)\over N}\longrightarrow0,
\]

so the limit `mu` is invariant.  Its `a`-integral is the limit of `A_N/N`.
An ergodic component of a maximizing invariant law is still maximizing.
If the common value is positive, Proposition 1C applies.

This proof explains why a positive invariant law is stronger than mere
unbounded charge: `A_N=sqrt(N)`-scale growth gives no recurrent mean but can
still produce divergent absorption along selected paths.

### Proposition 3 (proved: bounded-charge path bias)

If `K:=sup_N A_N<infinity`, then

\[
 \Phi(\omega)=\sum_{t=0}^{\infty}a(\omega_t)                      \tag{6.3}
\]

is a bounded lower-semicontinuous function on `Omega` satisfying the exact
coboundary identity

\[
 \Phi(\omega)=a(\omega_0)+\Phi(S\omega).                         \tag{6.4}
\]

### Proof

The partial sums are continuous, nondecreasing, and bounded above by `K`;
their pointwise supremum is therefore finite and lower-semicontinuous.  Split
off the first nonnegative term to obtain (6.4).

There are two substantive losses.  First, a bounded increasing supremum of
continuous partial sums need not be continuous, and `Phi` depends on the
whole chosen future rather than only the current Nash--Bellman state.  Second,
its orientation is the opposite of (5.2): (6.4) says charge is paid by a
**decrease** from the current path to its tail, whereas the checked admissible
charged relation reverses the chronological edge and therefore its canonical
potential **increases** from chronological current state `x` to tail state
`y`.  Thus the future-charge envelope is not an approximation to the checked
capacity potential even if it happened to factor through the current state.
This corrects an earlier draft that mistakenly reversed (5.2) after
identifying `R(x,y)` with the checked charged-relation orientation.  The two
relations have opposite source/target conventions.

This proposed next check is superseded by Section 7's source audit: the
repository already constructs a state-local bounded budget-to-go potential
directly from the common prefix bound.  Continuity is not its main documented
seam; semantic boundary calibration is.

## 7. Source overlap and closure verdict

### Proposition 4 (proved, ordinary mathematics)

If `beta>0`, exact punishment-floor finite prefixes have unbounded absorption
charge.  Consequently the checked theorem
`quittingGame_exists_uniformPayoff_of_unbounded_floorPrefixCharge` already
produces a uniform-equilibrium payoff.  Conversely, under a
`QuittingTerminalExploitabilityWitness`, `beta=0` and every path in `Omega`
has finite total absorption bounded by the canonical prefix-charge bound.

### Proof

Choose an ergodic invariant law of positive mean and a Birkhoff-typical path
`omega`.  Its first `N` chronological edges have charge tending to infinity.
To match the repository's finite-prefix orientation, reverse this literal
segment: for `0<=t<=N` put

\[
  \operatorname{value}(t)=\omega_{N-t}.v,
\]

and for `0<=t<N` use the root stored at `omega_{N-t-1}`.  The edge
`R(omega_{N-t-1},omega_{N-t})` says exactly that this root is endpoint Nash
against `value(t)` and that its successor payoff is `value(t+1)`.  Every state
lies in the box and above the punishment floor.  Thus the reversed segment is
a `QuittingPunishmentFloorFinitePrefix`, with charge

\[
  \sum_{t=0}^{N-1} a(\omega_t).
\]

These charges are unbounded, so the named checked compiler applies.

If a terminal exploitability witness exists, its checked `prefixCharge_le`
bounds every such reversed prefix by the fixed canonical charge bound.  Hence
every partial sum along every `omega` is bounded, every total absorption sum
is finite, and invariance gives

\[
 N\int a\,d\mu
 =\int\sum_{t<N}a\circ S^t\,d\mu
 \le C.
\]

Letting `N` tend to infinity yields `int a dmu=0` for every invariant law.

### Consequence and non-novelty

Proposition 1C remains a correct, independently reviewed direct recurrence
adapter, and its exceptional-owner use of punishment completion is reusable.
It does not change the universal frontier: its hypothesis is already a
special case of the unbounded-prefix producer.  In the bounded branch,
`quittingPunishmentFloorReachablePotential` is already a state-local bounded
potential with the exact edge decrement.  The checked capacity/debt files
show that the unresolved datum is equality or domination of the surviving
semantic debt boundary by this independently optimized capacity account.
No invariant-measure argument in this notebook supplies that equality.
