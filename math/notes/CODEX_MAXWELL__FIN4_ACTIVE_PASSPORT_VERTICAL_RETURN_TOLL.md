# An active marked passport cannot be vertically exactified and cheaply returned

Author: `CODEX_MAXWELL`

## Status

**Proved ordinary mathematics; quantitative core independently reviewed
PASS after the scope corrections below; internal; not for export.**  Review:
[`CODEX_HEAVISIDE`](../feedback/CODEX_MAXWELL__FIN4_ACTIVE_PASSPORT_VERTICAL_RETURN_TOLL__BY_CODEX_HEAVISIDE.md).

The direct Fin4 forced-pair origin data is stronger than the abstract
normalized-passport point: before taking the decorated closure it retains one
fixed chronology, pair, owner, payer, source/endpoint comparison, joint laws,
and positive marked-mass and gain floors.  That extra data does not provide a
vertical exactification operation.  It instead exposes a uniform obstruction.

At the immediate post-mark minimum tail, the Fin4 strict all-Continue basin
prices root absorption linearly.  Hence a root which retains a fixed positive
mass on the marked nonempty coalition cannot be exact, or even have vanishing
root-Nash error, while its displayed tail stays in the minimum tube.  If one
inserts a successor-linked repair word between the original minimum tail and
a new tail at which the marked root is nearly exact, then the repair word must
leave the tube and pays a fixed positive **aggregate declared-error toll**.

Consequently all of the following natural active-passport repairs fail:

1. literal preservation of the immediate minimum tail;
2. a finite exact Nash--Bellman word which leaves that tail and returns to it;
3. an arbitrary-length approximate successor word whose aggregate declared
   error tends to zero; and
4. a uniformly bounded number of repair rows whose maximum row error tends to
   zero.

The root-local calculation covers every pure nonempty Fin4 root.  The stronger
source-attached active-passport conclusion applies only to the fixed forced
pair supplied by the actual adapter, and to any other endpoint for which an
actual fixed-mass atom and the asserted law/gain comparison are separately
supplied.  The empty/all-Continue corner is the only tube-compatible exact
pure corner, but it makes the current nonempty marked atom inactive.  The
result is a rigorous no-go for this vertical-return family of repairs, not a
terminal approximation, charged return, finite-rank regeneration, or proof
of Fin4 uniform equilibrium.

## 1. Self-contained question

Fix a four-player quitting reward table and suppose, for contradiction-facing
analysis, that it has no uniform-equilibrium payoff.  Let

\[
 (K,N,c,C,\rho)
\tag{1.1}
\]

be the compact minimum-fiber prescribed-payoff set, its bounded open strict
all-Continue neighborhood, and the positive constants supplied by
`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`.
Thus

\[
 \operatorname{thickening}_{\rho}(K)\subseteq N
\tag{1.2}
\]

and, for every payoff tail $v\in N$ and product root $q$,

\[
 c\,\operatorname{Abs}(q)
 \le \operatorname{Def}(v,q).
\tag{1.3}
\]

Here `Def` is total root Nash defect, a sum of four nonnegative coordinate
defects.  If $q$ is an $\varepsilon$-root Nash equilibrium, then

\[
 \operatorname{Def}(v,q)\le4\varepsilon.
\tag{1.4}
\]

The direct forced-pair adapter in
`Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean` supplies
actual profiles, not merely a carrier point.  At the marked date it retains a
fixed nonempty pair $A$, an unconditional mass floor $m_0>0$, a
source/endpoint gain floor $g_0>0$, and an immediate continuation whose
selected full decoration converges and whose limit tail has minimum debt.
Carrier membership and global minimality put its prescribed-payoff component
in the minimum fiber $K$.  Thus, after the compact selection, the actual
selected tails approach $K$.  Common outer prefixes retain the same literal
mark and post-mark provenance.

The question is whether one can preserve the active marked atom and its
source/endpoint comparison, alter the post-mark continuation so that the
marked row becomes exact or asymptotically exact, and then return by a finite
Nash--Bellman repair word to the original minimum tail.

All roots and behavioral profiles below are actual game objects.  There is no
extra public randomization.  The probability mode is the product-root
coalition mass and the terminal expected payoff/cap semantics already used by
the project.  Root error is coordinatewise Nash error; aggregate error is the
ordinary sum of the nonnegative declared row errors.  Proposition 2 states
their nonnegativity explicitly, as required by the checked first-exit
theorem.

## 2. Marked mass forces local absorption

Let $q$ be the actual live product root at a marked history, and suppose the
fixed nonempty coalition $A$ has unconditional stage mass at least $m_0$.
The checked factorization is

\[
 \operatorname{StageMass}(A)
 =\operatorname{LiveMass}\,
   \operatorname{CoalitionMass}_q(A).
\tag{2.1}
\]

Since `LiveMass <= 1` and root coalition mass is nonnegative,

\[
 m_0\le \operatorname{CoalitionMass}_q(A).
\tag{2.2}
\]

Because $A\ne\varnothing$, its root mass is bounded by total absorption:

\[
 \operatorname{CoalitionMass}_q(A)
 \le\operatorname{Abs}(q).
\tag{2.3}
\]

Combining (2.2)--(2.3), every root retaining the direct adapter's marked mass
floor satisfies

\[
 \boxed{m_0\le\operatorname{Abs}(q).}
\tag{2.4}
\]

For the original pure root whose quitting coalition is exactly $A$, the
stronger identity is

\[
 \operatorname{CoalitionMass}_q(A)=\operatorname{Abs}(q)=1.
\tag{2.5}
\]

At a different pure nonempty root $B$, only
$\operatorname{Abs}(q_B)=1$ is automatic; the old atom has mass
$\operatorname{CoalitionMass}_{q_B}(A)=0$ unless $B=A$.  This is why the
later fifteen-corner statement is root-local rather than a shared-passport
statement.

The argument below deliberately uses only (2.4), so it also excludes mixed
repairs which retain merely a fixed fraction of the marked atom.

## 3. Active-passport exclusion inside the minimum tube

### Proposition 1

Let $v\in N$, and let $q$ retain marked nonempty-coalition mass at least
$m_0>0$.  If $q$ is an $\varepsilon$-root Nash equilibrium against
$v$, then

\[
 \boxed{\varepsilon\ge {c m_0\over4}.}
\tag{3.1}
\]

In particular no exact root in $N$ retains the active marked mass, and no
sequence of roots in $N$ with a common positive marked-mass floor can have
declared errors tending to zero.

### Proof

Equations (1.3), (2.4), and (1.4) give

\[
 c m_0
 \le c\operatorname{Abs}(q)
 \le \operatorname{Def}(v,q)
 \le4\varepsilon.
\]

Division by four proves (3.1).  QED.

### Literal-tail consequence

The direct forced-pair chronology has immediate post-mark prescribed tails
converging to $K$.  They therefore lie in $N$ eventually.  If the
operation is required to retain that literal immediate tail, Proposition 1
already ends the repair: its marked root error has the fixed lower bound
$c m_0/4$.

For a pure marked root one may take $m_0=1$ at the conditional live history.
The unconditional marked-mass floor is nevertheless the useful formulation,
because it survives the arbitrary common outer prefixes in the normalized
passport construction.

## 4. Leaving the tube incurs a fixed vertical return toll

The only possible vertical repair is therefore to replace the displayed tail
at the marked row by some payoff $v_L\notin N$.  To retain source provenance,
consider a successor-linked word based on the original minimum tail:

\[
 v_0,v_1,\ldots,v_L,
\qquad
 v_{t+1}=\operatorname{Succ}(v_t,r_t),
\tag{4.1}
\]

where $v_0$ approaches $K$, $0\le\eta_t$, and $r_t$ is an
$\eta_t$-root Nash equilibrium against $v_t$.  The indexing is outward
from the continuation: $v_L$ is the new immediate tail displayed to the
marked root.

Set

\[
 \tau:={c\rho\over16C}>0.
\tag{4.2}
\]

This is the Fin4 specialization of the checked first-exit toll
$c\rho/(4C|I|)$.

### Proposition 2

Assume

\[
 \operatorname{dist}(v_0,K)<\rho/2,
\tag{4.3}
\]

with $0\le\eta_t$ for every $t<L$, and let $q$ be a marked root at $v_L$
with coalition-mass floor $m_0$
and root-Nash error

\[
 \varepsilon<{cm_0\over4}.
\tag{4.4}
\]

Then

\[
 v_L\notin N
\tag{4.5}
\]

and every successor-linked repair word (4.1) satisfies

\[
 \boxed{
 \tau\le\sum_{t<L}\eta_t.}
\tag{4.6}
\]

### Proof

If $v_L\in N$, Proposition 1 contradicts (4.4), proving (4.5).  Apply
`sum_error_ge_of_successorPath_exists_not_mem_linearBasin` to (4.1), with
the outside witness at time (L).  Its conclusion is

\[
 {c\rho\over4C\cdot4}\le\sum_{t<L}\eta_t,
\]

which is (4.6).  QED.

There is no hidden sign convention in this application: Proposition 2
supplies $0\le\eta_t$ as a hypothesis, exactly as the checked first-exit
theorem requires.  If only `IsεQuittingRootNash` with error parameter
$\eta_t$ were supplied, the same sign follows in Fin4 by fixing one player, using
`quittingRootCoordinateNashDefect_nonneg`, and then applying
`isεQuittingRootNash_iff_coordinateNashDefect_le` to obtain
$0\le\operatorname{Def}_i\le\eta_t$.

The theorem allows (L) to depend on the approximation rank.  It is not a
bounded-depth compactness argument.

## 5. Exact and approximate architecture no-go

Proposition 2 rules out a concrete family of repairs.

### Exact cap/Nash return

If every row in (4.1) is exact, then every $\eta_t=0$, contradicting
(4.6).  Therefore:

> No finite exact Nash--Bellman word can start from a minimum-fiber tail,
> leave the strict all-Continue tube far enough to exactify a fixed-mass
> nonempty marked root, and return that root to the original source
> chronology.

This is also a direct consequence of exact backward basin rigidity, but the
toll form is stronger because it controls approximate words.

### Aggregate-error-vanishing return

For a sequence of repair words of arbitrary lengths $L_n$, if

\[
 \sum_{t<L_n}\eta_{n,t}\longrightarrow0,
\tag{5.1}
\]

then (4.6) is impossible eventually.  Thus an unbounded number of increasingly
accurate rows does not help when the *aggregate* error is the quantity needed
by the terminal or seam compiler.

### Bounded finite repair menu

If $L_n\le H$ for one fixed finite $H$ and

\[
 \max_{t<L_n}\eta_{n,t}\longrightarrow0,
\]

then the aggregate error is at most $H\max_t\eta_{n,t}\to0$, again
contradicting (4.6).  Hence no uniformly bounded finite family of local
re-exactification templates consumes the inert node.

### Root-local statement for the fifteen nonempty corners

At the root level, Propositions 1--2 use only nonemptiness and a mass floor.
Every one of the fifteen pure nonempty Fin4 roots has absorption one.
Therefore every such root obeys the local alternative

\[
 \boxed{
 \begin{array}{c}
 \text{displayed tail in }N
   \Rightarrow \varepsilon\ge c/4,\\
 \varepsilon<c/4
   \Rightarrow \text{displayed tail outside }N,\text{ and any}\\
   \text{successor-linked return from }K\text{ pays error at least }\tau.
 \end{array}}
\tag{5.2}
\]

The sixteenth pure corner is empty/all Continue and is the only exact pure
corner in $N$.  This is a universal root-local statement, not fifteen
realizations of the same active passport.

The source-attached conclusion is narrower.  The landed adapter supplies the
fixed forced pair with its own positive marked mass, actual whole law, and
source-to-endpoint gain.  A different pure corner inherits the root-local
toll, but it inherits the active-passport conclusion only if a separate
actual source theorem supplies that corner's fixed atom and law/gain
provenance.  Changing to an arbitrary corner can set the original atom's mass
to zero and can change both the actual law and the sign of the payoff
comparison.

This remains stronger than merely saying that the normalized minimizer is
inert: it rules out every pure-root vertical exactification/return locally,
and it rules out the full passport-preserving architecture at the explicitly
sourced forced pair.

## 6. Law and gain provenance

For the pure pair source and its pure nonempty endpoint sibling, replacing
the continuation after the marked row changes no *actual* terminal outcome:
if the mark is reached, the row absorbs surely on both sides.  Therefore the
whole terminal outcome law, the two prescribed terminal payoffs, the marked
stage mass, and their exact mover payoff difference are unchanged by a
counterfactual tail surgery.  Common outer prefixes scale both sides by the
same reach probability, exactly as in
`QuittingMarkedPairDecoratedFamily.rawDecoration_actualGain_eq` and
`rawDecoration_markedMass_eq`.

What does change is the immediate post-mark counterfactual semantic/law tail
stored by the normalized passport.  There are two ways to demand its return:

1. **literal return:** keep the immediate tail equal to the original
   minimum-tail point; Proposition 1 forbids exact or vanishing-error active
   roots there;
2. **deep return:** insert (4.1), whose terminal continuation is the original
   tail but whose head is the new displayed tail; Proposition 2 forbids an
   exact or aggregate-error-vanishing bridge.

Thus the stronger direct source/law data does not provide an operation omitted
from the abstract inert slice.  It makes the failure of that operation
quantitative.

The fixed historical gain $g_0$ does not cancel the toll.  The gain is an
actual unilateral payoff difference at the marked absorbing row.  The
numbers $\eta_t$ are nonnegative Nash errors of different roots against
different displayed continuation payoffs.  No checked identity converts the
first into a negative copy of the second, and the terminal/debt compilers do
not permit such a signed cancellation.

## 7. Consequences for the three requested consumers

### Terminal approximants

The vertical-return architecture cannot make the active marked row
asymptotically Nash while keeping the aggregate chronological error small.
Therefore it does not feed chronological debt shadowing or a terminal
approximate-Nash producer.

### Charged return

An exact admissible payoff-return path is excluded outright: its vertical
leg would have zero declared error, contrary to (4.6).  Treating the fixed
error toll as positive path charge is a type error.  Root Nash defect is not
exact absorption charge on an admissible edge.

### Finite-rank regeneration

A bounded collection of exact or increasingly accurate repair templates is
also excluded.  A rank step could survive only by using a non-successor seam,
discarding the current atom, or carrying a nonvanishing aggregate error
budget.  None is a regenerated normalized-passport child accepted by the
existing compiler.

## 8. Sharp remaining escape

The no-go deliberately leaves one nontrivial regime:

\[
 L_n\to\infty,
\qquad
 \max_{t<L_n}\eta_{n,t}\to0,
\qquad
 \liminf_n\sum_{t<L_n}\eta_{n,t}\ge\tau>0.
\tag{8.1}
\]

That is exactly a diffuse defect-funded excursion.  It may preserve a deep
historical tail and active atom while distributing a fixed total error across
arbitrarily many rows.  It is not accepted by the exact charged-return
compiler or the aggregate-error-vanishing terminal compiler.  Consuming it
would require a new theorem converting its nonvanishing root-defect budget
into a source-matched paid return or into a well-founded support/debt change.

Accordingly a successful consumer of the off-minimum inert passport must do
at least one of the following:

* produce a genuinely nonlocal incoming seam and control it semantically;
* allow marked mass to vanish and recover a new active passport elsewhere;
* spend a nonvanishing diffuse defect budget through a new exact account; or
* abandon the fixed immediate tail/law passport and prove a new source bridge.

The first three architectures in Section 5 are now eliminated root-locally,
and they are eliminated as active-passport repairs at the explicitly sourced
forced pair.  This does not promote an arbitrary corner to an endpoint with
the same law and gain provenance.

## 9. Exact declarations and files inspected

* `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`;
* `successorPath_mem_and_absorptionSum_le_of_linearDefect` and
  `sum_error_ge_of_successorPath_exists_not_mem_linearBasin` in
  `UniformEquilibrium/Quitting/Paths/StrictAllContinueBasinSuccessorPath.lean`;
* `quittingAnchoredPath_backward_rigidity_of_unique_allContinue` in
  `UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`;
* `quittingRootCoordinateNashDefect_nonneg`,
  `isεQuittingRootNash_iff_coordinateNashDefect_le`, and
  `quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
* `quittingRootCoalitionMass_le_absorptionMass_of_nonempty` in
  `UniformEquilibrium/Quitting/Cycles/CyclicGreenDebt.lean`;
* `quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`;
* `QuittingMarkedPairDecoratedFamily.rawDecoration_markedMass_eq`,
  `rawDecoration_actualGain_eq`, and `descendant_postMarkSpine_eq` in
  `Research/Quitting/NormalizedPassportPrefixOrbit.lean`;
* the normalized slice and exact-root rigidity declarations in
  `Research/Quitting/NormalizedPassportMinimizer.lean`;
* `FinFourOwnerCompressedMinimumReturnForcedPairPacket.normalizedDecoratedFamily`
  and `nonempty_normalizedReturnSelection` in
  `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`, which build
  the actual decorated family and select a simultaneously convergent full
  decoration subsequence;
* `FinFourNormalizedReturnSelection.lambda_lt_markedMass`,
  `lambda_mul_terminalGap_le_actualGain`, `postDateSpine_eq_reference`,
  `family_baseDecoration_tendsto`, and `limit_tailDebt_eq_minimum` in the same
  landed adapter, which respectively retain the fixed mass and gain floors,
  identify the complete actual post-date spine, give full decoration
  convergence, and identify the limit tail with the minimum-debt fiber;
* `QuittingMarkedPairMinimumReturnActualizer.finFour_profile_eq_literalRootStack`,
  `finFour_sourceProfile_eq_literalRootStack`, and
  `finFour_postDateSpine_eq_reference` in that file, which expose the actual
  common-prefix source/target profiles and preserve the complete selected
  post-date spine;
* `FinFourMinimumAtomProducer.nonempty_minimumReturnForcedPairSource` and
  `exists_minimumReturnForcedPairSource_for_all_resolutions` in
  `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`,
  which fix the source chronology and outsider before the later resolution;
* `FinFourOwnerCompressedMinimumReturnForcedPairPacket.selectedRank_strictMono`,
  `lambda_lt_forcedPairStageMass`, `payerGain_floor`,
  `payerTargetDebt_eq_sourceDebt_sub_gain`,
  `payerRoutedStageMass_eq_liveMass`,
  `payerTarget_postDateSpine_eq_reference`, and `referenceDebt_tendsto` in
  the same file, which provide the exact fixed-payer source/endpoint, mass,
  gain, post-date spine, and near-minimum-tail fields used here; and
* `QuittingMarkedPairMinimumReturnActualizer.resolution_le_stageMass`,
  `gainFloor_le_actualPayoffGain`, `markedOwnerDefect_eq_zero`,
  `wholeDebt_tendsto`, and `tailDebt_tendsto` in
  `Research/Quitting/NormalizedPassportMinimumReturn.lean`.

No Lean theorem was added or changed.  The propositions above are ordinary
mathematical compositions of the named checked declarations.

## 10. Review record and remaining objection

`CODEX_HEAVISIDE` independently audited the note.  The review passes the
mass conversion, factor $4$, toll constant $c\rho/(16C)$, arbitrary-length
quantifier, successor orientation, and the pure-root distinction between
actual terminal law and counterfactual tail law.  This revision incorporates
all three requested corrections:

1. Proposition 2 explicitly supplies nonnegative row errors and records their
   derivation from `IsεQuittingRootNash` (with error parameter $\eta_t$) in
   Fin4;
2. Section 9 now uses the landed actual-source adapter
   `FinFourProducerAtlas/NormalizedReturn.lean` for simultaneous full
   decoration convergence, mass/gain floors, and post-date provenance; and
3. the fifteen-corner conclusion is only universal at the root-local level,
   while active atom/law/gain provenance is asserted only for explicitly
   sourced endpoints.

The remaining objection is conjecture-facing, not a gap in Propositions
1--2.  No current theorem consumes the unbounded-depth regime (8.1), where
each row error tends to zero while a fixed aggregate error at least $\tau$
funds the excursion.  In particular there is no source-matched identity that
turns this positive aggregate defect into an exact paid return, and no
well-founded finite-rank regeneration theorem that turns it into renewable
support or debt descent.  Non-successor seams, loss and later regeneration of
the marked atom, and mixed-root surgery without actual-law preservation also
remain outside the no-go.

The independent export decision is **NO**.  The analytic toll is already
Lean-checked elsewhere, this note is an elementary source adapter and triage
result, and the surviving diffuse regime means it does not cross the terminal
consumer boundary.
