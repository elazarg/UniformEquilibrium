# Fin4 nonzero-persistent exact-spine selection: source moat and restart no-go

**Identity:** CODEX_STRENGTHEN  
**Date:** 2026-08-30  
**Status:** The requested persistent-spine producer remains open.  This note
proves, in ordinary mathematics from checked Lean interfaces, a sharp no-go
for the proposed summable-seam restart route and isolates the source
provenance that an all-summable-spine consumer would have to retain.  It also
rules out selection confined to the exact punishment-floor carrier.  No new
Lean declaration is claimed.

## Question

Fix a reward table

\[
 r:\{S\subseteq \operatorname{Fin}4:S\ne\varnothing\}\longrightarrow
 \mathbb R^4.
\]

An exact bounded Nash--Bellman spine is a bounded sequence \(v_n\) and a
sequence of product roots \(x_n\) such that

\[
 v_n=F_{x_n}(v_{n+1}),\qquad
 x_n\text{ is exact root Nash against }v_{n+1}.
\]

Write \(q_{n,i}=\Pr_{x_n}(i\text{ Quits})\).  The desired implication is

\[
 \text{no uniform-equilibrium payoff}
 \Longrightarrow
 \exists(v,x)\ \exists i\quad \sum_n q_{n,i}=+\infty.
\]

The downstream consumers in the question make any nonempty persistent set
sufficient.  Thus the producer may equivalently seek divergent total
absorption: for finitely many players, divergence of the sum of the marginal
hazards forces one fixed marginal to diverge.  Merely obtaining a positive
amount on every unrelated finite block is not enough.

## Narrow source audit

I read `SOURCES.md`, `GOAL.md`, the question file, and the relevant portions
of `docs/FRONTIER.md` and `docs/TOOLKIT.md`.  The following are checked Lean
declarations; the new deductions later in this note are ordinary proofs.

1. Exact-spine interface:

   - `IsCanonicalExactQuittingNashBellmanSpine` and
     `uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine` in
     `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`;
   - `exists_bounded_exact_quittingNashBellmanSpine` in
     `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`;
   - `IsCanonicalExactQuittingNashBellmanSpine.exists_tendsto_value_of_summableClock`
     in
     `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanValueConvergence.lean`;
   - `summable_quittingOpponentClockCharge_iff` and
     `hasTwoPersistentQuittingMarginals_iff_all_opponentClocks` in
     `UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`.

2. The actual Fin4 no-uniform-payoff source:

   - `exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff` and
     `exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`
     in
     `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`.

   The latter supplies a positive global-minimum semantic pair \(p\), its
   full envelope-to-prescribed debt segment \(P\), and one open set \(O\)
   containing \(P\), on every point of which all-Continue is the unique exact
   Nash root.

3. Unique-all-Continue basin rigidity:

   - `anchoredPath_terminal_not_mem_of_positiveAbsorption`,
     `le_dist_terminal_of_positiveAbsorption_of_ball_subset_allContinueBasin`,
     and `exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue` in
     `UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`;
   - `exactCapPrefix_joint_eq_self_of_unique_allContinue` and
     `capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap` in
     `Research/Quitting/UniqueAllContinueCapStackNoGo.lean`.

4. The exact punishment-floor carrier:

   - `QuittingTerminalExploitabilityWitness.infiniteOrbit_absorptionMass_summable`
     and
     `QuittingTerminalExploitabilityWitness.infiniteOrbit_tsum_absorptionMass_le_prefixChargeBound`
     in
     `UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitConsequences.lean`.

   These are **all-orbit** statements, not assertions about one arbitrary
   compactness selector.

5. Semantic-carrier endpoint:

   - `quittingTerminalSemanticCarrier` and
     `quittingTerminalSemanticCarrier_isCompact` in
     `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
   - `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` in
     `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.

6. The actual maximal-cap prefix ray:

   - `minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop` and
     `summable_maximalCapPrefix_absorption` in
     `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`;
   - the source-facing orientation is explicit in
     `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`.

   Hence a positive global semantic debt floor already makes the absorption
   of this recursively changed-state maximal-prefix construction summable.
   Moreover, it is an outward prefix construction, not automatically a
   single forward chronological Bellman spine.  It cannot simply be renamed
   as the desired persistent spine.

7. Exact regressions:

   - `Research/Quitting/FinFourEventualAllContinueLocalRegression.lean`
     gives an actual Fin4 table with semantic pair prescribed payoff
     \((1,4,1,2)\), cap \((3,4,2,2)\), debt \((2,0,1,0)\), unique
     all-Continue exact root at the cap, and an inert maximal-prefix orbit.
     Its global minimum is zero and zero is a uniform payoff, so it is a
     boundary regression, not a positive-gap counterexample.
   - `Research/Quitting/MaximalRayZeroMinimumActiveRegression.lean` gives a
     nontrivial but summable maximal-ray regression at zero minimum.

## 1. A uniform moat around the Fin4 source segment

Here is the strongest clean deduction I obtain from the strict-minimum
plateau theorem.

### Proposition (uniform source moat)

Assume the Fin4 game has no uniform-equilibrium payoff.  Select \(p,P,O\) from
`exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`.
There is \(\rho>0\) such that

\[
 a\in P,\ z\notin O \quad\Longrightarrow\quad
 \rho\leq \lVert z-a\rVert.
\]

If a finite exact Nash--Bellman block, anchored at terminal tail \(z\), has a
positive-absorption root at any date, then for every \(a\in P\),

\[
 \rho\leq \lVert z-a\rVert. \tag{1}
\]

#### Proof

The debt homotopy is affine and \([0,1]\) is compact, hence \(P\) is compact.
The checked theorem gives \(P\subset O\) with \(O\) open.  A finite subcover
of \(P\) by balls whose suitably enlarged balls remain in \(O\) gives a
uniform \(\rho>0\) with \(\bigcup_{a\in P}B(a,\rho)\subset O\).  Equivalently,
\(P\) has positive distance from the closed complement \(O^c\).

By `anchoredPath_terminal_not_mem_of_positiveAbsorption`, a positively
absorbing exact anchored block has \(z\notin O\).  The uniform separation
then gives (1).  This is also a compact-segment wrapper around the pointwise
checked theorem
`le_dist_terminal_of_positiveAbsorption_of_ball_subset_allContinueBasin`.
The tube theorem phrases uniqueness with `IsεQuittingRootNash`, while the
basin theorem uses `IsεQuittingRootEndpointNash`; the exact-zero adapter is
`isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash`, already used in
the same basin/tube source chain.
\(\square\)

### Corollary (plateau-anchored summable-seam restart no-go)

Consider finite exact blocks \(B_k\).  Let \(z_k\) be the terminal tail at
which \(B_k\) is anchored, and suppose the restart after that block chooses
an actual source anchor \(a_k\in P\).  Measure its ordinary endpoint seam by

\[
 e_k=\lVert z_k-a_k\rVert.
\]

If \(\sum_k e_k<\infty\), only finitely many \(B_k\) can contain any positive
absorption.  Therefore concatenating these finite blocks cannot create a
persistent marginal.

#### Proof

Every charge-bearing block has \(e_k\geq\rho\) by (1).  A summable
nonnegative sequence has only finitely many terms at least \(\rho\).  The
remaining blocks have zero absorption at every date.  The finitely many
exceptional finite blocks carry only finite total absorption.  Since every
marginal Quit probability is at most the total absorption probability, all
four marginal streams are summable. \(\square\)

This corollary is deliberately scoped.  It rules out restarts whose seam is
the metric endpoint jump from an exact block's terminal tail back to the
actual compact plateau segment.  It does not rule out a different source
reprojection whose error is measured in a genuinely different executable
quantity.  Such a route must explain why that quantity pays for
concatenation despite not controlling this fixed metric jump.

## 2. What happens to an all-summable exact spine

There is a useful generic consumer, but it exposes rather than removes the
source problem.

### Proposition (diagonal-provenance consumer)

Let \((v_n,x_n)\) be a canonical exact bounded Fin4 spine whose four marginal
hazard streams are summable.  Suppose there are semantic-carrier points
\(s_n\in C\), where \(C\) is the terminal semantic carrier, such that

\[
 \operatorname{dist}\bigl(s_n,(v_n,v_n)\bigr)\longrightarrow0. \tag{2}
\]

Then the game has a uniform-equilibrium payoff.

#### Proof

Summability of all marginal hazards implies summability of every opponent
clock.  The checked value-convergence theorem gives coordinatewise
convergence \(v_n\to v_\infty\).  Thus (2) gives
\(s_n\to(v_\infty,v_\infty)\).  The carrier is a closure, hence closed, so
\((v_\infty,v_\infty)\in C\).  Apply
`isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`.
\(\square\)

This is the exact source datum missing from bare all-summable spine
compactness.  At the actual positive-minimum source, every carrier point has
debt sum at least \(D_*>0\), whereas a diagonal pair has debt zero.
Continuity of debt therefore prevents the minimum source from approaching a
diagonal.  One cannot call the positive-minimum provenance in (2) without an
additional debt-discharge construction; doing so would assume the main work.

There is a second precise separation statement.  If an all-summable exact
spine has limit \(v_\infty\in O\), then
`exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue` makes the
whole path constant at \(v_\infty\), with every root all-Continue.  Hence
every nonconstant all-summable exact spine has limit in \(O^c\), and so

\[
 \operatorname{dist}(v_\infty,P)\geq\rho. \tag{3}
\]

Thus a nonconstant all-summable spine does not merely fail to remember its
source infinitesimally: its limit loses the strict-minimum plateau provenance
by a fixed macroscopic amount.

## 3. Selection and optimization rules

Three natural selection rules now have exact obstructions.

1. **Select the locally most absorbing exact root on the plateau.**  This
   returns all-Continue, because it is the unique exact root throughout
   \(O\).  At a cap/state point the stronger checked statement
   `exactCapPrefix_joint_eq_self_of_unique_allContinue` says that the entire
   semantic pair and retained terminal law are fixed and absorption is zero.
   Finite exact cap stacks anchored there are repetitions of all-Continue by
   `capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap`.

2. **Optimize globally among exact punishment-floor orbits.**  Under the
   terminal exploitability witness supplied by no uniform payoff, every such
   orbit has summable absorption, uniformly bounded by the common prefix
   charge.  This is exactly
   `QuittingTerminalExploitabilityWitness.infiniteOrbit_absorptionMass_summable`.
   Therefore no choice, tie-break, lexicographic maximum, or compactness
   selector *within this relation* can force persistence.

3. **Select the maximal semantic-cap prefix ray.**  Under the positive global
   minimum, `summable_maximalCapPrefix_absorption` already proves that its
   absorption series converges.  In addition, the construction points
   outward through progressively prefixed profiles; a forward infinite
   Bellman chronology would require a compatible return/limit argument that
   the current theorem does not supply.

Consequently, a successful optimization rule must leave both the open
all-Continue tube and the exact punishment-floor carrier.  It must also
carry a nonlocal source return; selecting a higher-charge root at unrelated
tails is not enough.

## 4. Small exact boundary tests

### Source-free all-summable spines do not determine a target

In the one-player game with singleton quitting reward \(-1\), let
\(v_n=-1\) and let the Quit probability be

\[
 q_n=2^{-(n+1)}.
\]

At continuation value \(-1\), Quit and Continue both give \(-1\).  Hence
every chosen root is exact Nash and the Bellman identity holds identically.
The spine is bounded and \(\sum_nq_n=1\).  Nevertheless \(-1\) is not a
uniform-equilibrium payoff: the player can choose Never and receive zero.
This example is outside the punishment-normal Fin4 hard residual (for one
player the punishment value is zero while the singleton reward is \(-1\)).
Its role is narrower: it disproves any claim that exactness, boundedness, and
all-summability alone turn the spine's own value into a semantic target.

Taking a constant positive \(q_n\) gives the same local exact spine with a
persistent marginal and the same global deviation.  This is a useful warning
that the persistent-spine consumer also needs the Fin4 hard-residual
normality/source hypotheses stated in the question.

### Zero-persistent and two-persistent edges

- Zero persistence is unavoidable without selection: the canonical
  all-Continue phantom exists in every game.  More strongly, the strict
  Fin4 plateau produces an open family of tails on which every local exact
  selector returns that phantom edge.
- Two persistent marginals are already a downstream success case.  The
  producer does not need to choose their names in advance.  It is enough to
  prove divergence of total marginal charge, because finiteness of
  \(\operatorname{Fin}4\) then supplies one fixed divergent label (and if at
  least two labels diverge, the checked two-label survival interface applies).
- A succession of blocks each having merely positive charge can remain on
  the zero-persistent side; the existing maximal-ray regressions realize the
  summable version of precisely this failure.

## Strongest surviving conclusion

I do **not** obtain the persistent spine, and I do not have a positive-gap
Fin4 counterexample.  The strongest exact reduction surviving the tests is:

> In a hypothetical Fin4 counterexample, neither the actual maximal prefix
> ray, nor any exact punishment-floor orbit selector, nor any restart scheme
> returning charged exact blocks to the strict-minimum debt segment through
> summable metric endpoint seams can produce persistence.  An all-summable
> exact spine is consumable if it asymptotically retains diagonal semantic
> provenance, but the positive minimum prevents that provenance unless an
> additional debt-discharge/source-return theorem is proved.

This narrows the original problem to a non-floor, nonlocal return mechanism.

## Precise next obligation

Construct from the actual Fin4 positive-minimum/hard-residual data one of the
following:

1. a non-floor exact incoming edge or finite block whose terminal tail lies
   outside \(O\), together with an executable return to the source carrier
   whose concatenation error is summable even though the ordinary endpoint
   jump is at least \(\rho\); or
2. a theorem discharging the positive carrier debt along an all-summable
   exact spine so as to establish (2).

Any proposal staying entirely inside the punishment-floor relation or
restarting through ordinary metric seams is blocked by the results above.

## Lean handoff if this no-go is formalized

The useful narrow wrappers would be:

1. compactness of the debt-homotopy segment and existence of a uniform
   radius whose balls lie in the open exact-all-Continue tube;
2. a segment-uniform version of
   `le_dist_terminal_of_positiveAbsorption_of_ball_subset_allContinueBasin`;
3. a sequence corollary: summable plateau-return seam distances imply only
   finitely many charge-bearing exact blocks;
4. under all-marginal summability, an
   `exactSpine_constantAllContinue_or_limit_separated_from_debtSegment`
   wrapper using value convergence and
   `exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue`; and
5. the diagonal-provenance consumer above, using carrier closedness and
   `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`.

These are formalizable boundary lemmas.  They are not the missing producer.

## Addendum: audit of the hazard-capacity proposal

I subsequently audited `gpt/NONZERO_PERSIST_ATTEMPT_1.md`, especially its
Section 1 and residual (28).  The compact combinatorial theorem is sound, but
its advertised game-theoretic consequence needs one additional adapter and
its capacity potential must be placed on trace nodes rather than payoff
states unless concatenation closure is separately proved.

### 5. The near-return block extraction is valid

Let a finite exact block be written in chronological orientation as

\[
 B=(v_0,x_0,v_1,\ldots,x_{n-1},v_n),\qquad
 v_t=F_{x_t}(v_{t+1}),\qquad x_t\in\operatorname{NE}(v_{t+1}),
\]

and put \(h(x)=\sum_iq_i(x)\leq4\).  Suppose a family of such blocks has all
payoff annotations in one compact set and has unbounded finite hazard charge
\(H(B)=\sum_{t<n}h(x_t)\).

For a cover by \(N\) sets of diameter less than \(\delta\), take a block with
charge greater than \(5N\).  Mark the first cumulative-hazard crossings of
\(5j\), \(0\leq j\leq N\).  Since one edge has charge at most four, two marked
payoffs in one cover cell delimit a contiguous exact subblock with endpoint
distance less than \(\delta\) and charge at least one.  Repeating as
\(\delta\downarrow0\), compactness and a fast subsequence give subblocks
\(B_k\), with initial and terminal values \(a_k,b_k\), such that

\[
 H(B_k)\geq1,\qquad
 a_k,b_k\longrightarrow z,qquad
 \sum_k\lVert b_k-a_{k+1}\rVert<\infty.
\]

The orientation at concatenation is correct.  At the last root of \(B_k\),
the original expected tail is \(b_k\), while the flattened annotation at the
next calendar date is \(a_{k+1}\).  The old current annotation is retained.
The one-step tail Lipschitz estimate therefore gives Bellman residual at most
\(d_k=\lVert b_k-a_{k+1}\rVert\), and exact Nash against \(b_k\) gives Nash
defect against \(a_{k+1}\) at most \(2d_k\).  All other dates remain exact.
Thus the literal flattened roots have divergent total marginal hazard and
summable Bellman/root-Nash residuals.  Finiteness of `Fin 4` selects one fixed
divergent marginal.  The constant `5` is correct: a threshold overshoot is
strictly less than four, so adjacent marked levels retain at least one unit.

This is a valid **paper-level approximate-spine selection theorem**.  In fact,
the trace-safe/source-provenance hypothesis is logically unused once the
inputs are same-table exact Nash--Bellman blocks in one compact value set:
every contiguous subblock is automatically another exact block.  The
artificial seams are not actual source traces, but the consumers in the next
section only need the literal roots and the controlled residuals.  Source
provenance remains relevant for proving that a proposed producer really
supplies the finite blocks; it is not needed by the compact extraction.

### 6. The current persistent consumers do not accept the conclusion verbatim

The exact paper-level adapter to use is the following.

#### Theorem (summable-residual persistent-spine adapter)

Let \(r\) be a finite quitting game in which every player is
punishment-normal.  Suppose \(w_t\) is uniformly bounded, \(y_t\) is a product
root sequence, and \(\beta_t,\nu_t\geq0\) are summable, with

\[
 \lVert w_t-F_{y_t}(w_{t+1})\rVert_\infty\leq\beta_t \tag{32}
\]

and, for every player \(i\) and mixed one-row replacement \(z_i\),

\[
 F_{y_t[i\leftarrow z_i]}(w_{t+1})_i
 -F_{y_t}(w_{t+1})_i\leq\nu_t. \tag{33}
\]

If at least one fixed marginal stream \(\sum_tq_i(y_t)\) diverges, then the
game has a uniform-equilibrium payoff.

This theorem covers unrestricted behavioral deviations because its last step
in both persistence branches is an existing terminal/all-behavior consumer,
not a stationary-deviation argument.  It is stronger than an
“arbitrarily-small total error” interface: one supplied spine with finite
total error suffices, since its tails have arbitrarily small total error.

The existing checked consumers are exact at the interface where the proposal
is approximate:

- `IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_persistent`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/NormalUniquePersistentNashBellmanSpine.lean`
  assumes an exact Bellman recursion and exact root Nash;
- `QuittingChronologicalDebtData.ofNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/NashBellmanChronologicalForcing.lean`
  makes prescribed and direct-debt defects zero using those same exact
  hypotheses;
- `quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors`
  in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean`
  consumes a `QuittingSummableSeamSource`, whose seams are prescribed/cap
  semantic-pair seams.  It does not directly take scalar Bellman and local
  root-Nash residual bounds.

Therefore the sentence “unbounded source capacity is already enough” is not
yet a checked corollary, and should not be exported without an adapter.
Calling the concatenation “trace-safe” does not fill this gap: every root is
copied from an actual block, but the last root of each block is evaluated at
a new artificial successor tail.

There is, however, a narrow paper-level adapter rather than a counterexample.
For an approximate spine \((w_t,y_t)\), define

\[
 S_t=(w_{t+1},w_{t+1}),\qquad
 C_t=\operatorname{Prefix}_{y_t}(S_t).
\]

Then \(C_t=\operatorname{Prefix}_{y_t}(S_t)\) is an exact artificial seam-chain
step by definition.  Its prescribed coordinate differs from \(w_t\) by the
Bellman residual.  Its debt is the one-row unilateral gain and is bounded by
the root-Nash residual.  Consequently the prescribed seam between \(S_t\)
and \(C_{t+1}\) is bounded by the next Bellman residual, and the cap seam is
bounded by Bellman plus Nash residual.  After shifting sufficiently far, all
these seam tails and the initial candidate debt are as small as required.

If at least two fixed marginals are persistent, the checked two-label theorem
supplies joint and every player-deleted survival for these same literal roots.
The preceding bounds give a `QuittingBoundedSeamChain`; shifting sufficiently
far makes its playerwise prescribed and total seam sums and initial debts less
than any requested positive accuracy.  Therefore the checked
`quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors`
consumer applies.  This is an ordinary proof using the checked structures,
although the construction has not been packaged as a Lean declaration.

If exactly one owner \(p\) is persistent, all other marginal streams are
summable.  Let \(U_t\) be the literal terminal payoff of the root schedule
starting at \(t\).  Persistence gives zero joint survival, hence \(U_t\) is
bounded and obeys the exact Bellman recursion.  Iterating the approximate
Bellman relation gives

\[
 \lVert w_t-U_t\rVert
 \leq\sum_{s\geq t}\beta_s; \tag{31}
\]

the terminal remainder vanishes by joint survival.  The checked exact
bounded-Bellman concentration estimate applied to \(U\), together with the
summable opponent clock, gives
\(U_t\to\operatorname{SoloReward}(p)\), and therefore the same holds for
\(w_t\).  Choose increasing dates with \(q_p(y_t)>0\).  At those dates the
opponent hazard tends to zero.  Approximate root Nash and Bellman give, for
every outsider, the pure-Quit endpoint bound with error at most
\(\nu_t+\beta_t\), which tends to zero.  The checked flexible endpoint
consumer
`isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits` in
`UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean`
then applies using punishment normality.

Thus the strengthened safe conclusion is:

> Unbounded finite hazard capacity for same-table exact Nash--Bellman blocks
> in one compact value set implies a uniform-equilibrium payoff for the
> punishment-normal Fin4 residual, by an ordinary
> mathematical adapter from the selected summable-error spine to the checked
> two-persistent or solo endpoint consumer.

The compact extraction is paper-level, as are the two short adapter wrappers;
no single checked declaration currently states this capstone.  It is valid as
a mathematical reduction but should not be described as already Lean-checked.

### 7. Interaction with the plateau moat

The capacity extraction does not evade the moat by compactness.  Once
\(\delta<\rho\), a charge-bearing near-return subblock cannot have its initial
endpoint in the strict-minimum segment \(P\): its terminal anchor lies outside
\(O\), while every point of \(P\) is at least \(\rho\) away.  Hence an
unbounded-capacity family can feed the extraction only after its contiguous
source trace has left the minimum plateau.  “Every subblock retains source
provenance” must mean provenance at a reachable off-plateau trace node; it
cannot mean that every extracted block is still anchored at the original
minimum pair.

Conversely, suppose a chronological exact block starts at \(a\in P\), ends at
\(z\), and has positive charge.  Then \(z\notin O\), so
\(\lVert z-a\rVert\geq\rho\).  If all reward and value coordinates are bounded
by \(M>0\), the exact Bellman variation estimate gives

\[
 \rho
 \leq \lVert v_0-v_n\rVert
 \leq\sum_{t<n}\lVert v_t-v_{t+1}\rVert
 \leq2M\sum_{t<n}a_t
 \leq2M H(B),
\]

where \(a_t\) is row absorption.  Thus every exact departure from the source
segment costs at least

\[
 c_P:=\rho/(2M)>0. \tag{29}
\]

If a composable trace-capacity potential exists, such a departure causes a
strict capacity drop of at least \(c_P\).  This is a genuine strengthening of
the moat.  It is only a one-source drop: the current source machinery does
not supply a new positive-minimum trace node after departure, nor a uniform
lower bound for the moat radii of successive regenerated sources.  Also, an
exact positive-charge block cannot end back in \(P\) at all; backward basin
rigidity makes every exact block terminally anchored in \(O\) all-Continue.

### 8. Capacity belongs on traces, and it is not a well-founded rank

For the unrestricted exact Nash--Bellman edge relation on a fixed compact
value set, legality is Markov in the payoff state, so the formula

\[
 \Phi(s)=\sup\{H(B):B\text{ is an exact block beginning at }s\}
\]

satisfies

\[
 \Phi(s)\geq h(x)+\Phi(s') \tag{30}
\]

because an exact edge \(s\xrightarrow{x}s'\) can be prepended to every exact
continuation beginning at \(s'\).  No maximizer is needed.  Under hypothetical
Fin4 nonexistence, the preceding unbounded-capacity criterion makes this
global \(\Phi\) finite.

For a **source-restricted** formula, however, (30) holds only when a legal
edge can be prepended to every source-legal continuation counted at \(s'\).
Closure under taking contiguous subblocks does not imply this concatenation
property: source legality may remember which terminal profile, law, marked
atom, or history reached the same payoff vector.

The unconditional repair is to make the state a source trace/history
\(\tau\), and define \(\Phi(\tau)\) from its legal finite extensions.  Then

\[
 \Phi(\tau)\geq h(e)+\Phi(\tau e)
\]

holds without attainment: apply the definition to every finite continuation
after \(e\) and take the supremum.  Finite capacity makes \(\Phi\) a finite
real budget and bounds hazard on every branch.  It does **not** make \(\Phi\)
a well-founded rank.  For example, on the compact graph

\[
 S=\{0\}\cup\{2^{-n}:n\in\mathbb N\},
\]

give the edge \(2^{-n}\to2^{-(n+1)}\) charge \(2^{-(n+1)}\), and give the
limit self-loop \(0\to0\) charge zero.  The edge relation is closed and the
charge is continuous.  Capacity is

\[
 \Phi(2^{-n})=2^{-n},
\]

so it drops strictly forever along one infinite branch.  There is no
well-founded descent, and the finite-path supremum at \(2^{-n}\) is not
attained by any finite path.

Nor do compactness, a closed edge graph, continuous charge, and a uniform
finite-capacity bound imply upper semicontinuity or attainment.  A concrete
compact comb is

\[
 S=\{r\}\cup(\{0\}\times[0,1])
   \cup\bigcup_{n\ge2}\{(1/n,k/n):0\leq k\leq n\}.
\]

Include zero-charge edges \(r\to(1/n,0)\) and \(r\to(0,0)\), row edges

\[
 (1/n,k/n)\to(1/n,(k+1)/n)
\]

of charge \((1-1/n)/n\), and zero-charge self-loops on
\(\{0\}\times[0,1]\) and at every finite row endpoint \((1/n,1)\).
This is a closed compact edge graph and the charge is continuous on it.  Yet

\[
 \Phi(1/n,0)=1-1/n\longrightarrow1,qquad
 \Phi(0,0)=0.
\]

Thus \(\Phi\) is not upper semicontinuous at \((0,0)\).  Moreover
\(\Phi(r)=1\), but no finite or infinite path from \(r\) realizes charge one.
Fixed-length value functions may attain maxima; the supremum over all lengths
need not.

### 9. Exact source ports and the closure actually used

There are two different interfaces, which the phrase “trace-safe family” in
the draft conflates.

#### Block-extraction port

A compact exact block port consists simply of an index set \(A\) and, for each
\(\alpha\in A\), a finite chronological word

\[
 B_\alpha=(v^\alpha_0,x^\alpha_0,\ldots,
   x^\alpha_{n_\alpha-1},v^\alpha_{n_\alpha})
\]

for the same reward table, satisfying exact Bellman and exact root Nash at
each edge, with every value in one compact set \(K\).  The unbounded-capacity
hypothesis is \(\sup_\alpha H(B_\alpha)=\infty\).

Section 1 uses no concatenation or ancestry closure on \(A\).  It only takes
a contiguous interval of a chosen block; exact Bellman/Nash is automatically
inherited.  Optional source witnesses may be restricted to that interval,
but the approximate concatenation does not remain one actual source trace.
The summable-residual adapter above is exactly why no cross-seam source trace
is needed.

Thus an actual Fin4 source attaches to the unbounded-capacity theorem once it
provides arbitrarily charged **chronologically oriented** finite exact blocks
in a common compact value set.  It is not enough to provide nominal root
words or outward predecessor equations without explicitly reversing them
into

\[
 v_t=F_{x_t}(v_{t+1}),\qquad x_t\in\operatorname{NE}(v_{t+1}).
\]

The current maximal-prefix ray can be read as finite chronological ancestry
blocks by reversing its outward predecessor order, but its charge is already
summable by `summable_maximalCapPrefix_absorption`.  Hence it supplies a
bounded-capacity instance, not the unbounded premise.

#### History port for the capacity dynamic program

For a source-restricted Bellman principle, more structure is necessary.  A
canonical port is a prefix-closed set \(T\) of finite histories, with a compact
value annotation \(V(\tau)\), complete actual-source witness \(\Sigma(\tau)\),
and for every one-step extension \(\tau e\in T\) a root \(X(\tau,e)\) such
that

\[
 V(\tau)=F_{X(\tau,e)}(V(\tau e)),\qquad
 X(\tau,e)\in\operatorname{NE}(V(\tau e)). \tag{34}
\]

The witness at \(\tau e\) must restrict to the witness at \(\tau\); this is
the ancestry condition.  Legal continuations after \(\tau\) are precisely
its extensions in \(T\).  Define

\[
 \Phi_T(\tau)=\sup\{H(\sigma\setminus\tau):
   \tau\preceq\sigma\in T\}.
\]

Then, for every legal child,

\[
 \Phi_T(\tau)\geq h(X(\tau,e))+\Phi_T(\tau e). \tag{35}
\]

The proof uses the extension/ancestry closure: every continuation of
\(\tau e\) is also a continuation of \(\tau\) after the displayed edge.
Attainment is unnecessary.  Prefix closure by itself gives subblocks but not
(35); extension compatibility is the additional axiom.

Collapsing \(\tau\) to \(V(\tau)\) is valid only if histories with the same
payoff have identical admissible future sets, or if one deliberately enlarges
to the unrestricted Markov exact-edge graph.  A minimal exact regression is
the all-indifferent zero-reward table at payoff zero.  Give two source-history
tags \(A,B\) the same payoff.  From tag \(A\), permit one positive-hazard exact
edge and then stop; from tag \(B\), permit a long positive-hazard exact word,
but forbid it after \(A\).  All words and subwords are exact.  The
payoff-collapsed capacity at zero sees the long \(B\)-continuation, so applying
the statewise Bellman inequality to the \(A\)-edge falsely demands “one edge
charge plus the \(B\)-capacity.”  The history capacities correctly keep the
two futures separate.

The source port does not repair orientation automatically.  If the actual
construction grows predecessors by
\(V(\tau e)=F_X(V(\tau))\), it is reverse-chronological.  One may extract each
finite ancestry chain in reverse order for the block-extraction theorem, but
it does not thereby become a forward prefix-extension tree satisfying (34).
A DP or regeneration argument must specify which oriented history is being
extended.

No currently inspected positive-minimum declaration supplies an unbounded
instance of this chronological block port or a regenerative history port with
a well-founded rank.  The port definition discharges the ambiguity in the
conditional theorem; it is not an actual-data producer.  In particular, a
terminal-semantic carrier point, a cap-Nash root, or a retained law is not by
itself an instance: the source-to-port adapter must output the literal
chronologically oriented `IsQuittingNashBellmanEdge` certificates (or their
equivalent Bellman and Nash fields) and compatible history witnesses.

### Revised residual after the audit

The finite-capacity alternative (28) is therefore a valid paper-level
reduction after inserting the adapters above, but capacity alone is a
summable real resource, not the requested well-founded regeneration rank.
The moat supplies the quantitative one-time drop (29) for an exact departure
from the actual minimum segment.  The remaining mathematical obligation is,
in the finite-capacity branch, a trace-safe regeneration theorem whose
new source rank lies in a discrete/well-founded set, or whose capacity drop
has a uniform positive lower bound across every regenerated source.

Formalization would additionally need the approximate-spine seam-chain and
unique-persistent wrappers from Section 6.  The mathematical regeneration
does not follow from upper semicontinuity or attainment of \(\Phi\), because
those properties fail even for compact closed continuous abstract graphs.

## Declaration-level handoff: four independent packets

The following packets should remain separate in review and formalization.
Packets A, B1, and B2 together give the generic unbounded-capacity criterion;
Packet C describes the genuinely open finite-capacity residual.  The moat
packet is an independent boundary theorem group.

### Packet A — unbounded finite hazard capacity extraction

**Suggested declaration**
`exists_summableResidual_persistentSpine_of_unbounded_finiteHazardCapacity`.

**Minimal hypotheses**

- a nonempty finite player type and one fixed reward table;
- a family of finite chronological exact Nash--Bellman blocks;
- all displayed payoff vectors lie in one compact set \(K\);
- their total marginal hazard charges are unbounded.

No punishment normality, source provenance, ancestry closure, common
endpoint, or attainment hypothesis is used.

**Conclusion**

For every \(\eta>0\), obtain bounded \(w_t\), literal product roots \(y_t\),
and nonnegative residuals \(\beta_t,\nu_t\) satisfying (32)--(33),

\[
 \sum_t(\beta_t+\nu_t)<\eta,
 \qquad \sum_t\sum_iq_i(y_t)=\infty.
\]

Hence one fixed marginal diverges.  A useful intermediate declaration is the
compact-cover lemma extracting, for every \(\delta>0\), a contiguous block of
charge at least one and endpoint distance below \(\delta\).  Tail stability
can reuse `isεQuittingRootEndpointNash_of_tail_close` from
`UniformEquilibrium/Quitting/Root/TailStability.lean`, or prove the direct
full-replacement bound used in (33).  The finite path representation can
reuse `QuittingFiniteNashBellmanPath` and
`quittingFiniteNashBellmanPathRoots` from
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanMinimizer.lean`.

**Status:** complete ordinary proof; not Lean-checked.

### Packet B1 — two-or-more-persistent summable-residual consumer

**Suggested declaration**
`quittingGame_exists_uniformEquilibriumPayoff_of_twoPersistent_summableNashBellmanResidual`.

**Minimal hypotheses**

- a bounded annotation/root sequence satisfying (32)--(33);
- `Summable β` and `Summable ν`;
- `HasTwoPersistentQuittingMarginals y`.

Punishment normality and source provenance are unnecessary.

**Construction and exact bounds**

Set

\[
 S_t=(w_{t+1},w_{t+1}),\qquad
 C_t=\operatorname{Prefix}_{y_t}(S_t).
\]

Use these as `QuittingBoundedSeamChain.successor` and `.candidate`.  For each
player,

\[
 0\leq\operatorname{Debt}(C_t)\leq\nu_t,
\]

because diagonal-prefix debt is exactly the best one-row replacement gain.
Moreover,

\[
 \operatorname{prescribedSeam}_t\leq\beta_{t+1},\qquad
 \operatorname{capSeam}_t\leq\beta_{t+1}+\nu_{t+1},
\]

so `totalSeam ≤ 2 * β + ν` after the index shift.  Shift the whole chain far
enough to meet an arbitrary positive `eta` budget and the initial-debt bound.
Use
`QuittingBoundedSeamChain.nonempty_chronologicalDebtShadowingCertificate_of_twoPersistent`
and then
`quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors`,
both in
`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean`.
The survival facts ultimately come from
`QuittingChronologicalDebtShadowingSurvivalFields.of_twoPersistent` in
`UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`.

**Status:** complete ordinary adapter to checked unrestricted-behavior
consumers; wrapper not Lean-checked.

### Packet B2 — unique-persistent normal consumer and Fin4 capstone

**Suggested declarations**

- `isUniformEquilibriumPayoff_soloReward_of_uniquePersistent_summableNashBellmanResidual`;
- `quittingGame_exists_uniformEquilibriumPayoff_of_finFour_unbounded_finiteHazardCapacity`.

**Minimal generic hypotheses**

- a bounded annotation/root sequence satisfying (32)--(33), with summable
  \(\beta,\nu\);
- one owner \(p\) has nonsummable marginal hazard;
- every other marginal hazard is summable;
- \(p\) is punishment-normal.

**Proof interface**

Let \(U_t\) be the literal root-sequence terminal payoff.  Joint survival is
zero because \(p\) is persistent.  The exact Bellman recursion for \(U\) and
summable Bellman residual give (31), hence \(w_t-U_t\to0\).  Apply
`abs_value_sub_soloReward_le_of_bounded_bellman` from
`UniformEquilibrium/Quitting/Classification/Existence/NormalUniquePersistentNashBellmanSpine.lean`
to \(U\).  Along increasing dates with \(q_p(y_t)>0\), use

\[
 \operatorname{FixedOpponentsQuitValue}_i(y_t)
 \leq w_t(i)+\beta_t+\nu_t
 \quad(i\ne p),
\]

the vanishing opponent hazard, and \(w_t\to\operatorname{SoloReward}(p)\).
Feed these to
`isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits` in
`UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean`.
This checked endpoint covers arbitrary behavioral deviations.

For literal `Fin 4`, argue by contradiction from no uniform payoff.  Obtain
`FinFourQuantitativeFullSupportHardResidual` using
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
its `all_punishmentNormal` field supplies the B2 hypothesis.  Packet A gives
a nonempty persistent set.  Use B1 if it has at least two labels and B2 if it
has exactly one.  Therefore every compact family of same-table finite exact
Fin4 blocks has finite hazard capacity under no uniform payoff.

**Status:** complete ordinary proof to checked endpoint consumers; wrappers
and combined capstone not Lean-checked.  The repository already contains the
exact Bellman concentration, exact unique-persistent compiler, and exact Fin4
hard-residual marginal-summability theorem; these should be reused, not
reimplemented.  Only their summable-residual wrappers and the Packet-A
capstone are new obligations here.

### Packet C — finite-capacity potential and sharp no-gos

**Suggested definitions/declarations**

- `quittingExactFiniteHazardCapacity` on the unrestricted compact exact-edge
  graph;
- `QuittingActualSourceHistoryPort` with prefix-compatible witnesses and the
  chronological orientation (34);
- `QuittingActualSourceHistoryPort.capacity_drop` proving (35);
- abstract regressions showing that finite real capacity is not a
  well-founded rank, need not be attained, and need not be upper
  semicontinuous.

**Minimal valid dynamic-program hypotheses**

On the unrestricted exact graph, payoff-state Markov concatenation is enough.
On a source-restricted graph, use history nodes and require that every legal
continuation of a child is also the corresponding extension of its parent.
Subblock/prefix closure alone is insufficient.  No attainment is needed for
the Bellman inequality.

**Conclusions and nonconclusions**

Finite capacity bounds every branch's total hazard.  It does not yield
termination or well-founded regeneration.  The dyadic-chain example gives an
infinite strict capacity descent, and the compact comb gives failure of upper
semicontinuity and nonattainment even with a closed compact edge graph and
continuous charge.  Thus residual (28) still needs a discrete rank, a uniform
positive drop across every regeneration, or a direct all-summable consumer.

**Status:** dynamic inequality and regressions are complete ordinary
mathematics; no actual positive-minimum regeneration producer is supplied.

### Separate moat packet — plateau restart obstruction and one-time drop

**Suggested declarations**

- `exists_finFour_minimumDebtSegment_uniform_allContinueRadius`;
- `le_dist_minimumDebtSegment_terminal_of_positiveAbsorption`;
- `finite_positiveAbsorptionBlocks_of_summable_minimumSegmentSeams`;
- `minimumSegment_departureHazardCapacity_drop`.

Start from
`exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`
and compactness of the affine debt segment.  Use
`anchoredPath_terminal_not_mem_of_positiveAbsorption` and
`le_dist_terminal_of_positiveAbsorption_of_ball_subset_allContinueBasin` from
`UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`.
The exact-zero Nash/endpoint adapter is
`isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash`.

The first three declarations give the uniform radius \(\rho\), the terminal
separation, and the summable-seam restart no-go.  For a block starting on the
segment, combine the separation with
`abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass` in
`UniformEquilibrium/Quitting/Debt/Marked/TimeAdvance.lean` to obtain the
one-time hazard/capacity drop \(\rho/(2M)\).  This drop does not iterate without
a regenerated source carrying a uniform moat bound.

**Status:** complete ordinary theorem group from checked ingredients; not a
persistent-spine producer and not Lean-checked as a group.
