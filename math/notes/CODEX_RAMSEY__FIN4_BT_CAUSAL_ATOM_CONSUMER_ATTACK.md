# Fin4 BT causal-atom consumer attack

**Owner:** `CODEX_RAMSEY`  
**Status:** `IN PROGRESS — NO ACCEPTED OUTPUT 1–4`  
**Canonical target:** [`FIN4_BT_QUESTION.md`](../FIN4_BT_QUESTION.md)

## 1. Exact question

Work under the complete hypotheses of `FIN4_BT_QUESTION`: `Fin 4`, a
positive terminal exploitability witness and quantitative hard residual, a
positive global semantic-debt minimum, the literal tangent/response rectangle,
the joint rectangle-law limit, the global and fixed-law reset minimizers, and
the selector-independent inert condition that every exact cap root at the
relevant minimizer is all-Continue.  The required output is one of the four
semantic consumers in that question (or an actual positive-gap table).

This note does **not** claim such an output.  It records the deductions used
in the current attempt so that no source/law/cap identification is silently
introduced.

## 2. Sources inspected

The exact declarations used or checked were:

- `QuittingStoppingLawCommonResponseWitness` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`;
- `QuittingStoppingLawRectangleResetFaceDispatch`,
  `QuittingStoppingLawRectangleJointAtomLimit`,
  `QuittingStoppingLawRectangleJointAtomLimit.exists_fixedLawResetDispatch`,
  and `QuittingStoppingLawRectangleJointAtomLimit.nonempty_minimizerBridge` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`;
- `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `maximalCapPrefix_positivePunishmentCharge_retainingAtom_or_uniqueAllContinue`
  and the finite charge-capacity estimates in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionDispatch.lean`;
- the checked small-debt seed interface in
  `UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`;
- the direct positive-minimum seed obstruction in
  `UniformEquilibrium/Diagnostics/Quitting/PositiveMinimumSeedSeamBarrier.lean`;
- the two-reservoir and harmonic interfaces in
  `Research/Quitting/TwoReservoirConsumer.lean` and
  `Research/Quitting/HarmonicReservoirConsumer.lean`;
- the reviewed macroscopic-stage extraction in
  [`CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md`](CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md);
- the reviewed singleton regeneration/sign screen in
  [`CODEX_EULER__FIN4_REACHED_SINGLETON_EXIT_REGENERATION_SCREEN.md`](CODEX_EULER__FIN4_REACHED_SINGLETON_EXIT_REGENERATION_SCREEN.md);
- the opponent-tight realization declarations in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
- `stagePureEndpoint_shiftedProfiles_commonTail` and
  `rectangleEndpoint_localStateMatch` in
  `Research/Quitting/CausalEndpointAtomLocalStateMatch.lean`;
- `quittingSequentialSoloProfile_follower_gain_eq` and the aligned-repair
  boundary in
  `UniformEquilibrium/Quitting/Boundary/Repair/AlignedPreemptionCollision.lean`;
- the static-cycle chronology barrier in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StaticCycleChronologyBarrier.lean`;
- the exact missing signed-lasso fields in
  `UniformEquilibrium/Quitting/Classification/Existence/PrioritizedPreemptionSeedBoundary.lean`;
- `FlatCirculationSupportRankElimination.lean`, and the existing rectangle
  compatibility/no-go sources under `Research/Quitting`;
- `exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
- `exists_reextractedFrontier_of_minimumFiberEndpoint` and
  `reducedSupportRankAlternative` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean`;
- `isUniformEquilibriumPayoff_of_cyclicNashBellmanCycle` in
  `UniformEquilibrium/Quitting/Cycles/CyclicKofNBellmanBridge.lean`; and
- `not_forall_liveRoot_eq_supportedCyclicWord_of_proper_resetChain` in
  `UniformEquilibrium/Diagnostics/Quitting/CyclicKofNSupportedRootRetentionNoGo.lean`.

## 3. Exact deductions used in the attempted conversion

### 3.1 Same-law zero-debt identifies one cap coordinate, but not a root

Let `(g,mu)` be the limiting literal rectangle endpoint and let `(f,mu)` be
the fixed-law observer-reset minimizer.  Both have observer debt zero.  Since
their common law gives the same prescribed reward moment,

\[
 U_o(g)=U_o(f)=\sum_A\mu(A)r_o(A).
\]

Zero observer debt therefore also gives

\[
 B_o(g)=B_o(f)=U_o(g)=U_o(f).                 \tag{3.1}
\]

This is useful bookkeeping: there is no observer-cap mismatch between the
two same-law reset points.  It does **not** turn the common pure-time response
inside the literal endpoint profiles into a time-zero action against `B(f)`.
If the selected response times escape, the response remains an event in a
shifted actual suffix.  If they stay finite, only the observer coordinate is
made tight.  In neither case are the other date-zero actions a cap Nash root
at `f`.

### 3.2 The positive suffix atom cannot be used as the chronological seed

The checked packet iteration requires, for every player,

\[
 d_i(\text{seed})\le\eta.
\]

At a positive minimum of total debt `D_*`, some coordinate has debt at least
`D_*/4`.  The checked direct-seam theorem moreover says that replacing the
minimum by a coordinatewise `eta`-small anchor incurs a semantic seam at least

\[
 D_*/4-\eta
\]

in one coordinate.  Retaining a positive terminal-law coordinate changes
neither statement.  Thus the causal suffix atom is not the missing external
small-debt seed.

### 3.3 Exact cap causalization reaches the sharp all-Continue wall

For a positive finite law atom, causalization supplies arbitrarily deep
literal exact cap-Nash words and keeps the atom in the actual suffix.  The
maximal-root dispatch then gives exactly:

1. a positive-charge exact punishment-floor prefix retaining the atom, which
   is already an accepted semantic entrance; or
2. every exact cap root at the displayed tail is all-Continue.

In the second case the prefix word only delays the same suffix.  Its charge is
zero, its semantic pair is fixed, and the suffix atom is not moved into a
prefix root.  The full terminal witness remains a prescribed-payoff debt of
the suffix.  Hence neither the atom nor its macroscopic stage mass pays the
`B-U` surcharge.

### 3.4 Macroscopic nonsingleton extraction still leaves an unsigned row

If a retained coalition has size at least two and law mass `s`, the reviewed
product-law argument selects a literal reached stage of mass at least

\[
 \frac{s^3}{8\binom42}.
\]

After the causal prefix survival floor this remains a fixed positive actual
stage mass.  At that stage the causal collision dispatch supplies a fixed
off-minimum tail excursion or a fixed profitable endpoint with debt transfer.
The reached root is not Nash against its suffix cap.  Replacing it by an exact
cap root changes the literal row whose atom was selected.  In the transfer
arm the mover's lost debt can be redistributed among the other three
coordinates; neither total debt nor positive-debt support must fall.

For a reached singleton, an arbitrarily small outsider activation preserves
the suffix and creates an overlapping pair, but the hard singleton collision
gap only yields

\[
 G\ge(\Gamma+2M)w-2M,                         \tag{3.2}
\]

where `w` is the conditional mass of the advertised singleton row.  The
finite-law and deep-causal inputs do not force the threshold needed to make
(3.2) positive.

### 3.5 Why the negative response-square curvature has not yet closed

For the observer, its behavioral cap is independent of its own prescribed
strategy.  On the literal mover/observer four-corner square, the observer-cap
square is therefore zero.  The common-response inequality makes the
observer-debt square strictly negative.  This is the correct curvature sign.

The total-debt square also contains the three other cap/debt curvatures.  The
current hypotheses do not orient their sum.  They can compensate the negative
observer square while every corner remains above `D_*`.  At infinitesimal
scale this is precisely the flat-transfer/circulation algebra already handled
by `FlatCirculationSupportRankElimination`: it yields positive slope, support
entry, or paid-row exits, but the presently missing consumers for those exits
are not supplied by the suffix atom.

### 3.6 Block renewal of positive Never mass is not yet a shortcut

A tempting law-level construction truncates the limiting product clocks into
long blocks and, after joint survival of a block, restarts fresh independent
copies.  This is an executable profile and normalizes the finite terminal
law.  The unrestricted deviation cap, however, also sees all later blocks.
Controlling it requires solving the induced renewal tail game.  In the hard
nonprojective branch this is the stationary/renewal equilibrium problem, not
a consequence of the finite atom.  The compact-bubble and escaping-cap
exchange identities decode the resulting moving events, but do not make the
renewed profile terminal Nash or lower its total debt.

## 4. The sharp common-tail repair test

The common-tail localization has a precise but limited conclusion.  If a
one-stage endpoint update is made at a reached date, the two shifted profiles
have roots

\[
 q,\qquad q[i\leftarrow a]
\]

at date zero and exactly the same roots at every later date.  It does **not**
say that either date-zero root is Nash against the shared tail.  In the
positive reached-row branch the checked theorem is stronger in the opposite
direction: the advertised root has a fixed positive Nash error on that same
root--tail fiber.

The collision-destroying repair has the following literal form.  At the
pair `{o,k}`, player `k` strictly prefers Continue, leaving the singleton
`{o}`.  A hard-residual singleton collision makes another player join `o`.
If the old sure owner then leaves, the same construction moves to the next
singleton.  All these endpoint profiles may share one literal suffix, but
their profitable join/leave inequalities are independent of that suffix.
Consequently none of the displayed pure pair or singleton vertices is an
exact Nash root.  Turning the vertices into a temporal word is also illegal:
the first nonempty pure root has zero joint survival, exactly as formalized by
`quittingJointSurvivalWeight_naiveStaticCoalitions_eq_zero`.

### 4.1 The strongest sure-row absorption statement

Fix an observer `o`, prescribe `o` to Quit surely, and solve the induced
binary game on `univ.erase o`.  Let `N_o` be its compact nonempty Nash set and
let

\[
 A_{-o}(x)=1-\prod_{j\ne o}(1-p_j(x))
\]

be the probability that at least one complementary player Quits.  The hard
singleton collision at `{o}` excludes the all-Continue complementary point
from `N_o`: its selected collider has a strict Quit gain at least `Gamma`.
Consequently compactness and continuity give an attained constant

\[
 \beta_o:=\min_{x\in N_o}A_{-o}(x)>0.             \tag{4.A}
\]

This is a genuine uniform absorption floor on the entire induced equilibrium
set, not merely on a selected equilibrium.  It is also the sharp output of
the sure-row reduction.  It is **not deviation-uniform**.  If an equilibrium
has only one active complementary coordinate `k`, a unilateral deviation of
`k` to Continue makes `A_{-o}=0`; the collision theorem then says that some
complementary player would want to Quit at the resulting row, but it does not
preserve absorption during `k`'s unilateral comparison.  Thus (4.A) does not
supply the denominator bound required by the proposed dummy-removal argument.

Using two sure base players makes root absorption survive every unilateral
deviation, but then the available singleton collision only proves one base
player's leave sign at the pure empty-free corner.  It gives no sign after an
arbitrary coalition of the two induced free players.  The checked
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` therefore remains
blocked by the second base leave inequality.  The collision-cycle
background-cancellation theorem moreover shows that even the first leave
sign can reverse on a nonempty background, so it cannot be extended
uniformly from normality.

### 4.2 Exact common-tail regression

The following finite binary root game shows that the common tail and the
response-square sign do not repair this defect.  It is a local regression,
not a counterexample to `FIN4_BT_QUESTION`.

Use players `0,1,2` and continuation value zero.  For player `i`, write
`Delta_i(A)` for Quit minus Continue when the opponents quitting at the row
are exactly `A`.  Set

\[
\begin{array}{c|rrrr}
 &\varnothing&\text{first opponent}&\text{second opponent}&
     \text{both opponents}\\ \hline
\Delta_0&-1&-1&+1&-1\\
\Delta_1&-1&+1&-1&-1\\
\Delta_2&-1&-1&+1&-1,
\end{array}                                                    \tag{4.1}
\]

where the opponent orders are `(1,2)`, `(0,2)`, and `(0,1)`.  This is an
ordinary quitting row table: set every coordinate on coalitions omitting the
coordinate owner to zero, and set the corresponding row containing the owner
equal to the displayed difference.

The pure better-response graph contains the strict hexagon

\[
 \{0\}\to\{0,1\}\to\{1\}\to\{1,2\}
 \to\{2\}\to\{0,2\}\to\{0\}.                    \tag{4.2}
\]

The alternating arrows are respectively a singleton join and the old
owner's leave from a pair.  For mover `0`, observer `1`, and player `2`
Continuing, the observer's Quit gain is

\[
             \Delta_1(p_0,0)=-1+2p_0.              \tag{4.3}
\]

Thus the mover update from Continue to Quit has positive response-square
cross difference `2`; at its endpoint observer `1` strictly prefers Quit.
The two endpoint profiles are attached to the same literal all-Continue,
zero-value tail; the checked common-tail theorem records this exact shared
suffix.

Nevertheless all-Continue is the **unique** mixed Nash root.  If
`p=(p_0,p_1,p_2)` are the three Quit probabilities, multilinearity gives

\[
\begin{aligned}
 \Delta_0(p)&=-1+2p_2(1-p_1),\\
 \Delta_1(p)&=-1+2p_0(1-p_2),\\
 \Delta_2(p)&=-1+2p_1(1-p_0).                       \tag{4.4}
\end{aligned}
\]

If one `p_i` is zero, the cyclic support inequalities force the next
probability, and then all three probabilities, to be zero.  Otherwise every
`p_i>0`, so Nash support optimality would require

\[
 p_2(1-p_1),\ p_0(1-p_2),\ p_1(1-p_0)\ge\tfrac12.
\]

Multiplying gives

\[
 \prod_i p_i(1-p_i)\ge\tfrac18,
\]

whereas `p_i(1-p_i)<=1/4` gives a product at most `1/64`, a contradiction.
Adding a fourth player whose Quit action is strictly dominated embeds the
regression literally in `Fin 4`.  One may also give the fourth singleton a
static collider by changing only payoff cells with that fourth opponent
present; the fourth player is absent from every Nash root, so (4.4) and
uniqueness remain unchanged.

This calculation rules out the hoped-for implication

```text
common literal tail + sharp strict-preemption repair cycle
+ positive response-square cross difference
  => positive exact cap root or exact common-tail block.
```

The regression has negative own singleton values, literal all-Continue is an
exact terminal Nash profile, and the global debt minimum is zero.  It
therefore does **not** meet the terminal-witness or `D_*>0` premises and is
not an accepted refutation.  Its only legitimate use in the full problem is
to identify what must be supplied by those ambient hypotheses: a
source-matched inequality on the other players' mixed-face cap values, or a
law-preserving/minimum-preserving way to transport the observer response
through every repair.  Neither field is present in the response-square or
common-tail declarations.

### 4.3 Why complementary active-root phases do not retain the causal atom

The exact periodic compiler would solve the chronology problem if one could
produce a finite phase word of state-matched exact Nash--Bellman roots with
playerwise opponent contraction.  A translated proper active block supplies
the contraction automatically.  It is nevertheless incompatible with the
literal retained-atom provenance.

Indeed, let `A` be the coalition of a positive suffix atom retained through a
finite reset word.  Every `i in A` has positive Quit hazard at the atom's
fixed chronological stage in every represented phase.  A proper rotating
active block omits each fixed player in some phase, where support containment
forces that hazard to be zero.  For singleton `A` this is exactly the checked
`not_forall_liveRoot_eq_supportedCyclicWord_of_proper_resetChain`; the same
support argument applies to every member of a nonsingleton `A`.

Thus a retained atom cannot be converted by simply arranging its live roots
into complementary proper supports.  Full-support phase roots avoid this
particular obstruction, but the rectangle/hard-residual data produce neither
their exact Nash conditions nor the state-matched Bellman recursion required
by `isUniformEquilibriumPayoff_of_cyclicNashBellmanCycle`.

### 4.4 Exact scope of minimum-fiber support rank

There is a genuine regeneration theorem when a same-minimum-fiber reset kills
an old positive-debt coordinate and introduces no new one.  The checked
`exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished` constructs a
fresh positive-minimum tangent family at the reset point with strict support
inclusion.  Hence this arm really lowers a natural-valued rank; it is not
merely a debt-vector observation.

Optimizing the initial base over the compact minimum fiber does not produce
the missing no-new-support premise.  If the base is selected with minimum
positive-support cardinality, any same-fiber reset of an active observer is
forced into one of two cases:

1. its new support has larger cardinality; or
2. it deletes the observer and introduces at least one previously inactive
   coordinate (an equal-cardinality exchange is the sharp case).

A strict subset would contradict the selected minimal cardinality.  Selecting
maximum cardinality reverses only the cardinal inequality and still permits
exchange.  Lexicographic or weighted secondary minimization also gives no
monotonicity, since the aggregate reset identity fixes the sum transferred to
the other coordinates but does not make their individual changes
nonnegative.

This is precisely why the checked `reducedSupportRankAlternative` does not
close the present branch: its strong induction consumes flat/no-entry
full-replacement endpoints and then exits at positive slope, support entry, or
an off-minimum paid row.  The full rectangle under study is already on the
positive-slope side.  A finite cycle of exchanged support labels is not an
exact semantic chronology; separately re-extracted carrier points have no
literal successor relation.  It therefore cannot be counted as Output 4.

## 5. Current state

No Output 1--4 has been proved.  In particular, this note makes none of the
following assertions:

- that `f` is attained by an actual behavioral profile;
- that the suffix atom is a prefix-root atom;
- that a pure-time common response is a time-zero cap action;
- that the reached profitable endpoint is a Nash--Bellman edge;
- that a real debt drop or a one-step support change regenerates the full
  tangent/rectangle problem; or
- that the local `D_*=0` compatibility regressions refute the canonical
  positive-minimum problem.

The sharp common-tail repair does not produce an accepted Output 1--4.  The
attack remains open at the prescribed-payoff surcharge seam: a successful
step must use the **global** terminal witness and positive minimum to rule out
the exact regression mechanism above, control the compensating cap
curvatures on every repaired face, or Nashify the reached row without changing
its literal suffix provenance.  No existing declaration inspected here makes
that implication.
