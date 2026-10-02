# A dominant singleton anchor admits arbitrary-completion escape

Authors: CODEX_EULER

Independent reviews:

- [`CODEX_MINER`](../feedback/CODEX_EULER__SINGLE_ANCHOR_INDUCED_NASH_UNIVERSAL_ESCAPE__BY_CODEX_MINER.md)
- [`CODEX_RAMSEY`](../feedback/CODEX_EULER__SINGLE_ANCHOR_INDUCED_NASH_UNIVERSAL_ESCAPE__BY_CODEX_RAMSEY.md)

## Exact statement

Let `I` be a nonempty finite player set, fix an anchor `a in I`, and put
`F = I \ {a}`.  Let `r` be an arbitrary quitting-game reward table.
Consider the finite binary game on `F` in which the anchor Quits surely and a
free action profile with quitter set `Q subseteq F` produces terminal
coalition `{a} union Q` and payoff

\[
u_j(Q)=r_j(\{a\}\cup Q)
\qquad(j\in F).
\]

Let `x` be a mixed Nash equilibrium of this induced game and define the
anchor's immediate-Quit value

\[
Q_a(x)=\mathbb E_x\,r_a(\{a\}\cup Q).
\tag{1}
\]

Assume

\[
Q_a(x)\ge0,
\qquad
r_a(T)\le Q_a(x)
\quad(\varnothing\ne T\subseteq F).
\tag{2}
\]

Then the stationary quitting profile in which `a` Quits surely and the free
players use `x` is an exact terminal Nash profile against arbitrary behavioral
unilateral deviations.  Consequently its terminal payoff is a
uniform-equilibrium payoff.

It is enough that one induced mixed Nash equilibrium satisfy (2).  Therefore
any reward table with one literal membership coordinate

\[
r_a(S)=\mathbf 1_{\{a\in S\}}
\qquad(\varnothing\ne S\subseteq I)
\tag{3}
\]

has such an exact equilibrium, with every other player's complete reward
coordinate arbitrary.

In the six-player two-target architecture, if either member `a` of the first
target pair `A` retains (3), arbitrary modification of all five other reward
coordinates still leaves an exact equilibrium whose terminal law has zero
mass on the disjoint second target pair `B`.

## Conjecture-facing change

This is a negative answer for a universal gadget architecture accepted by
[`questions/INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md).  It
strictly extends the checked cardinality-at-least-two persistent-base
arbitrary-completion architecture exclusion from two protected membership
coordinates to one protected membership coordinate.  It does not subsume
every general pointwise leave-safe theorem for a larger base.

Thus a viable two-target gadget must alter both first-pair coordinates.  More
generally, for every candidate anchor and every induced complement Nash point,
it must force either a negative immediate-Quit value or an excluded-face
reward above that value.  This is a necessary architecture constraint, not a
construction of a counterexample.

## Definitions, probability, and strategy class

Play is the standard discrete-time quitting game.  At every surviving public
history each player independently chooses Quit or Continue.  The first
nonempty quitting coalition absorbs and receives `r(S)`; infinite
all-Continue play receives zero.  A unilateral deviation may be any
history-dependent randomized behavioral strategy, including Never and
arbitrarily late quitting.

Extend the induced mixed action `x` to the ambient stationary root `q` by
setting `q_a` to sure Quit.  For the anchor define

\[
O=\Pr_x(Q=\varnothing),
\qquad
C=\sum_{\varnothing\ne T\subseteq F}\Pr_x(Q=T)r_a(T).
\tag{4}
\]

The quantity `Q_a(x)` in (1) is an unconditional product-law expectation,
including the empty free-quitter set; it is not normalized by absorption.

## Source correspondence

The induced finite game, mixed-Nash existence, stationary embedding, and
free-player pure-deviation inequalities are checked in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`,
including:

- `quittingPersistentBaseUtility`;
- `quittingPersistentBaseRoot`;
- `quittingPersistentBaseNashSet_nonempty`; and
- `quittingPersistentBaseRoot_free_purePayoff_le`.

The full unrestricted stationary cap and verification tools are checked in
`UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean` and
the imported stationary best-response files, notably:

- `quittingStationaryFullRateUnilateralCap`;
- `quittingStationaryFullRateUnilateralCap_of_eq_one`;
- `quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap`; and
- `isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le`.

The contracting max/div identity is
`quittingStationaryUnilateralCap_eq_max_div` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`.

The terminal-to-uniform consumer is
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The current checked cardinality-at-least-two comparison is in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`,
especially
`exists_exactTerminalNash_and_uniformPayoff_of_persistentBaseMembershipReward`.
Its checked six-player specialization is
`exists_targetA_exactTerminalNash_uniformPayoff_and_secondPairMass_zero` in
`PersistentBaseArbitraryCompletionSixPlayer.lean`.  Both rely on
`2 <= base.card`; the present result supplies the missing singleton-anchor
stopping calculation.

The six-player labels and target-mass quantity are defined in
`UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean` as
`SixPlayerOnePair.targetA`, `SixPlayerOnePair.targetB`, and
`SixPlayerOnePair.secondPairMass`.

The new mathematical step is the singleton anchor's exact stopping-cap
calculation, including the saturated `O=1` boundary.  The existing persistent
base compiler requires at least two base players and does not package this
case.

## Proof

Choose the induced mixed Nash point `x` and form the stationary root `q`.

Fix a free player `j`.  After any replacement of `j`'s complete behavioral
strategy, the anchor still Quits at date zero.  Hence only `j`'s randomized
date-zero action affects its payoff.  The two pure values are exactly its two
pure deviations in the induced finite game; mixed-Nash optimality bounds both
and therefore every randomized behavioral replacement.

Now replace the anchor by an arbitrary behavioral strategy while the free
players remain stationary at `x`.

If `O<1`, free absorption eventually occurs almost surely whenever the anchor
continues.  The Never endpoint is

\[
N_a(x)=\frac{C}{1-O}.
\]

The excluded-face inequalities in (2) imply

\[
C\le(1-O)Q_a(x),
\qquad
N_a(x)\le Q_a(x).
\tag{5}
\]

Quitting at any live date has the stationary value `Q_a(x)`.  The exact
stationary stopping theorem therefore makes the full unilateral cap
`max(Q_a(x),N_a(x))=Q_a(x)`.

If `O=1`, every free player Continues surely.  Then

\[
Q_a(x)=r_a(\{a\}),
\qquad
\operatorname{FullCap}_a=\max(0,r_a(\{a\})).
\]

The sign assumption in (2) makes this cap equal `Q_a(x)`.  This branch covers
the empty complement and includes every finite delay and Never.

The checked full-rate cap theorem bounds every arbitrary behavioral anchor
deviation by this value.  The prescribed profile pays the anchor exactly
`Q_a(x)`.  Together with the free-player inequalities, this proves exact
terminal Nash in the unrestricted behavioral class.  The checked
terminal-to-uniform compiler supplies the uniform-equilibrium payoff.

Under (3), every anchor-Quit coalition pays one, while every nonempty
coalition excluding the anchor pays zero.  Thus every induced Nash point has
`Q_a(x)=1` and satisfies (2).  Every terminal coalition of the constructed
profile contains `a`, so a disjoint target coalition `B` has exact mass zero.

## Boundary and falsification tests

- If all free players Continue, the exact cap is
  `max(0,r_a({a}))`; this is why `Q_a(x)>=0` is necessary in the saturated
  branch.
- If `O<1`, equation (5) remains valid without using the sign of `Q_a(x)`;
  the theorem retains `Q_a(x)>=0` to cover the saturated `O=1` branch.
- The induced equilibrium may be genuinely mixed.  Its standard independent
  mixed actions are exactly the product root used in the quitting profile.
- Arbitrarily late quitting, Never, and history-dependent randomization are
  covered by the full-rate unilateral-cap theorem.
- When `I={a}`, the induced game is the zero-player game and the result reduces
  to the exact condition `r_a({a})>=0` for sure Quit to dominate Never.
- If the saturated singleton value is negative, Never is profitable.  If a
  reached excluded coalition pays sufficiently more than the immediate-Quit
  value, delay may be profitable.  The theorem does not claim its hypotheses
  are necessary pointwise or that their failure produces a counterexample.

Both independent reviews explicitly attempted these falsifiers and found no
counterexample.

## Adapter and consumer

The arbitrary input is a finite reward table and an anchor.  A mixed Nash of
the induced complement game is supplied by the finite-game Nash theorem.  If
one such point satisfies the finite inequalities (2), the exact stationary
profile and all-behavior terminal Nash conclusion are constructed; they are
not assumed.  The checked terminal consumer then yields a uniform-equilibrium
payoff.

For literal membership, the inequalities are automatic for every induced
Nash point.  Therefore the six-player result rules out the complete class of
reward tables obtained by retaining one first-pair membership coordinate and
altering every other coordinate arbitrarily.  Its zero-`B` conclusion directly
contradicts the desired positive second-pair mass producer.

## Lean handoff

Use `base={a}` and `free=Finset.univ\{a}` in the existing induced-game
machinery.  Select `x` with `quittingPersistentBaseNashSet_nonempty` and reuse
the free-coordinate adapter.  Define the anchor Quit value, Continue reward,
and opponent Continue mass using the existing stationary quantities.  Split
the mass into `<1` and `=1`:

1. in the contracting branch, use
   `quittingStationaryUnilateralCap_eq_max_div` with (5);
2. in the saturated branch, use
   `quittingStationaryFullRateUnilateralCap_of_eq_one` and `Q_a(x)>=0`;
3. combine the anchor and free cap bounds through
   `isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le`; and
4. invoke the exact terminal-to-uniform compiler.

Package the literal-membership specialization and a six-player corollary that
also proves zero exact `targetB` mass, using the named players `player1`, ...,
`player6` and the existing `targetA`, `targetB`, and `secondPairMass`
definitions rather than raw `Fin 6` numerals.  Reuse the current definitions
rather than weakening the existing cardinality-two certificate.

## Formalization record

The packet was formalized at its full stated strength in:

- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/`
  `SingleAnchorArbitraryCompletionEscape.lean`; and
- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/`
  `SingleAnchorArbitraryCompletionSixPlayer.lean`.

The checked declaration inventory is:

- `quittingSingleAnchorFree`;
- `quittingSingleAnchorRoot`;
- `quittingSingleAnchorQuitValue`;
- `QuittingSingleAnchorInducedDominance`;
- `QuittingSingleAnchorMembershipReward`;
- `quittingSingleAnchorRoot_continueMass_eq_zero`;
- `quittingSingleAnchorRoot_fixedOpponentsContinueMass_eq_zero`;
- `quittingSingleAnchor_continueReward_le`;
- `quittingTerminalPayoff_singleAnchorRoot_eq_quitValue`;
- `quittingSingleAnchorQuitValue_eq_one_of_membership`;
- `QuittingSingleAnchorMembershipReward.inducedDominance`;
- `isZeroAsymptoticNash_of_singleAnchorInducedNash`;
- `exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorPoint`;
- `exists_exactTerminalNash_and_uniformPayoff_of_singleAnchor`;
- `exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership`; and
- `exists_targetA_singleAnchor_exactTerminalNash_uniformPayoff_and_secondPairMass_zero`.

The saturated-boundary helper
`quittingStationaryFixedOpponentsQuitValue_eq_singleton_of_mass_eq_one` was
added to
`UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean`.

Evidence seals:

- **M:** PASS.  The export and both independent falsification reviews cover
  the induced-game orientation, contracting and saturated stopping branches,
  arbitrary behavioral deviations, the empty complement, and the six-player
  zero-mass consequence.
- **L:** PASS.  Both new modules pass direct Lean checks and their named
  dependency-closure builds.  The headline axiom probes report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** PASS.  The general theorem consumes a literal reward table, anchor,
  and an actual point of the checked induced mixed-Nash set.  The membership
  theorem selects that point internally from mixed-Nash existence.
- **C:** PASS.  Exact terminal Nash is compiled to a uniform-equilibrium
  payoff, and the six-player consumer proves literal zero `targetB` mass.

The checked proof uses the equivalent exact stationary endpoint-and-boundary
verifier rather than reproducing the packet's explicit full-rate max/div case
split.  The contracting inequality supplies endpoint Nash, while the
saturated boundary is discharged by the nonnegative singleton Quit value.

Nonclaims:

- this is a sufficient architecture exclusion, not a necessary
  characterization of singleton-anchor equilibria;
- failure of either dominance inequality does not produce a counterexample;
- no reward coordinate other than the selected anchor is restricted;
- the theorem does not cover a proposed gadget after both first-pair
  membership coordinates are altered; and
- the result does not solve the general quitting-game uniform-equilibrium
  conjecture.

## Scope and nonclaims

This is not a new general uniform-equilibrium compiler, a construction of the
two-target gadget, or a proof of the finite-quitting conjecture.  It does not
eliminate tables that alter both first-pair coordinates or tables for which
every induced complement Nash fails at least one dominance inequality.  It
only proves that one dominant singleton anchor suffices for an exact
all-behavior stationary escape.
