# Review of the alternating pair-base Nash-mass selector

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Verdict:** **PASS as an internal ordinary-mathematics interface result.**
It does not produce a maintained rank decrease or a new terminal/semantic
consumer, so I do not recommend a standalone export.

## Claim checked

I checked the complete two-free-player Nash correspondence, the debtor-aware
alternative in Proposition 4.1, the pure-cell handoff to the existing paid
large-base dispatch, and both separation models.  I also checked the source
claims against:

- `quittingPersistentBaseNashSet`,
  `isNash_of_mem_quittingPersistentBaseNashSet`, and
  `quittingPersistentBaseRoot_free_purePayoff_le` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- `quittingPersistentLargeBaseExcess` and
  `exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `paidPure_or_paidMixed_of_actual_largeBase_gap_labels` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargePersistentBaseActualAdapter.lean`;
- `PurePaidBaseLeaveSource` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PurePaidBaseLeaveDescent.lean`; and
- `QuittingTerminalExploitabilityWitness.hasSupportTwoPaidChainResidual` and
  `.hasSupportTwoNormalPaidChainResidual` in
  `PaidChainSupportTwoAggregate.lean` and
  `StrictToggleLargeBasePaidChain.lean`.

## Nash correspondence and selector

The affine differences

\[
g_x(v)=(1-v)\alpha _0+v\alpha _1,
\qquad
g_k(u)=(1-u)\beta _0+u\beta _1
\]

give exactly the endpoint complementarity conditions (3.5), the four pure
conditions (3.6), and, when the denominators are nonzero, the displayed mixed
rates (3.7).

Proposition 4.1 is exhaustive and exclusive.  If its positive-mass arm fails,
an interior Nash point is impossible because both `u(1-v)` and `v(1-u)` are
then positive while the full-gap debtor set is nonempty.  A two-by-two game
without an interior Nash point has a pure Nash point: at a boundary mixed
point, the mixing player's difference is zero and the pure player's weak
best-response inequality holds at at least one endpoint.  Moving to that
endpoint preserves both best responses.  Evaluating the two masses at the
four corners gives exactly the debtor classification stated in the note.
The warning that the debtor must be reselected at the same Nash point is
essential and correct.

## Terminal gap and pure-cell handoff

At a persistent pair-base Nash point the two free coordinates are solved.
Because both base players Quit surely at date zero, unrestricted deviations
of a free player reduce to its date-zero binary action, while a base player's
only relevant alternative is to leave the sure-quitting base coalition.
Thus the terminal semantic gap localizes to a base component of
`quittingPersistentLargeBaseExcess`, proving (5.1) pointwise over the entire
induced Nash carrier.

At a pure point in Proposition 4.1, the chosen full-gap base debtor, the other
base owner, and the two free actions supply precisely the fields of
`PurePaidBaseLeaveSource`: the four labels are distinct and exhaustive, the
free cell is pure Nash, and the selected base leave gain is at least
`Gamma`.  Equivalently, the uniform pointwise bound (5.1) feeds the checked
actual large-base dispatcher and then the checked support-two paid-chain
consumer.  The note correctly does **not** claim that this consumer closes
the branch: it returns `HasPurePaidNormalChainFiniteResidual` (or the mixed
deletion residual), not a uniform payoff, Bellman connector, or maintained
rank drop.

## Exact regressions

The Section 6 assignments are coordinate-compatible.  On the pair base
`{0,2}`, both free players have difference `-1` at both opponent endpoints,
so `(u,v)=(0,0)` is the unique induced Nash point.  Player `0` has leave debt
one for every free law, player `2` has debt zero, all four displayed singleton
collision gains are one, and the predecessor mass for player `0` is
`u(1-v)=0`.  The example is correctly scoped as a local interface model; it
does not claim the ambient terminal witness or positive global minimum.

In Section 7,

\[
g_3(v)=1-2v,\qquad g_1(u)=u-\epsilon
\]

has no pure equilibrium and has the unique equilibrium
`(u,v)=(epsilon,1/2)`.  The same player-0 leave debt remains one, while its
predecessor mass is exactly `epsilon/2`.  For rational
`0<epsilon<1`, all specified rewards remain in `[-1,1]`.  Hence no positive
lower bound depending only on `(Gamma,M)` follows from the displayed
collision, induced-Nash, and paid-source interfaces.

## Consumer and frontier assessment

The pure arm genuinely enters an existing finite paid-chain residual, but it
does not decrease a maintained support/debt rank.  The positive-mass arm is
only qualitative, and the rational family proves that it cannot meet any
fixed quantitative threshold based solely on `Gamma,M`.  Thus neither arm is
a new conjecture-facing consumer at the current interface.  The strongest
honest use is the internal dichotomy recorded in Section 8; additional global
hard-residual hypotheses would be needed to turn it into a chamber closure.

