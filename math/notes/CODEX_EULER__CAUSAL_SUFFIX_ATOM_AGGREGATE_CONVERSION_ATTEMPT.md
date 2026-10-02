# Causal suffix atoms: aggregate conversion attempt

**Owner:** CODEX_EULER  
**Status:** IN PROGRESS / NO ACCEPTED CONSUMER.  The aggregate lemma below is
proved in ordinary mathematics from checked declarations, but neither of its
outputs is yet one of the requested conjecture-facing endpoints.  Nothing in
this note is proposed for export.  
**Target:** consume
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` rather
than merely observing that its atom lies in the suffix.

## 1. Exact input and notation

Let `p=(U,B,mu)` be a point of the joint terminal-semantic/law carrier with

\[
 D(p)=D_*>0,
 \qquad \mu(S)=m>0
\]

for one finite nonempty coalition `S`.  The checked causalization theorem
returns actual profiles `sigma_n`, windows `N_n`, marks `t_n`, and exact
cap--Nash words `w_n` of length `n+1` such that

\[
 \operatorname{SemLaw}(\sigma_n)\to p,
 \qquad
 \sum_{t<N_n} a^S_{n,t}>m/2,                                    \tag{1.1}
\]

and the atom at `t_n` remains positive after prepending `w_n`.  Here
`a^S_{n,t}` is the unconditional stage mass of coalition `S` in `sigma_n`.
The total debt at the front of the literal stack tends to `D_*`.

## 2. What the exact cap prefix itself can and cannot pay

Write `P_n` for the joint Continue product of `w_n`.  Exact cap-stack debt
scaling gives

\[
 D(\operatorname{Prefix}(w_n,\sigma_n))=P_nD(\sigma_n).
\]

Both sides tend to `D_*>0`, while `D(\sigma_n)\to D_*`.  Hence

\[
 P_n\to1,
 \qquad
 \sum_{q\in w_n}\operatorname{absorption}(q)\to0.                \tag{2.1}
\]

The second conclusion is the checked logarithmic cap-stack estimate.  Thus
the exact prefix cannot itself supply a fixed positive cumulative-charge
floor.  Its function is survival transport: the suffix atom survives with
asymptotically no loss.  It neither repeats that atom nor turns the suffix
live row into a cap root.

This is not the conclusion of the note; the remaining question is whether
the entire causal window has an aggregate consumer.

## 3. Aggregate collision-window lemma

Assume in this section that `|S|>=2`.  For one actual profile `sigma`, put

\[
 D_t=D(\operatorname{Spine}(\sigma,t)),\quad
 e_t=D_t-D_*,\quad
 L_t=\Pr_\sigma(\text{live at }t),
\]

and let `delta_t` be the total one-row Nash defect of the actual live root at
time `t`, priced at the prescribed payoff of the shifted tail `t+1`.

### Lemma 3.1 (window mass pays tail escape or defect occupation)

For every cutoff `N`,

\[
 D_*\sum_{t<N}a^S_t
 \le
 L_Ne_N-e_0
 +\sum_{t<N}(L_t-L_{t+1})e_{t+1}
 +\sum_{t<N}L_t\delta_t.                                        \tag{3.1}
\]

Consequently, if `e_t<=E` for all `t<=N`, `e_0>=0`, and
`sum_{t<N} a^S_t >= m/2`, then

\[
 mD_*/2\le E+\sum_{t<N}L_t\delta_t.                              \tag{3.2}
\]

In particular,

\[
 \max_{t\le N} e_t\ge mD_*/4
 \quad\text{or}\quad
 \sum_{t<N}L_t\delta_t\ge mD_*/4.                               \tag{3.3}
\]

#### Proof

Equation (3.1) is exactly
`sum_stageCollisionMass_mul_tailDebtSum_le_stoppedDefectExcess`, using
`D_{t+1}>=D_*` and the collision property of `S`.  For (3.2), the coefficients
of the nonnegative excess terms have total weight

\[
 L_N+\sum_{t<N}(L_t-L_{t+1})=L_0=1.
\]

The favorable term `-e_0` may be discarded.  Equation (3.3) follows by
splitting (3.2).

Applied to (1.1), this is stronger than selecting the single positive mark,
whose mass may vanish as `N_n` grows.  After a subsequence it gives one of:

1. an actual shifted suffix whose debt is at least
   `D_*+mD_*/4`; or
2. a fixed positive actual-live occupation budget of local Nash defects.

The statement uses the entire fixed coalition mass `m/2`, so it remains
quantitative in the temporally diffuse case.

## 4. Why neither branch presently reaches the requested endpoint

### 4.1 Off-minimum shifted tail

The shifted tail is an actual profile and therefore can be fed into the
checked full-gap paid-cap adapter.  But the adapter's exact trichotomy still
allows its literal inert arm.  Positive excess debt is only an upper budget
for possible cap charge/descent; it is not a lower bound on either.  If the
port is displaced, its lower-debt limit is not returned with an attained
profile or a regenerated paid row.  Thus this branch is not a well-founded
source descent.

### 4.2 Defect occupation

Each summand `L_t delta_{t,i}` is a legal same-profile unilateral gain:
`quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
realizes it by changing player `i` only at the reached row and then resuming
the original live word.  Nevertheless the sum over an unbounded window is
not the gain of one such deviation.  Quit-optimal rows can be mutually
exclusive stopping opportunities, and replacing one row changes the reach
weights of later rows.

Even after pigeonholing one player, a full endpoint repair only decreases
that player's debt: its unrestricted cap is opponent-owned and stays fixed,
while its prescribed payoff rises by the realized gain.  The debts of the
other players can increase.  Global minimality says exactly that their total
increase compensates the repaired coordinate; it does not orient total debt
downward or strictly reduce debt-support cardinality.  This is the already
known tangent-transfer mechanism, not a new finite rank.

## 5. Tests of the three requested outputs

### 5.1 Prescribed-payoff exact charged edge / cumulative return

Failed.  The rows of `w_n` are exact Nash against continuation caps, and their
aggregate charge tends to zero by (2.1).  The rows carrying `a^S_{n,t}` are
literal suffix rows and can have the positive defects in (3.3); they are not
exact roots against their prescribed tails.  No checked theorem moves their
mass onto a cap root or removes the cap-to-prescribed surcharge.

### 5.2 Regenerated minimum source with finite rank drop

Failed.  Branch 1 of (3.3) regenerates an actual source but moves *above* the
minimum fiber.  Branch 2 gives debt transfer under unilateral repair, with no
strict orientation of total debt, support size, or an existing natural-valued
rank.  Re-extracting a tangent family loses the fixed causal row.

### 5.3 Realizable positive-gap `Fin 4` table

Not obtained.  Producing a genuine table with global `D_*>0` is, by
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`,
already a counterexample to the finite-quitting conjecture.  No local
`D_*=0` regression is substituted for that requirement here.

## 6. Exact declarations inspected

- `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` and
  `quittingStageCoalitionMass_literalRootStack_add_length` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `capNashStack_absorptionSum_le_log_debtRatio` and
  `exists_deep_nearMinimum_capNashChronology` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
- `quittingTerminalSemanticPair_spine_eq_prefix` and
  `positive_stageCoalitionMass_has_semanticPrefixIncidence` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`;
- `sum_stageCollisionMass_mul_tailDebtSum_le_stoppedDefectExcess` and
  `sum_liveMass_mul_spineOpponentAbsorptionDebtCharge_le_epsilon_add_defect`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectTelescope.lean`;
- `quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`;
- `QuittingPaidCapLiftedSource.exactTrichotomy` and the minimum-fiber
  contraction estimates listed in `questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`.

## 7. Exact remaining test

The only potentially converting step exposed by this attempt is a theorem
that turns the fixed occupation budget in (3.3) into either:

1. one behavioral repair whose *total* semantic debt falls; or
2. a finite sequence of repairs carrying a source-native natural rank that
   cannot cycle.

The general one-row identity does neither, and the full `Fin 4` hard residual
currently supplies no sign controlling the other players' cap changes under
that repair.  Until such a sign is produced, the causal finite atom is an
aggregate actual-profile charge, but not an exact-edge or descent producer.
