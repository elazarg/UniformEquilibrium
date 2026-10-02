# Review of `CODEX_ROOT__NONSINGLETON_COLLISION_ANTIDIFFUSION_LINEAR_TRANSFER`

Reviewer: Codex Ramsey

## Verdict

**PASS in ordinary mathematics, with two proof-writing/source repairs.**  I
found no sign, current/tail, live-mass, unrestricted-cap, or literal-profile
error in Theorems C--E.  The retained-live-mass calculation is correct and
actually proves a slightly stronger inequality than the boxed statement.  The
pure-endpoint route preserves the selected **stage mass** with no square loss.

Before export or Lean handoff, the author should:

1. state the strongest charge chain and its correspondingly stronger
   live-weighted dichotomy, displayed below; and
2. add the exact cap-stack debt-scaling source
   `quittingTerminalDebtSum_capNashRootStack_eq` from
   `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`.
   Also repair the missing `\ge` in display (20).

These are not mathematical objections.  The result remains a producer-side
contraction, not a FIN4-BT consumer: the endpoint row is not asserted to be a
cap--Nash or punishment-floor Bellman row, and the positive debt recipient is
not identified with the routed coalition.

## Claim checked

At one actual reached row, let

- `L` be live mass;
- `m` be the unconditional stage mass of a fixed coalition `S`, with
  `1 < card S`;
- `tail` be the semantic pair of the all-Continue suffix beginning at the
  next row;
- `D_* > 0` be minimum carrier total debt;
- `E = D(tail)-D_*`;
- `delta_i` be the coordinate root Nash defect against `tail.1`; and
- `R=sum_i delta_i`.

The proposed local conclusion is

`m D_* <= E + L R`, followed by a tail-excess/actual-gain dichotomy, exact
mover-debt loss, aggregate recipient transfer, and no-loss routing of the
selected stage atom under the pure endpoint update.  The deep adapter first
concentrates a positive nonsingleton law atom in one row and then transports
that row through a literal exact cap--Nash stack.

## 1. Exact retained-live-mass inequality

The strongest direct statement supported by the checked declarations is

\[
 \boxed{
 mD_*\le LC\le L(E+R)=LE+LR\le E+LR,
 }
 \tag{R1}
\]

where

\[
 C=\sum_i
   \operatorname{OpponentAbsorptionMass}(x,i)\,d_i(\mathrm{tail}).
\]

The first inequality is obtained as follows.

- `quittingStageCoalitionMass_mul_tailDebtSum_le_liveMass_mul_charge` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectTelescope.lean`
  gives
  `m * D(tail) <= L * C`.  Its use of `1 < card S` is essential: every debt
  coordinate must see some *other* member of `S`.
- The actual shifted tail is in the semantic carrier by
  `quittingTerminalSemanticPair_mem_carrier`, so global minimality gives
  `D_* <= D(tail)`.  Since `m>=0`, this yields `mD_*<=mD(tail)`.
- `minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectCharge.lean`
  gives `C<=E+R` with exactly this orientation.
- `0<=L<=1` and `E>=0` give the final comparison in (R1).

Thus the note's boxed `mD_*<=E+LR` is correct, but it should preserve the
intermediate `mD_*<=L(E+R)`.  The sharp half split is

\[
 LE\ge \frac{mD_*}{2}
 \quad\text{or}\quad
 LR\ge \frac{mD_*}{2}.
 \tag{R2}
\]

The note's displayed alternative with `E` in place of `LE` is a valid weaker
consequence.  Keeping `LE` makes clear that no survival factor has been
silently discarded.

This is a single-stage statement.  It must not be applied directly to only an
aggregate window mass.  Theorem A is what first turns a nonsingleton window
mass into one retained stage mass; without that concentration step, selecting
one defect row would incur a finite-window averaging loss.

## 2. Actual behavioral gain and Fin4 constants

Each coordinate defect is nonnegative by
`quittingRootCoordinateNashDefect_nonneg`.  For `n=card I`, the second arm of
(R2) selects `p` with

\[
 L\delta_p\ge \frac{mD_*}{2n}.
\]

The identity

`quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`
identifies `L delta_p` with the payoff gain of the literal legal behavioral
deviation which uses the better pure endpoint at that row and the prescribed
continuation thereafter.  It is not merely a root-level or stationary gain.

For `I=Fin 4`, this is

\[
 g_p\ge mD_*/8.
\]

If the first branch is strictly false, the proof actually gives a strict
inequality; the note's weak lower bound is safe.  There is an unavoidable
factor `4` here: total defect `R` is not itself the gain of one player.

## 3. Exact mover debt and recipient transfer

Let `source=Sem(sigma)` and let `target=Sem(sigma')` for the actual endpoint
profile.  The opponents' strategies are literally unchanged, so
`quittingContinuationBestResponseValue_update_self` yields

\[
 d_p(\mathrm{target})=d_p(\mathrm{source})-g_p.
 \tag{R3}
\]

The target is in the carrier because it is the semantic pair of an actual
behavior profile.  The checked near-minimum account is
`nearMinimumDebt_opponentTransfer_of_coordinateDecrease` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauPartialResetTransfer.lean`;
equivalently, the exact proof is already exposed in
`causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionMinimumTransfer.lean`.
It gives

\[
 g_p-\varepsilon\le
 \sum_{j\ne p}\bigl(d_j(\mathrm{target})-d_j(\mathrm{source})\bigr).
 \tag{R4}
\]

Here `epsilon` is the **full source excess** above the minimum.  It is not the
shifted-tail excess `E` in (R1), and the two quantities must remain separate.

For `Fin 4`, `card (univ.erase p)=3`.  If `epsilon<=g_p/2`, (R4) implies that
one recipient has debt increase at least `g_p/6`; no coordinatewise
nonnegativity assumption is needed.  Combining `g_p>=mD_*/8` with
`epsilon<=mD_*/16` gives the explicit recipient floor `mD_*/48`.

The atom decoder
`hasQuittingEndpointDebtRecipientAtom_of_pos` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionRecipientAtom.lean`
can be applied after a strictly positive recipient is selected.  Its terminal
label is newly decoded and is not inherited from `S`.

## 4. No-loss pure-endpoint routing

The no-loss statement is exact.  Write `x` for the source live root, `a` for
the selected endpoint, and

`S'=quittingPureEndpointRoutedCoalition S p a`.

The checked ingredients are:

- `quittingRootCoalitionMass_le_pureEndpointRouted` and the exact
  action-factor identity
  `quittingRootCoalitionMass_eq_actionProbability_mul_routed` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectStratification.lean`;
- `quittingProfileLiveRoot_stagePureEndpoint_self` and
  `quittingLiveMass_stagePureEndpoint_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionAtomicOrientation.lean`;
- `quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`.

They compose to

\[
 \operatorname{StageMass}_{\sigma}(t,S)
 \le
 \operatorname{StageMass}_{\sigma'}(t,S').
 \tag{R5}
\]

There is no additional `L`, `m`, or `m^2` loss: the old and new profiles have
the same probability of reaching the displayed row.  The assumption
`1<card S`, together with
`quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card`, ensures that
`S'` is a legal nonempty terminal coalition.

The precise limitation is cardinality, not mass.  If `card S=2`, `p in S`,
and the better endpoint is Continue, then `S'=S.erase p` is a singleton.
Thus (R5) preserves the actual atom and its date, but does not preserve the
collision property.  It also does not identify a Nash--Bellman edge: the
endpoint is selected against the prescribed-payoff tail `U`, not the cap tail
`B`, and no punishment-floor condition is produced.

## 5. Nonsingleton anti-diffusion and the deep constants

Theorem A is correct.  With `k=card S>=2`, the stopping-law product formula
gives `m_S(t)<=prod_{i in S}p_i(t)`.  Holder yields

\[
 \sum_t m_S(t)^{1/k}\le1,
 \]

and hence

\[
 \sup_t m_S(t)\ge
 \left(\sum_t m_S(t)\right)^{k/(k-1)}.
\]

The uniform-clock example establishes sharpness, and summability ensures a
positive supremum is attained at a finite date.  The diffuse-window singleton
corollary is also correct: a window mass `M_n>lower` would create normalized
clock mesh at least `M_n>lower`, contradicting `clock_mesh` at
`epsilon=lower`.

For a limiting nonsingleton law atom of mass `mu`, the current causalization
interface supplies a window mass `>mu/2`.  Theorem A therefore selects a row
with mass `>mu^2/4`.  This row should be described explicitly as a **new
argmax/reselection inside the finite window**, rather than the arbitrary
positive `mark` returned by
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`.
The root word transports every suffix row, so the reselection is legitimate.

For the selected exact cap stack, put
`c_n=quittingCapNashStackContinueProduct (roots n)`.  The exact identity

`quittingTerminalDebtSum_capNashRootStack_eq`

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`
gives `D(prefix_n)=c_n D(suffix_n)`.  Both debts tend to `D_*>0`, hence
`c_n->1`; eventually `c_n>1/2`.  Together with
`quittingStageCoalitionMass_literalRootStack_add_length`, this proves the
shifted stage floor `lambda=mu^2/8`.

Applying Sections 1--4 at that literal suffix row gives exactly the note's
Fin4 constants:

- tail excess at least `mu^2 D_*/16`, or
- actual endpoint gain at least `mu^2 D_*/64`;
- routed stage atom at least `mu^2/8`; and
- once source excess is at most half the gain floor, one recipient debt
  increase at least `mu^2 D_*/384`.

The prefix stack is exact cap--Nash, but the marked collision row remains in
its declared suffix.  None of these calculations upgrades that suffix row to
a cap--Nash or prescribed-payoff punishment-floor Bellman row.

## 6. Source and novelty audit

All declaration paths listed in Section 9 are exact.  The missing explicit
source needed by the proof of Theorem E is
`quittingTerminalDebtSum_capNashRootStack_eq` in
`TerminalCapNashChronology.lean`, noted above.  The stopping-law product
factorization used in Theorem A is not presently a single named checked
declaration; the proposed Lean handoff correctly treats that connection as
new work, using `quittingBehaviorStoppingLaw_some_toReal` and
`quittingHazardStoppingLaw_some_toReal` from
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`.

Narrow searches found no checked theorem already stating either the sharp
nonsingleton clock concentration or the direct routed **stage**-mass
monotonicity.  The live-weighted charge result is a strict derived adapter of
the checked charge declarations, while the currently checked causal wrapper
loses an additional supplied lower factor and obtains `lower^2`.

This is meaningful new internal mathematics and a good formalization target.
It does not yet meet the conjecture-facing export significance gate by
itself: the fixed-resolution transfer/tail-escape alternatives remain
unconsumed and no regeneration, return, or uniform-payoff conclusion is
proved.

