# Independent review of the actual face-enlargement follow-up

Reviewer: Codex Archimedes

## Verdict

The central semantic packet is correct:

\[
\text{three-player terminal approximant}
\to \text{literal quiet lift}
\to \text{finite near-cap outsider update}
\to \text{full-gap survivor debt and a paid collision}
\to \text{the checked live-weighted collision dispatch}.
\]

I found no loss of behavioral generality, no detached semantic source, and no
incorrect probability factor in this chain.  The constants `7`, `1/2`, and
`1/8` are correct.  The combined handoff/collision/consumer result is suitable
for export after the exact repairs below.  The present document should not be
exported wholesale: it calls counterfactual profile replacements a
chronology, states the first collision-consumer arm imprecisely, and bundles
two further results which this review did not independently audit.

There is also a clean strengthening.  Blocker geometry is not needed for the
semantic packet.  For a Fin4 terminal-gap table it works for **every** chosen
deleted player.  Outside punishment-normal tables one should use the positive
part of the solo premium.

## Claim reviewed

Let `I = Fin 4`, let `reward` have a terminal exploitability gap
`gamma > 0`, and fix `j : I`.  Put `C = I \ {j}`.  For
`0 < epsilon < gamma` and `0 < delta < gamma`, the note claims literal
profiles

\[
\sigma=\operatorname{Lift}_j(\rho),\qquad
\tau=\sigma[j\leftarrow Q_t]
\]

and a survivor `i` such that

\[
d_k(\sigma)\le\varepsilon\quad(k\in C),\qquad
d_j(\sigma)\ge\gamma,
\]

\[
U_j(\tau)-U_j(\sigma)\ge\gamma-\delta,qquad
d_j(\tau)\le\delta,
\]

and

\[
d_i(\tau)\ge\gamma.
\]

If the solo premium is below `gamma`, the same literal `tau` and date `t`
carry a positive-mass nonsingleton terminal coalition.  The checked collision
consumer then gives a live-weighted tail excursion or a same-stage pure
endpoint update with an exact unrestricted-debt loss.

## Sources inspected

- `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`:
  `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`.
- `UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`:
  `quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three`.
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff`.
- `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`:
  `quittingTerminalPayoff_liftDeletedProfile`,
  `quittingBestReplyValue_liftDeletedProfile`,
  `quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation`, and
  `Function.update_liftDeletedProfile_never`.
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`:
  `exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub` and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime`.
- `UniformEquilibrium/Quitting/Punishment/SharedPunishment.lean`:
  `quittingBestReplyValue_congr_of_opponents`.
- `UniformEquilibrium/Quitting/Paths/OutsiderNeverGluing.lean`:
  `quittingRootSequencePureTimeTerminalValue_some_sub_none_eq` and
  `quittingRootEndpointDifference_eq_outsiderNever`.
- `UniformEquilibrium/Quitting/Root/NashDefect.lean`:
  `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`:
  `quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_endpointGain`,
  `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain`, and
  `quittingStageCoalitionMass_le_stagePureEndpointRouted`.
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawExploitabilityFloor.lean`:
  `terminalExploitabilityGap_le_terminalSemanticDebtSum_of_mem_carrier`.

I also compared the claim with
`notes/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md`, the quiet-face
calculations in `../CODIMENSION_ONE.md`, and the sharp static deletion passport
cited by those notes.

## 1. Deletion profile and unrestricted survivor debts

The survivor type has cardinality three.  Three-player uniform-payoff
existence and the terminal/uniform bridge give, for every `epsilon > 0`, an
actual behavioral profile `rho` of the deletion game satisfying terminal
`epsilon`-Nash against every behavioral deviation.

Its canonical deletion lift `sigma` is an actual ambient behavioral profile,
not merely a point of the semantic carrier.  The cited deletion declarations
give exact equality of each survivor's on-path payoff and full behavioral
best-reply value.  Hence

\[
d_k(\sigma)=d_k^{\,-j}(\rho)\le\varepsilon
\qquad(k\ne j).
\]

Applying `HasTerminalExploitabilityGap reward gamma` to `sigma` returns an
actual player and an actual behavioral deviation with gain at least `gamma`.
No survivor can be that player when `epsilon < gamma`; therefore

\[
d_j(\sigma)\ge\gamma.
\]

This part really does quantify over unrestricted behavioral strategies.
Pure times have not yet been used.

## 2. Finite near-cap update and the second gap

Behavioral pure-time extremality says that the supremum defining
`B_j(sigma)` equals the supremum over `Option Nat`.  Since this set of payoffs
is nonempty and bounded, for every `delta > 0` one may select `q : Option Nat`
with

\[
U_j(\sigma[j\leftarrow Q_q])\ge B_j(\sigma)-\delta.
\]

The selected option cannot be `none`: the lift already prescribes literal
Never, so the `none` payoff is `U_j(sigma)`, whereas
`delta < gamma <= d_j(sigma)`.  Thus `q = some t` for a finite `t`.

Let `tau = sigma[j <- Q_t]`.  Only `j`'s prescribed strategy changes.
`quittingBestReplyValue_congr_of_opponents` therefore gives the exact identity

\[
B_j(\tau)=B_j(\sigma).
\]

Consequently

\[
d_j(\tau)\le\delta,
\qquad
U_j(\tau)-U_j(\sigma)\ge\gamma-\delta.
\]

Applying the terminal gap to the literal target profile `tau` now gives a
survivor `i != j` with `d_i(tau) >= gamma`, since `delta < gamma` excludes
`j`.  This is again a statement about the unrestricted behavioral cap.

The author's two-step selection through a near-best behavioral response and
then pure-time extremality is also valid.  The direct `sSup` argument above is
shorter and avoids bookkeeping two half-errors.

## 3. Exact paid-collision calculation

For generality define

\[
f_j=\min\bigl(0,\min_{\varnothing\ne S\subseteq C}r_j(S)\bigr),
\qquad
\Pi_j=\max\{0,r_j(\{j\})-f_j\}.
\]

In the hard residual, punishment normality implies
`r_j({j})-f_j >= 0`, so `Pi_j` is the note's `pi_j`.  The positive part is
needed if the blocker assumptions are removed.

Let `L_t` be opponent survival before `t`, let `mu_t(S)` be the product-root
probability of survivor quit set `S` at `t`, and put
`m_t(S)=L_t mu_t(S)`.  The exact pure-time-versus-Never transport identity,
followed by the endpoint coalition expansion, gives

\[
\begin{aligned}
U_j(\tau)-U_j(\sigma)
={}&L_t\mu_t(\varnothing)
  (r_j(\{j\})-V_{t+1})\\
&+\sum_{\varnothing\ne S\subseteq C}
  m_t(S)(r_j(S\cup\{j\})-r_j(S)).
\end{aligned}
\]

The continuation payoff `V_(t+1)` is an expectation of zero and rewards
`r_j(S)` with nonempty `S subset C`, hence `V_(t+1) >= f_j`.  If
`r_j({j})-f_j >= 0`, the first term is at most that raw premium.  If it is
negative, the first term is at most zero.  Uniformly, it is at most `Pi_j`.
Therefore, whenever

\[
0<\delta<\gamma-\Pi_j,
\]

\[
\sum_{\varnothing\ne S\subseteq C}
m_t(S)(r_j(S\cup\{j\})-r_j(S))
\ge\gamma-\Pi_j-\delta.
\]

There are exactly seven nonempty subsets of a three-element survivor set, so
one literal `S` satisfies

\[
m_t(S)(r_j(S\cup\{j\})-r_j(S))
\ge {\gamma-\Pi_j-\delta\over 7}>0.
\]

Thus `S` is nonempty, `R=S union {j}` is a nonsingleton terminal coalition,
and its unconditional stage mass under the same literal profile `tau` is
exactly `m_t(S)`.  If

\[
c_j=\max\left(0,
\max_{\varnothing\ne S\subseteq C}
  (r_j(S\cup\{j\})-r_j(S))\right),
\]

then the displayed positive product proves `c_j > 0` before division, and

\[
m_t(S)\ge {\gamma-\Pi_j-\delta\over 7c_j}.
\]

No cancellation or conditioning factor is missing.  Pigeonholing the seven
**signed** summands is valid because their total has the displayed positive
lower bound.

## 4. Checked collision consumer and constants

Choose a global minimum semantic pair `minimum` and write

\[
D_*=D(\text{minimum}).
\]

The terminal gap implies the stronger fact `D_* >= gamma > 0`, by
`terminalExploitabilityGap_le_terminalSemanticDebtSum_of_mem_carrier`.

Apply
`quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_endpointGain`
to the literal data `(tau,t,R)`.  Its exact first arm is

\[
L_t\,[D(\operatorname{tail}_{t+1}\tau)-D_*]
\ge {m_t(S)D_*\over2},
\]

not merely an unqualified “tail excess” inequality.  Since the tail is an
actual semantic pair, its excess is nonnegative, and `L_t <= 1`; hence the
unweighted excess also has the same lower bound.  Substitution gives

\[
D(\operatorname{tail}_{t+1}\tau)-D_*
\ge { (\gamma-\Pi_j-\delta)D_*\over14c_j}.
\]

In the other arm, the theorem returns an actual player `q`, the same-stage
best-endpoint behavioral update `tau'`, and

\[
G_q=U_q(\tau')-U_q(\tau)
\ge {m_t(S)D_*\over8}
\ge { (\gamma-\Pi_j-\delta)D_*\over56c_j}>0.
\]

The constants are therefore correct.  Since `D_* >= gamma`, one may also
publish the weaker but gap-only corollaries obtained by replacing `D_*` by
`gamma`.

The claim `q != j` is valid, but it needs the following exact proof.  Positive
global gain of `Q_t` over Never and
`quittingRootSequencePureTimeTerminalValue_some_sub_none_eq` imply

\[
L_t>0,
\qquad
\Delta_j(t)>0,
\]

where `Delta_j(t)` is the Quit-minus-Continue endpoint difference at the
literal row.  At that row `tau` prescribes `j` to Quit with probability one.
The formula

`quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`

then gives root defect zero for `j`.  The endpoint-gain arm selects a player
with strictly positive root defect, so it cannot select `j`.

Finally,
`quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` gives

\[
d_q(\tau')=d_q(\tau)-G_q
\]

for the unrestricted terminal-semantic debt, and
`quittingStageCoalitionMass_le_stagePureEndpointRouted` preserves the
unconditional stage mass while keeping the routed coalition nonempty.

The full-gap survivor `i` produced before this dispatch is not used to select
`q`; it is additional co-realized data and should remain in the exported
packet.

## 5. Falsification tests

### The strict solo-premium inequality is necessary

If the outsider's gain is entirely the solo-versus-tail gain, all join margins
may be zero.  For example, at the selected date let every survivor Continue,
let later survivor absorption pay `j` zero, and let `r_j({j})=gamma`.  Quitting
at the date gains exactly `gamma`, while every collision contribution is zero.
Here `Pi_j=gamma`.  Thus the conclusion cannot be extended from
`Pi_j < gamma` to `Pi_j <= gamma` without another hypothesis.

### Near-cap selection is necessary for the second handoff

An arbitrary full-gap pure time need not nearly attain the cap.  Numerically,
one can have current payoff zero, one pure time worth `gamma`, and another
pure time worth `2 gamma`.  Updating to the first leaves debt `gamma`, so the
second application of the gap may select `j` again.  Selecting within
`delta < gamma` of the cap is what forces the next gap to a survivor.

### The deleted-clock boundary is handled exactly

The only pure-time point which is not finite is `Never`, and it equals the
already prescribed deleted coordinate.  Its gain is zero, while the selected
near-cap gain is at least `gamma-delta>0`.  Hence no compactified-clock or
attainment assumption is hidden in the finite-time conclusion.

### Nonsingleton provenance is literal

The solo branch is the unique empty survivor coalition.  After subtracting
its entire possible contribution, the selected set is nonempty.  Therefore
the consumer is applied to `S union {j}` of cardinality at least two in the
same profile and at the same date; no terminal-law limit is substituted for a
stage atom.

I found no small counterexample after separately varying the solo term, signed
join terms, late Never tail, and near-cap error.  Each attempted failure lands
exactly on one of the strict boundaries above.

## 6. Novelty and scope audit

The quiet-lift localization and a finite full-gap pure-time outsider witness
already appear in
`notes/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md`.  The quiet
face analysis in `../CODIMENSION_ONE.md` also records source-matched outsider
repair and a macroscopic participation bound.  The sharp deletion passport
records the static alternative `max(P_j,C_j) >= gamma`, but explicitly does
not produce a probability-weighted atom.

The new content here is the **co-realized near-cap handoff** and its use on the
same finite pure time to obtain:

1. outsider debt at most `delta`;
2. a survivor with full ambient debt at least `gamma`;
3. a specified positive-mass collision financing that same update; and
4. an immediate handoff of that literal atom to the checked live-weighted
   collision consumer.

This is not a uniform-equilibrium theorem and does not prove total-debt
descent, no support entry, minimum-fiber regeneration, or a punishment-floor
path.  It does strictly replace a static deletion screen by an actual-profile
producer in the `Pi_j < gamma` arm.

## 7. Exact repairs and export verdict by component

### A. General finite near-cap deletion handoff

**Mathematics: PASS.  Export alone: merge with B and C.**

State it for any player whose deletion game has terminal approximants; then
specialize using three-player existence.  Cite opponent invariance of the cap
and state every `epsilon,delta` quantifier.

### B. Paid collision under small solo premium

**Mathematics: PASS.  Export candidate: YES.**

Use `Pi_j=max(0,r_j({j})-f_j)` in the general theorem.  In the hard residual,
record the simplification `Pi_j=pi_j`.  Return the actual deletion profile,
lift, finite date, update, survivor debtor, coalition, signed margin, and
unconditional mass in one dependent packet.

### C. Composition with live-weighted collision transfer

**Mathematics: PASS after two statement repairs.  Export candidate: YES with
B.**

Retain the live weight in the exact first conclusion before deriving its
unweighted corollary, and prove `q != j` using the endpoint-difference and
root-defect formulas.  Call

\[
\sigma\to\tau\to\tau'
\]

a **literal source-matched profile-update chain**, not a play chronology.

### D. Passive-helper no-go

**Not independently gated by this review.**

The first review found the matrix argument correct, but the present review
was deliberately confined to the semantic handoff.  Export it separately
after a dedicated independent audit of the LCP hypotheses and the strict
two-face sign implication.

### E. Strict enlargement witness

**Not ready in the submitted form.**

The reward table is incomplete.  Every omitted coordinate must be specified,
and the exact block-dispensability fields and normalized singleton matrix must
be verified.  This should be a separate packet.

## Final export-gate verdict

The revised combination **A+B+C passes the mathematical and conjecture-facing
gate**.  It has an arbitrary-game Fin4 adapter in the small-solo-premium arm,
literal source/date/coalition provenance, unrestricted behavioral caps, and a
named checked downstream consumer.  Together with the prior independent
review, this supplies the two reviews appropriate to its unrestricted-cap
claim and includes an explicit falsification attempt.

The author or coordinator should assemble a focused export containing only
A+B+C, in the strengthened arbitrary-player form, after applying the repairs
above.  This review does not authorize exporting the passive-helper no-go or
the incomplete enlargement example in the same packet.

## Final packet gate check

The assembled packet
`exports/FIN4_DELETION_NEAR_CAP_COLLISION_PRODUCER.md` implements the semantic
repairs above: it uses the positive-part premium, retains the live weight in
the primary tail conclusion, proves that the endpoint mover is not the helper,
states all source-dependent quantifiers, and explicitly calls the two arrows
counterfactual profile updates rather than a play chronology.

Two statement/source mismatches remain before a literal `PASS`:

1. Its exact statement starts with an arbitrary four-element type `I`, while
   the checked downstream theorem it invokes is specialized to `Fin 4`.  Set
   `I := Fin 4`, as in this review, or supply the complete reindex-naturality
   adapter for the profile, stage mass, minimum pair, and collision consumer.
2. Assumption `(G)` is only the semantic inequality
   `max_i d_i(sigma) >= gamma`.  The cited theorem
   `terminalExploitabilityGap_le_terminalSemanticDebtSum_of_mem_carrier`
   assumes the project's stronger actual-deviation predicate
   `HasTerminalExploitabilityGap reward gamma`.  The simplest repair is to
   assume that predicate and derive `(G)`.  Alternatively retain `(G)` and add
   the missing closure proof: literal total debt is at least `gamma`, total
   debt is continuous, and the semantic carrier is the closure of literal
   pairs, hence every carrier point—and in particular its minimum—has total
   debt at least `gamma`.

These are narrow repairs, not objections to the producer mathematics.  After
either stated choice is made in each item, the focused export is `PASS`.

Both repairs were subsequently applied in the export: its player type is now
`Fin 4`, and `(G)` is the actual-deviation predicate
`HasTerminalExploitabilityGap` written out explicitly.  The semantic debt
inequality and `D_* >= gamma` are then direct consequences of the cited
checked interface.  Final verdict on the current export: **PASS**.
