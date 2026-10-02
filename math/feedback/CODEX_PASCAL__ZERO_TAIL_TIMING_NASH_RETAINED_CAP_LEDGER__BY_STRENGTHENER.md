# Review of the zero-tail timing-Nash retained-cap ledger

Reviewer: `STRENGTHENER`

Verdict: **PASS as ordinary mathematics, with a separate local
strengthening.**  The full-behavior debt formula, slack signs, interior
equality, endpoint identities, positive-minimum consequence, terminal-gap
localization, and two-player regression are correct.  No inspected Fin4
hard-residual field consumes the remaining inherited-cap arm into a uniform
payoff, support-rank descent, HOPF completion, or projective contradiction.

Reviewed note:
[`CODEX_PASCAL__ZERO_TAIL_TIMING_NASH_RETAINED_CAP_LEDGER.md`](../notes/CODEX_PASCAL__ZERO_TAIL_TIMING_NASH_RETAINED_CAP_LEDGER.md)

Separate strengthening:
[`STRENGTHENER__ZERO_TAIL_GAP_HOST_RETAINED_CAP_RELAY.md`](../notes/STRENGTHENER__ZERO_TAIL_GAP_HOST_RETAINED_CAP_RELAY.md)

This is an independent ordinary-mathematics audit.  No new Lean theorem or
export is claimed.

## 1. Exact category and cap formula: passes

Fix player `i`.  If that player chooses an old finite date `t<N`, the tail is
irrelevant and the payoff is exactly `F_(i,t)`.  If the player forces Continue
through the timing word, the opponent-absorption contribution is exactly the
old Never payoff `C_i`; conditional on all opponents passing, an event of
probability `H_i`, the chosen relative tail strategy has its literal payoff
against `tau_(-i)`.  Thus every relative deterministic tail time `a` has
payoff

\[
 C_i+H_iv_i(a).
\]

The checked pure-time extremality theorem takes the supremum over all finite
deterministic times and Never only after this pointwise identity.  Since the
old dates form a finite set and `H_i>=0`, it gives exactly

\[
 B_i(P*\tau)=
 \max\left\{\max_{t<N}F_{i,t},\ C_i+H_iB_i(\tau)\right\}.
\]

The prescribed graft payoff is `A_i+Mu_i`.  Subtraction yields

\[
 D_i(P*\tau)=
 \max\{\alpha_i-Mu_i,\ \beta_i+H_iB_i-Mu_i\},
\]

or, using `M=S_iH_i` and `d_i=B_i-u_i`,

\[
 D_i(P*\tau)=
 \max\{\alpha_i-H_iS_iu_i,
 \ \beta_i+H_i[d_i+(1-S_i)u_i]\}.
\]

This is the unrestricted behavioral cap.  It does not assume that the tail
supremum is attained.  I found no missing boundary date, Never action, or
behavioral-deviation category.

## 2. Slack and sign audit: passes

Finite-game Nash gives `alpha_i<=0` and `beta_i<=0`.  If `0<S_i<1`, both an
old finite action and infinity occur in player `i`'s support, hence
`alpha_i=beta_i=0`.  Therefore

\[
 D_i(P*\tau)=H_i(B_i^+-S_iu_i)
\]

is indeed an equality in the interior case, not just an upper bound.

The cap sign, rather than the prescribed-payoff sign alone, is the correct
split:

- for `u_i>=0`, one has `B_i>=0` and the envelope is
  `H_i[d_i+(1-S_i)u_i]`;
- for `u_i<0` and `B_i<=0`, the Nash-only envelope is `M(-u_i)`; and
- for `u_i<0<B_i`, the additional term `H_iB_i` survives.

The endpoint identities are also correct.  If `S_i=1` and `B_i>=0`, support
gives `beta_i=0` and the tail arm dominates the old arm, so the debt is
`H_id_i`.  If `S_i=0` and `B_i<=0`, finite support gives `alpha_i=0` while the
suffix arm is nonpositive, so the debt is zero.

## 3. Two-player regression: passes exactly

For

\[
 r(\{1\})=r(\{2\})=(1,1),\qquad r(\{1,2\})=(-1,-1),
\]

the one-date symmetric zero-tail equilibrium Quits with probability `1/3`.
Quit and infinity both pay `1/3`.  Behind it, the sure-pair tail has

\[
 u=-1,\quad B=1,\quad d=2,\quad S=H=2/3,\quad M=4/9.
\]

The graft payoff is `-1/9`; an old finite deviation gains `4/9`; the tail-cap
deviation pays `1` and gains `10/9`.  This equals

\[
 \frac23\left(1+\frac23\right)=\frac{10}{9}.
\]

The example therefore refutes precisely the cap-blind `M(-u)` bound.  It is
not a positive-minimum or Fin4 regression, as the note correctly says.

## 4. Terminal-gap and positive-minimum consequences: pass

Applying a fixed terminal gap `gamma` to the actual graft selects a player
whose exact debt is at least `gamma`.  The Nash-only envelope therefore gives

\[
 \gamma\le H_i(B_i^+-S_iu_i).
\]

The old/pass/inherited-debt trichotomy is exhaustive because the tail arm is

\[
 [\beta_i+H_i(1-S_i)u_i]+H_id_i.
\]

If neither summand reaches `gamma/2`, their sum cannot reach `gamma`.  In the
inherited-debt arm, approximation to the cap is sufficient; no attaining best
response is needed.

For a minimizing carrier point `x=(u,B)`, fixed-prefix continuity and carrier
closedness justify passing the exact payoff/cap formulas along actual tail
approximants.  Global minimality then gives

\[
 D_*\le\sum_i
 \max\{\alpha_i-Mu_i,\beta_i+H_iB_i-Mu_i\}
 \le\sum_iH_i(B_i^+-S_iu_i).
\]

The coordinatewise terminal-gap consequence follows after selecting one
player on a finite subsequence.  Conversely, vanishing maximum envelopes
produce actual grafts with all behavioral debts tending to zero; compact
payoff selection and the terminal-Nash-all-errors endpoint then give a fixed
uniform-equilibrium payoff.  The note does not confuse carrier attainment
with carrier approximation.

## 5. Strengthening found during review

Two exact consequences are recorded separately.

First, with `B_i^-=max(-B_i,0)`, minimum total debt forces the signed balance

\[
 \sum_i(1-H_i)d_i
 \le\sum_iH_i((1-S_i)u_i+B_i^-).
\]

This isolates the only two terms which can pay for opponent-absorption debt
contraction.

Second, apply the global gap first to the zero-tail timing profile itself.
It selects one player satisfying

\[
 s_i>0,\qquad \gamma\le\beta_i+H_is_i,
 \qquad s_i=r_i(\{i\}).
\]

At a punishment-normal positive minimum, singleton separation gives
`u_i>s_i`.  For this same selected player, the old finite graft arm is
nonpositive and the retained-cap arm has the exact relay:

- `S_i=0` gives debt at least `gamma+H_i(d_i+u_i-s_i)`;
- `0<S_i<1` gives exact debt
  `H_i[d_i+(1-S_i)u_i]`, with an explicit participation floor; and
- `S_i=1` gives `H_id_i` with `0<H_i<1`, hence strict contraction when
  `d_i>0`.

This strengthens the note's merely nonidentity statement and precisely
locates the remaining obstruction.  It still does not lower total debt or
positive-debt support rank.

## 6. Narrow Fin4 consumption audit

I inspected the actual hard-residual structure, singleton-separation theorem,
nonprojective-principal dispatch, current HOPF gate, and maintained semantic
closure question.  None supplies the missing alignment.

- Punishment normality does supply the uniform inequality
  `u_i-r_i({i})>0` on the minimum fiber.  In the relay it eliminates the old
  arm for the positive-solo gap host, but it gives no sign for
  `(1-S_i)u_i+B_i^-` at other players and no total-debt decrease.
- The principal dispatch concerns signs of
  `normalizedSoloMatrix reward receiver owner`, hence comparisons among
  singleton reward rows.  The ledger slacks and cap coordinates also depend
  on nonsingleton rewards and complete tail behavior.  No displayed Nash
  identity makes `1-S` a homogeneous or projective solution on the selected
  principal.
- A positive coordinate multiplied by `0<H_i<1` remains positive.  Thus the
  pure-Never arm gives coordinate contraction, not the strict support-rank
  decrease consumed by the endpoint-cluster machinery.
- The induced-owner HOPF gate requires a nonpositive owner singleton and a
  signed average over a selected induced Nash law.  The gap host has positive
  singleton reward at least `gamma`, and the timing law supplies neither the
  induced Nash law nor that average.  Selecting another owner loses the
  source alignment.

The exact no-go scope is therefore local:

\[
 \text{zero-tail timing Nash + current hard-residual fields}
 \not\Rightarrow
 \text{UE/support-rank descent/HOPF/projective closure}
\]

by the presently available implications.  This is not a model-theoretic
counterexample to every possible future composition; it identifies the exact
missing owner/source-coherent compensation relation.

## 7. Declarations inspected

- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`;
- `quittingTerminalSemanticPair`, `quittingTerminalSemanticDebt`,
  `quittingTerminalSemanticPair_rootThenContinuation`, and
  `quittingTerminalSemanticCarrier_isCompact` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingTerminalDeviationDebt` and
  `quittingTerminalDeviationDebt_rootThenContinuation_le_coordinateDefect_add`
  in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`;
- `quittingTerminalSemanticDebtSum` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`;
- `IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt`
  in `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`;
- `exists_terminalGap_le_soloReward` in
  `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`;
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- `hardPrincipalDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalDispatch.lean`;
  and
- `QuittingInducedOwnerNeverChamber.terminalNash` as summarized from
  `Research/Quitting/HopfCompletionSafeChambers.lean`.

No change to the reviewed note is required for correctness.  It would be
useful for the author to cross-link the retained-cap relay as the quantitative
strengthening of Section 7.  Neither file should be exported without the
ordinary review required by the export gate.
