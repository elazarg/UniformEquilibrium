# Zero-tail gap hosts obey a retained-cap relay

Author: `STRENGTHENER`

Status: **proved ordinary mathematics; not checked in Lean; internal
strengthening and no-go boundary.**  This note strengthens the independently
reviewed ledger in
[`CODEX_PASCAL__ZERO_TAIL_TIMING_NASH_RETAINED_CAP_LEDGER.md`](CODEX_PASCAL__ZERO_TAIL_TIMING_NASH_RETAINED_CAP_LEDGER.md).
The review is
[`CODEX_PASCAL__ZERO_TAIL_TIMING_NASH_RETAINED_CAP_LEDGER__BY_STRENGTHENER.md`](../feedback/CODEX_PASCAL__ZERO_TAIL_TIMING_NASH_RETAINED_CAP_LEDGER__BY_STRENGTHENER.md).
The result is a supplied-law consequence, not a producer of a uniform
equilibrium and not a contradiction to the Fin4 hard residual.

## 1. Question and data

Let `I` be a nonempty finite player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting reward table.  Fix `N>0` and an independent mixed Nash law `P`
of the `N`-date timing game whose all-`infinity` outcome pays zero.  For each
player write

\[
 S_i=P_i(\infty),\qquad H_i=\prod_{j\ne i}S_j,
 \qquad M=\prod_jS_j=S_iH_i.
\tag{1.1}
\]

Let `A_i` be the equilibrium payoff, `F_(i,t)` the payoff of finite action
`t<N`, and `C_i` the payoff of action `infinity`.  Put

\[
 \alpha_i=\max_{t<N}(F_{i,t}-A_i),\qquad
 \beta_i=C_i-A_i.
\tag{1.2}
\]

Nash optimality gives `alpha_i<=0` and `beta_i<=0`.  If `S_i<1`, some finite
action is supported and `alpha_i=0`; if `S_i>0`, then `beta_i=0`.

Let `x=(u,B)` be a terminal semantic carrier point of globally minimum total
debt

\[
 d_i=B_i-u_i,\qquad D_*=\sum_i d_i>0.
\tag{1.3}
\]

Graft actual profiles converging semantically to `x` behind the timing law.
The fixed prefix map is continuous, so the limiting graft is again a carrier
point.  The exact playerwise graft debt is

\[
 D_i'=\max\{\alpha_i-Mu_i,\ \beta_i+H_iB_i-Mu_i\}.
\tag{1.4}
\]

This is full behavioral debt.  It uses the supremum over complete unilateral
behavioral deviations and does not assume that a best response is attained.

## 2. Signed minimum-balance inequality

Define the negative part `B_i^-:=max(-B_i,0)`.  Since

\[
 B_i^+-S_iu_i=d_i+(1-S_i)u_i+B_i^-,
\tag{2.1}
\]

zero-tail Nash optimality and global minimality give

\[
\begin{aligned}
 D_*
 &\le \sum_iD_i'\\
 &\le \sum_iH_i\bigl(d_i+(1-S_i)u_i+B_i^-\bigr).
\end{aligned}
\tag{2.2}
\]

Equivalently, every zero-tail timing Nash law satisfies the necessary
minimum-balance inequality

\[
 \boxed{
 \sum_i(1-H_i)d_i
 \le
 \sum_iH_i\bigl((1-S_i)u_i+B_i^-\bigr).}
\tag{2.3}
\]

The left side is the debt contraction bought by opponent absorption.  The
right side contains exactly the signed prescribed-payoff participation term
and the nonnegative negative-cap surcharge.  Positive values of those terms
are the two obstructions to contraction.  Thus the strict reverse
of (2.3), for even one produced zero-tail Nash law, contradicts positive
global minimum and gives the usual zero-minimum/uniform-payoff conclusion.
The Fin4 hard residual does not supply that strict reverse.

## 3. The adjusted zero-tail gap host

Assume a terminal exploitability gap `gamma>0` for every actual behavioral
profile.  Put

\[
 s_i=r_i(\{i\}).
\tag{3.1}
\]

First graft the all-Continue tail behind `P`.  Against all-Continue opponents,
player `i`'s prescribed payoff is zero and its complete behavioral cap is
`s_i^+=max(s_i,0)`.  Formula (1.4) therefore gives

\[
 D_i^0=\max\{\alpha_i,\ \beta_i+H_i s_i^+\}.
\tag{3.2}
\]

The global gap selects one player `i` with `D_i^0>=gamma`.  Because
`alpha_i<=0`, this same player satisfies

\[
 \boxed{s_i>0,\qquad \gamma\le\beta_i+H_i s_i.}
\tag{3.3}
\]

In particular `H_i>0` and `s_i>=gamma`.  This is the exact adjusted
finite-horizon escape witness, now tagged to the player whose retained-tail
ledger will be followed.

Suppose additionally that the minimum point has strict singleton separation
at this player:

\[
 \delta_i:=u_i-s_i>0.
\tag{3.4}
\]

Then `u_i>0` and `B_i>=u_i>0`, so the old finite arm in (1.4) is nonpositive.
The gap host is therefore governed entirely by the retained-cap arm, with the
following exhaustive trichotomy.

### No Never mass

If `S_i=0`, then

\[
 \boxed{D_i'\ge\gamma+H_i(d_i+\delta_i)>\gamma.}
\tag{3.5}
\]

Indeed,

\[
 \beta_i+H_iB_i
 = (\beta_i+H_is_i)+H_i(B_i-s_i),
\]

and `B_i-s_i=d_i+\delta_i`.

### Mixed Never mass

If `0<S_i<1`, support gives `alpha_i=beta_i=0`, and the exact interior ledger
becomes

\[
 \boxed{
 D_i'=H_i\bigl(d_i+(1-S_i)u_i\bigr)
 \ge H_id_i+(1-S_i)(\gamma+H_i\delta_i).}
\tag{3.6}
\]

Thus any quantitative amount of finite participation by the selected host
retains a correspondingly quantitative charge at the minimum-tail graft.

### Pure Never host

If `S_i=1`, then

\[
 \boxed{D_i'=H_id_i,\qquad 0<H_i<1.}
\tag{3.7}
\]

The first identity is the exact positive-cap endpoint formula.  Positivity of
`H_i` follows from (3.3).  If `H_i=1`, every player would choose pure
`infinity`; player `i` could then gain `s_i>0` by any finite action, contrary
to Nash.  Hence `H_i<1`.  If `d_i>0`, this arm strictly contracts that one
debt coordinate.  It does not lower positive-debt support rank, because the
multiplier is positive.

Equations (3.5)--(3.7) are the retained-cap relay: the adjusted zero-tail gap
host either keeps an explicit positive graft charge or becomes a pure-Never
host whose inherited debt is strictly contracted.

## 4. Why the relay does not close the Fin4 hard residual

The maintained hard residual supplies the terminal gap and, on the positive
minimum fiber, a uniform version of (3.4).  It therefore supplies every
hypothesis of the local relay once a zero-tail timing Nash law is selected.
It does not consume the surviving alternatives.

1. In the pure-Never arm, global minimality merely forces the loss
   `(1-H_i)d_i` to be offset by debt growth in other coordinates.  No endpoint
   remains on the same minimum fiber, and positive-debt support does not drop.
2. The hard nonprojective principal controls signs of entries of the
   normalized singleton matrix.  The quantities `alpha_i`, `beta_i`, `u_i`,
   and `B_i` also depend on nonsingleton outcomes and on the complete tail.
   The timing participation vector is not shown to satisfy the homogeneous or
   projective LCP equations on that principal.
3. The HOPF induced-owner compiler requires a nonpositive owner singleton and
   a signed average over one induced Nash law.  The relay's selected owner has
   `s_i>=gamma>0`, and the ledger selects no induced Nash law and controls no
   such average.  It therefore cannot be used as the HOPF owner; no theorem
   aligns a different HOPF owner with the gap host.
4. Punishment normality gives the minimum-fiber singleton separation used in
   (3.4), but it gives no sign for the two surcharges on the right of (2.3).

Thus the exact surviving obligation is a source-coherent compensation or
owner-alignment theorem.  The current hard-residual fields alone do not turn
the relay into a uniform payoff, support-rank descent, HOPF completion, or a
projective contradiction.

## 5. Regression check

For the two-player table

\[
 r(\{1\})=r(\{2\})=(1,1),\qquad r(\{1,2\})=(-1,-1),
\]

the one-date zero-tail Nash law has `S=H=2/3`.  Grafting the sure-pair tail
gives `u=-1`, `B=1`, `d=2`, and exact graft debt

\[
 H(B-Su)=\frac{10}{9}.
\]

This verifies the cap-sensitive ledger, but it deliberately lies outside the
relay hypothesis: its tail has `u=-1<s=1`, rather than strict minimum-fiber
singleton separation.  It therefore remains a sharp regression against any
attempt to infer (3.5)--(3.7) from the sign of `u` alone.

## 6. Inspected declarations and exact scope

The following checked declarations were inspected directly:

- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`;
- `quittingTerminalSemanticPair_rootThenContinuation` and
  `quittingTerminalSemanticCarrier_isCompact` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingTerminalDeviationDebt_rootThenContinuation_le_coordinateDefect_add`
  in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`;
- `exists_terminalGap_le_soloReward` in
  `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`;
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
  and
- `hardPrincipalDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalDispatch.lean`.

The finite timing law, the full graft formula, (2.3), and the relay are
ordinary mathematics not checked in Lean.  Nothing here asserts behavioral
attainment of the minimum carrier point, a produced source return, or a
uniform-equilibrium payoff.

## 7. Next exact question

In the pure-Never host arm (3.7), can the forced aggregate compensation be
localized to an endpoint which remains on the minimum fiber and strictly
lowers positive-debt support rank?  Without that localization, coordinate
contraction is not a recursive progress measure.
