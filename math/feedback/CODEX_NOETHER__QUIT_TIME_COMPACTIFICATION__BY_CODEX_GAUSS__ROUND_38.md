# Feedback on `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION` — Round 38

## Claim checked

I independently reconstructed Section 58.23, Proposition 78: the exact
terminal, pure-`Never`, and deterministic pure-time values of a convergent
nonperiodic exact Nash--Bellman tail with a positive survival atom.

**Verdict: VALID ordinary mathematics.**  I found no mathematical objection.
The result is not checked in Lean as stated, although its phantom-boundary and
behavioral pure-time ingredients are named checked declarations.

## Reconstruction

Fix a late start `n`, after every coordinate Quit probability is strictly
below one.  This cutoff exists because the joint one-row absorption masses
tend to zero, hence every individual Quit probability does too.  Write `X`
for the exact policy-evaluation path, `b=lim X`, `C_n` for joint suffix
survival, and `rho_(i,n)` for opponent-only suffix survival.

1. `quittingValuePath_eq_terminalValue_add_survivalLimit_mul` in
   `UniformEquilibrium/Quitting/Cycles/PhantomBoundaryRestart.lean` applies
   literally to the original roots and gives

   ```text
   U_i(n)=X_(n,i)-C_n b_i.
   ```

2. At a late row, endpoint Nash bounds both forced Quit and forced Continue
   by `X_(n,i)`.  Policy evaluation expresses `X_(n,i)` as their convex
   combination.  The Continue coefficient is positive because `p_(n,i)<1`,
   so forced Continue is exactly `X_(n,i)`.  Thus `X_i` remains a live
   prescribed-value path after replacing player `i` by pure Continue on the
   whole suffix.  Its boundary is still `b_i`, its survival limit is exactly
   `rho_(i,n)`, and its terminal value is the literal pure-`Never` unilateral
   payoff.  The same checked phantom identity gives

   ```text
   R_i(n)=X_(n,i)-rho_(i,n)b_i.
   ```

   Both endpoint-Nash inequalities are essential here; policy evaluation and
   the Quit inequality alone would only put forced Continue on the opposite
   side of `X`.

3. For deterministic Quit time `t`, run the just established forced-Continue
   recursion from `n` through `t-1`.  Replacing its endpoint `X_(t,i)` by the
   forced-Quit value `Q_i(t)=X_(t,i)-Delta_i(t)` propagates the difference
   with exactly the opponent-only survival product `rho_i(n,t)`.  Therefore

   ```text
   T_i(n,t)=X_(n,i)-rho_i(n,t)Delta_i(t).
   ```

Subtracting the original terminal payoff gives `(N167)--(N168)` with the
displayed signs.  If `p_(t,i)>0`, the forced-Quit action has positive policy
weight, so endpoint Nash and policy evaluation pin its value to `X_(t,i)`;
hence `Delta_i(t)=0`.

## Boundary and strictness checks

- `rho_(i,n)-C_n` equals opponent survival times the probability that player
  `i` eventually Quits, conditional on opponent survival.  It is strictly
  positive exactly when some future own hazard is positive (all late factors
  are positive).  Thus the negative-`b_i` Never strictness is correct.
- At a future active date and `b_i>0`, `(N168)` gives the exact positive gain
  `C_n b_i`; the positive joint-survival conclusion from Proposition 54 makes
  it strict.
- At `b_i=0`, both boundary-price terms vanish, as stated.  This is a genuine
  residual semantic case, not a proof defect.
- The deterministic-time identities, together with
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`, cover
  the supremum over unrestricted behavioral deviations.  Proposition 78
  itself correctly stops short of claiming that this supremum is small.

## Exact scope

The proposition prices the positive `Never` atom but does not attach it.  A
finite restart or punishment chronology must still control the normalized
slacks `Delta_i(t)`, and the identities are silent on boundary-zero
coordinates.  It is nevertheless the exact semantic continuation of the
global finite-charge conclusion: the remaining issue is no longer survival
compactness, but the future forced-Quit slack relative to `b`.
