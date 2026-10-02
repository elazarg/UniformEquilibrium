# Review of `gpt/DECIDE.md`

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Verdict: **mathematically sound as a reduction, but almost entirely duplicate;
it does not change the Fin4 frontier.**

## Claim audit

1. **Stopping-law normal form.**  Correct.  Independent behavioral strategies
   are exactly independent laws on \(\mathbb N\cup\{\infty\}\), and the
   unrestricted behavioral cap is the supremum of pure stopping-time values.
   This is existing infrastructure, not a new theorem.

2. **Late-versus-Never identity.**  Correct:
   \[
   \lim_{t\to\infty}V_i(t)-V_i(\infty)
     =r_i(\{i\})\prod_{j\ne i}\mu_j(\infty).
   \]
   The finite all-Continue-tail version and its unrestricted-cap consequences
   are already checked in
   `TerminalSemanticFiniteDeadlineNashEscalation.lean`; compact stopping-law
   tail and truncation control is already checked in
   `OpponentTightTerminalSemanticRealization.lean`.

3. **Finite-support approximation and \(\varepsilon_T\) characterization.**
   Correct provided the stated total-variation convention is used.  Moving
   every finite atom after \(T\) to Never converges in marginal total
   variation, uniformly controls every unilateral pure-time value, and hence
   controls the supremum cap.  The equality of infima and the decreasing
   sequence \(\varepsilon_T\downarrow\inf E_r\) are then routine.  This is a
   useful compact formulation, but it packages the already checked
   finite-deadline/projective-boundary machinery and the prior
   `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` / finite-horizon escape
   reduction rather than supplying a new producer or consumer.

4. **Two-anchor lemma.**  Correct and elementary.  If two distinct marginal
   Never masses vanish, every deviator has at least one opponent with zero
   Never mass, so every finite time beyond the declared horizon is payoff-
   equivalent to Never.  Finite-game Nash therefore controls the complete
   behavioral response class.  This is a special sufficient boundary
   consumer, not a solution of the zero/one-anchor chamber.

5. **Procrastinating finite-Nash regression.**  Correct.  At the final row the
   symmetric mixture \(q=2/3\) makes Quit and Continue indifferent at payoff
   \(4/3\); arbitrary all-Continue padding preserves finite-horizon Nash, while
   quitting just after the horizon gives \(5/3\), a permanent gain \(1/3\).
   The example has an exact terminal Nash profile, so it refutes only arbitrary
   finite-horizon equilibrium selection.  This is a clean regression but does
   not affect the positive-minimum residual.

## Novelty and frontier verdict

The only potentially useful incremental packaging is the explicit scalar
sequence \(\varepsilon_T\) and the two-anchor sufficient condition.  Neither
advances the current Fin4 consumer: the unresolved case remains finite timing
Nash laws with at most one zero Never marginal and a nonvanishing first-
excluded-date gain.  Existing adjacent-deadline and projective-compatibility
results already identify that boundary and require a compatible selection or
large-effect consumer.  `gpt/DECIDE.md` supplies neither.

Recommendation: retain only as an internal explanatory/regression note if
desired; do not export as new mathematics and do not revise the Fin4 frontier
on its basis.
