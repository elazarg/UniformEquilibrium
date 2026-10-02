# Review of `CONTROLLER_VS_TESTER.md`: uniform-horizon identification

## Verdict

Section 5 is mathematically sound under the note's standing assumption that the
player set is finite and nonempty. I found no counterexample to any of the
following claims:

1. for every fixed behavioral profile, finite-horizon exploitability converges
   to complete terminal debt, even though a maximizing deviation may depend on
   the horizon;
2. the prescribed-target uniform value equals the terminal carrier objective
   and the decreasing finite-clock value;
3. minimizing over the target removes only the payoff-delivery coordinate and
   leaves the minimum terminal exploitability; and
4. this minimum is zero exactly when a uniform-equilibrium payoff exists.

These are exact semantic reformulations, not a solution of the quitting-game
existence conjecture. Their force is that any controller--tester formulation
using the value in Section 5 has the correct unrestricted behavioral and
uniform-horizon quantifiers.

## Claim checked

For a fixed profile \(\sigma\), let

\[
E_H(\sigma)=
\max_i\sup_{\tau_i}
\bigl(U_i^H(\sigma[i\leftarrow\tau_i])-U_i^H(\sigma)\bigr)
\]

and

\[
d(\sigma)=\max_i\bigl(B_i(\sigma)-U_i(\sigma)\bigr).
\]

The note claims \(E_H(\sigma)\to d(\sigma)\), then uses this to identify
\(W_r(v)\), the carrier minimum, and \(\lim_m V_m(v)\), and finally claims
\(\eta(r)=0\) if and only if the game has a uniform-equilibrium payoff.

## 1. The lower bound for \(E_H\) is valid

Fix \(\delta>0\), choose a player whose terminal debt is \(d(\sigma)\), and
choose one complete behavioral replacement with terminal gain at least
\(d(\sigma)-\delta\). The replacement is fixed while \(H\to\infty\).
Finite-average convergence for both the prescribed and replaced profiles then
gives

\[
\liminf_H E_H(\sigma)\ge d(\sigma)-\delta.
\]

Letting \(\delta\downarrow0\) gives the required lower bound. No interchange of
supremum and limit is used.

The convergence invoked here is the checked theorem
`tendsto_finiteAveragePayoff_quittingGame` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Asymptotic.lean`.

## 2. The upper bound is genuinely uniform over horizon-dependent deviations

Every player-coordinate terminal debt is at most \(d(\sigma)\), so for every
\(\delta>0\) the fixed profile \(\sigma\) is a terminal
\((d(\sigma)+\delta)\)-Nash profile. Apply
`quittingGame_isUniformεEquilibrium_of_terminalNash` from
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`
with the strictly larger error \(d(\sigma)+2\delta\). It supplies one horizon
threshold after which the Nash inequality holds for every player and every
complete behavioral replacement.

The universal quantifier over replacements lies inside the assertion for each
horizon. It therefore also covers a different maximizing replacement chosen
for each \(H\). Hence

\[
\limsup_H E_H(\sigma)\le d(\sigma)+2\delta,
\]

and then \(\delta\downarrow0\) proves the upper bound. This avoids the false
argument that pointwise convergence for each fixed deviation would be uniform
over all deviations.

The supremum is nonnegative because the prescribed strategy itself is an
allowed replacement, and it is finite because rewards are bounded.

## 3. The formula for \(W_r(v)\) is valid

For fixed \(\sigma\), both

\[
\lVert U^H(\sigma)-v\rVert_\infty
\quad\text{and}\quad E_H(\sigma)
\]

converge. Therefore the tail supremum in the definition of \(W_r(v)\) has
limit

\[
\max\{\lVert U(\sigma)-v\rVert_\infty,d(\sigma)\}.
\]

Taking the infimum over profiles gives the first equality in (27). No exchange
of the profile infimum with a limit is being asserted here: the tail operation
is evaluated separately for each fixed profile before the outer infimum.

The objective is continuous in the terminal semantic pair \((u,b)\). Its
infimum on realized pairs therefore equals its minimum on their compact
closure \(\mathcal K_r\). Conditional on the finite-word density result (21),
the equality with \(\lim_m V_m(v)\) follows from nested compact reachable sets
and continuity exactly as stated in Section 4.

## 4. Target minimization and the zero criterion are valid

Jointly minimizing over \(v\) and \((u,b)\in\mathcal K_r\) is legitimate on
the compact product. For each fixed semantic pair, choosing \(v=u\) eliminates
the delivery term and leaves

\[
\max_i(b_i-u_i).
\]

Every realized coordinate debt is nonnegative because retaining one's
prescribed strategy is an allowed behavioral replacement; this remains true
on the carrier closure. Thus a zero minimizer \((u_*,b_*)\) has
\(b_*=u_*\). Actual finite-word profiles converging semantically to this point
have terminal payoff converging to the one fixed vector \(u_*\) and terminal
Nash error converging to zero. The checked fixed-target compiler
`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
then proves that \(u_*\) is a uniform-equilibrium payoff.

Conversely, a uniform-equilibrium payoff supplies terminal approximate Nash
profiles at every positive error by
`quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff` in the
same file. Hence the minimum carrier debt is zero. Equivalently, this follows
from
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`.

The fixed-target quantifier is therefore not lost: the target is selected from
one zero-debt carrier point before accuracy-dependent approximating profiles
are chosen.

## Scope and wording cautions

- Equation (25) is a theorem for each fixed prescribed profile. It does not say
  that arbitrary sequences of profiles admit a common horizon threshold.
- The equality with \(\lim_mV_m(v)\) depends on the finite-word semantic
  density theorem in Section 4. Section 5 does not independently prove that
  density.
- Calling \(W_r(v)\) a controller--tester value is safe only for the explicit
  quantifier order in (26). It is not, without another theorem, the value of an
  online game in which the controller reacts dynamically to tester choices.
- The result is a complete semantic representation and finite-clock
  approximation. It supplies neither a proof that \(\eta(r)=0\) for all reward
  tables nor a table with \(\eta(r)>0\).

## Sources inspected

- `quittingGame_isUniformεEquilibrium_of_terminalNash`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`;
- `tendsto_finiteAveragePayoff_quittingGame`,
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Asymptotic.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`,
  `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff`, and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`,
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.
