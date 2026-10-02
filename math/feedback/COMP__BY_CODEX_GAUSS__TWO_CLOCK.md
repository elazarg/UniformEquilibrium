# Review of the periodic two-clock residual theorem

Reviewer: Codex Gauss

## Verdict

**REPAIR.** The mathematical consumer in Section 4 is correct after its
informal phrase "executable chronological data" is replaced by the exact
generated-secant hypotheses below. Its conclusion controls unrestricted
behavioral deviations, and terminal approximate equilibria obtained for
arbitrarily small `h` do select one fixed uniform-equilibrium payoff.

The displayed constant in `COMP.md` is valid but nonsharp. One may replace

\[
\Psi(A,B)=K(A+B)+B/\rho
\]

by

\[
\Phi(A,B)=KA+B+B/\rho.
\tag{R1}
\]

Section 4 is a conditional consumer. By itself it has no arbitrary-game
producer and does not pass export gate item 4. As part of the full `COMP.md`
reduction, however, it is a valid consumer for the remaining first-order
periodic-realization obligation.

## Claim checked

The audited claim is that a periodic sequence of literal quitting roots with
candidate payoff and debt annotations is terminal `O(h)`-Nash when:

* its prescribed and direct-debt Bellman defects are individually `O(h)`;
* the sum of either defect around one period is `O(h^2)`;
* both the joint-Continue clock and each generated best-response-secant clock
  contract by `Omega(h)` per period; and
* the candidate initial debt is `O(h)`.

The conclusion is against every unilateral behavioral strategy, rather than
only endpoint, stationary, periodic, or bounded-time deviations.

## Corrected exact statement

Let `I` be a nonempty finite player set and let `r` be a quitting reward
table. Fix an integer `K >= 1`, a number `0 < h <= 1`, nonnegative constants

\[
A_0,A_p,A_f,B_p,B_f
\]

and `rho > 0`.

Let `x_n` be a `K`-periodic sequence of product quitting roots and let
`u_n,d_n,s_{n,i}` be `K`-periodic real annotations. Put

\[
\beta_n=\Pr_{x_n}(\hbox{all players Continue}).
\]

The data must satisfy the following semantic conditions.

1. `d_{n,i} >= 0`.

2. For every `n,i`, `s_{n,i}` is an exact generated secant for the full
   behavioral best-response cap, comparing the actual successor tail with the
   candidate successor pair `(u_{n+1},u_{n+1}+d_{n+1})`. In particular,

   \[
   0\le s_{n,i}\le
   \Pr_{x_n}(\hbox{all opponents of }i\hbox{ Continue})\le1.
   \tag{R2}
   \]

   In repository terms this is exactly `secant_generated`, together with
   `secant_nonneg` and `secant_le_opponentContinue`, from
   `QuittingChronologicalDebtShadowingCertificate`.

3. Define the prescribed defect `p_{n,i}` and direct debt defect `f_{n,i}`
   using `QuittingChronologicalDebtData.prescribedDefect` and
   `QuittingChronologicalDebtData.directDebtDefect`. For every player,

   \[
   |p_{n,i}|\le A_ph,
   \qquad
   \left|\sum_{n=0}^{K-1}p_{n,i}\right|\le B_ph^2,
   \tag{R3}
   \]

   \[
   |f_{n,i}|\le A_fh,
   \qquad
   \left|\sum_{n=0}^{K-1}f_{n,i}\right|\le B_fh^2.
   \tag{R4}
   \]

4. The one-period clock products obey

   \[
   \prod_{n=0}^{K-1}\beta_n\le1-\rho h,
   \qquad
   \prod_{n=0}^{K-1}s_{n,i}\le1-\rho h
   \quad(i\in I).
   \tag{R5}
   \]

5. `d_{0,i} <= A_0 h` for every player.

Extend the root word periodically to an infinite literal behavioral profile
`sigma^h`. Then

\[
B_i(\sigma^h)-U_i(\sigma^h)
\le
\left[A_0+2\Phi(A_p,B_p)+\Phi(A_f,B_f)\right]h
\tag{R6}
\]

for every player, where `Phi` is (R1). Consequently `sigma^h` is terminal
`epsilon_h`-Nash against all behavioral deviations for the right-hand side
`epsilon_h`.

If the same constants work and such data exist for arbitrarily small positive
`h`, the quitting game has a uniform-equilibrium payoff.

No separate uniform boundedness field for `u,d` is needed: a real-valued
`K`-periodic annotation is bounded. Actual payoff and cap coordinates are
bounded by the finite reward bound.

## Proof

### Periodic Abel lemma

Let `a_n` be `K`-periodic and suppose

\[
|a_n|\le Ah,
\qquad
|R|:=\left|\sum_{n<K}a_n\right|\le Bh^2.
\]

Set `b_n=a_n-R/K`. Then `b` has zero period sum. Every unweighted prefix of
`b` is a collection of complete zero-sum periods followed by at most one
partial period, so

\[
\left|\sum_{n<N}b_n\right|
\le KAh+Bh^2.
\tag{R7}
\]

Let `c_n` be `K`-periodic with `0 <= c_n <= 1`, put

\[
W_n=\prod_{j<n}c_j,
\qquad
q=\prod_{n<K}c_n,
\]

and suppose `q <= 1-rho h`. Abel summation for the decreasing nonnegative
weights `W_n`, as proved by
`abs_survivalWeightedSum_le_prefixAbsMax`, gives

\[
\left|\sum_{n<N}W_nb_n\right|\le KAh+Bh^2.
\tag{R8}
\]

Moreover, division into complete periods gives

\[
\sum_{n\ge0}W_n
\le K\sum_{j\ge0}q^j
\le \frac{K}{\rho h}.
\tag{R9}
\]

Therefore, uniformly over finite cutoffs and hence in the infinite limit,

\[
\left|\sum_{n\ge0}W_na_n\right|
\le
KAh+Bh^2+\frac B\rho h
\le \Phi(A,B)h.
\tag{R10}
\]

This also proves that every relevant survival-weighted series converges. The
same argument works after any phase rotation, because the period sum and
period product are rotation invariant; only the finite order of the factors
changes, and multiplication is commutative.

### Two-clock debt account

Let `e^U_n` be actual prescribed payoff minus candidate prescribed payoff,
and let `e^B_n` be actual behavioral cap minus candidate cap. The exact
recursions are

\[
e^U_n=\beta_ne^U_{n+1}-p_n,
\]

\[
e^B_n=s_ne^B_{n+1}-(p_n+f_n).
\]

They are precisely `prescribedError_recursion` and
`bestResponseError_recursion` in
`ChronologicalDebtShadowing.lean`. Applying
`twoDiscountDebtError_eq` and sending the cutoff to infinity gives

\[
(e^B_0-e^U_0)
=-sum_{n\ge0}W^s_nf_n
+\sum_{n\ge0}(W^\beta_n-W^s_n)p_n.
\tag{R11}
\]

There is no sign reversal missing here: `f` is candidate debt minus the debt
of the one-step candidate prefix, so its adverse contribution is `-sum W^s f`.

The terminal remainders vanish. Indeed (R5) implies geometric decay along
period blocks for both survival products. The actual payoff and cap are reward
bounded, while candidate annotations are periodic and therefore bounded.

Apply (R10) once to `f` under `W^s`, and twice to `p`, under `W^beta` and
`W^s`. Since actual debt minus candidate debt is exactly `e^B-e^U`,

\[
d_i(\operatorname{Sem}(\sigma^h))-d_{0,i}
\le \Phi(A_f,B_f)h+2\Phi(A_p,B_p)h.
\]

The initial debt bound proves (R6).

### Behavioral and uniform conclusions

The cap in (R11) is
`quittingContinuationBestResponseValue`, which bounds the payoff from every
complete unilateral behavioral replacement. Thus (R6) is a terminal Nash
bound in the repository's unrestricted strategy class. This is exactly the
last step used by
`QuittingChronologicalDebtShadowingCertificate.isAsymptoticNash`; there is no
stationarity or bounded-stopping-time restriction on the deviator.

For every positive requested error, choose `h` small enough that the
right-hand side of (R6) is below that error. This gives terminal approximate
Nash profiles at every positive error. The checked theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
then selects, by compactness of the reward cube, one payoff target fixed before
the accuracy and proves it is a uniform-equilibrium payoff.

## Boundary and falsification tests

1. **The `B/rho` scale is necessary.** With `K=1`, forcing
   `a_0=Bh^2` and clock coefficient `1-rho h`, the infinite weighted forcing
   is exactly `Bh^2/(rho h)=(B/rho)h`.

2. **Zero period sum still costs order `h`.** With `K=2`, forcing
   `(h,-h)` and a clock that loses all survival after the first phase, the
   weighted forcing is `h`. Hence period cancellation cannot improve the
   answer to `O(h^2)`; the local `A` term is genuine.

3. **Both clock contractions matter.** In the underlying two-recursion
   identity, a noncontracting homogeneous mode leaves an arbitrary bounded
   terminal remainder even when `p=f=0`. Thus neither the joint nor secant
   contraction may be dropped from this certificate without an independent
   boundary condition.

4. **Period-sum control matters.** A constant forcing of order `h` under a
   `1-rho h` clock accumulates to order one. The improvement comes from the
   `O(h^2)` period sum, not merely the local `O(h)` bound.

5. **Never and arbitrarily late deviations are included.** They are included
   in `quittingContinuationBestResponseValue`; no finite-horizon truncation is
   used in (R11).

These tests did not falsify the corrected theorem.

## Source audit

The exact algebraic dependencies inspected were:

* `twoDiscountDebtError_eq`,
  `abs_survivalWeightedSum_le_prefixAbsMax`, and
  `tendsto_survivalProduct_mul_bounded_zero` in
  `MathUE/Probability/OneSidedDebtShadowing.lean`;
* `exists_quittingTerminalSemanticPrefix_secant`, the definitions in
  `QuittingChronologicalDebtData`, and the recursions and behavioral cap
  conversion in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`;
* `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The existing chronological certificate assumes a uniform bound on every
unweighted suffix discrepancy. A periodic forcing with a nonzero `O(h^2)`
period sum does not have such a uniform unweighted bound over arbitrarily many
periods. The new content is the direct use of per-period clock contraction to
sum that residual as `O(h)`. It is not a restatement of the existing
certificate theorem.

## Lean handoff

The clean split is:

1. In `MathUE/Probability`, prove a generic periodic weighted-forcing lemma
   giving the `Phi(A,B)h` bound (R10). Use natural-indexed periodic functions
   and state `0 < K` explicitly.
2. Define a quitting-specific periodic data structure whose fields are the
   roots, prescribed/debt annotations, generated secants, residual estimates,
   and the two one-period contractions. Do not make the desired terminal Nash
   conclusion a field.
3. Instantiate `twoDiscountDebtError_eq` directly. The existing
   `QuittingChronologicalDebtShadowingCertificate` is not quite the right
   intermediate object because its unweighted all-suffix hypothesis generally
   fails when the period sum is nonzero.
4. Prove the terminal-Nash bound through
   `quittingTerminalPayoff_update_le_continuationBestResponseValue`, then call
   `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`.

The mathematical consumer is ready for formalization after the statement is
repaired as above. Producing these periodic data from the closed Fin4 endpoint
monodromy remains open.
