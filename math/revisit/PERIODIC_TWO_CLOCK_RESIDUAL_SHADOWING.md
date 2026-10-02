# Periodic two-clock residual shadowing

Authors: Codex Root (assembly of the mathematical argument in `COMP.md`)

Independent reviews and falsification attempts:
[Codex Gauss](../feedback/COMP__BY_CODEX_GAUSS__TWO_CLOCK.md) and
[Codex Poincare](../feedback/COMP__BY_CODEX_POINCARE.md)

## Exact statement

Let `I` be a nonempty finite player set, let `r` be a quitting-game reward
table, and fix a positive integer period `K`. Fix nonnegative constants

\[
A_0,A_p,A_f,B_p,B_f
\]

and `rho > 0`. For `A,B >= 0`, define

\[
\Phi(A,B):=KA+B+\frac B\rho. \tag{1}
\]

For every `0 < h <= 1`, suppose the following executable data are supplied.

- A `K`-periodic sequence `x_k` of product quitting roots.
- `K`-periodic candidate prescribed-payoff vectors `u_k` and nonnegative
  candidate debt vectors `d_k`.
- For every phase `k` and player `i`, an exact generated best-response secant
  `s_{k,i}`.

Extend the root word periodically to the infinite literal behavioral profile
`sigma^h`. Let `Sigma_k^h` be its actual tail beginning at phase `k`, with
actual terminal-semantic pair

\[
Z_k^h=(U_k^h,B_k^h).
\]

Put

\[
c_{k+1}:=(u_{k+1},u_{k+1}+d_{k+1})
\]

and let `Prefix_r(x,z)` be the exact one-stage terminal-semantic prefix of
tail pair `z` by root `x`.

The secant is required to satisfy

\[
0\le s_{k,i}\le
\Pr_{x_k}(\text{all opponents of }i\text{ Continue})\le1, \tag{2}
\]

and the exact generated identity

\[
B_{k,i}^h-\operatorname{Prefix}_r(x_k,c_{k+1})_{B,i}
=s_{k,i}\bigl(B_{k+1,i}^h-(u_{k+1,i}+d_{k+1,i})\bigr). \tag{3}
\]

Define the prescribed Bellman defect

\[
p_{k,i}:=u_{k,i}-
  \operatorname{Prefix}_r(x_k,c_{k+1})_{U,i}, \tag{4}
\]

and the direct debt defect

\[
f_{k,i}:=d_{k,i}-
  d_i\bigl(\operatorname{Prefix}_r(x_k,c_{k+1})\bigr). \tag{5}
\]

Assume, for every player and phase,

\[
|p_{k,i}|\le A_ph,
\qquad
\left|\sum_{k=0}^{K-1}p_{k,i}\right|\le B_ph^2, \tag{6}
\]

\[
|f_{k,i}|\le A_fh,
\qquad
\left|\sum_{k=0}^{K-1}f_{k,i}\right|\le B_fh^2, \tag{7}
\]

and

\[
d_{0,i}\le A_0h. \tag{8}
\]

Let

\[
\beta_k:=\Pr_{x_k}(\text{all players Continue}).
\]

Assume both one-period clocks contract at linear scale:

\[
\prod_{k=0}^{K-1}\beta_k\le1-\rho h, \tag{9}
\]

\[
\prod_{k=0}^{K-1}s_{k,i}\le1-\rho h
\qquad(i\in I). \tag{10}
\]

Then the actual periodic behavioral profile is terminal
`epsilon_h`-Nash against every unilateral behavioral strategy, where

\[
\boxed{
\epsilon_h
\le
\bigl[A_0+2\Phi(A_p,B_p)+\Phi(A_f,B_f)\bigr]h.} \tag{11}
\]

In particular, if the same period and constants work for arbitrarily small
positive `h`, the quitting game has a uniform-equilibrium payoff.

## Conjecture-facing change

The maintained chronological-debt compiler consumes exact executable root
sequences, but its existing convenient interface asks for uniformly small
unweighted discrepancy on every suffix. A periodic construction with a
nonzero `O(h^2)` residual per turn generally fails that hypothesis after many
turns.

This theorem proves that the exact two-clock Green account nevertheless
consumes such a construction: local `O(h)` defects, `O(h^2)` period sums, and
`Omega(h)` contraction of both clocks yield `O(h)` unrestricted terminal
debt. It therefore replaces an exact-closing or all-suffix producer
obligation by a strictly weaker first-order periodic realization obligation.

For the source-closed endpoint cycles in
`SAME_STAGE_ENDPOINT_MONODROMY_REDUCTION.md`, it is enough to construct an
ordered small-`h` Bellman packet whose first derivatives reproduce the closed
payoff/debt increments, whose period errors are quadratic, and whose two
clocks have linear exposure. Producing that packet remains open.

## Definitions, probability, and agency

The roots are literal independent product action laws executed successively
on the unique live public history. The candidate vectors are annotations;
the actual profile is the infinite periodic root sequence.

The cap coordinate `B_i` is the supremum over all unilateral behavioral
replacements, including Never and arbitrarily late or randomized stopping.
The secant in (3) is not a restricted best-response derivative. It is the
exact secant of the max-affine one-step Snell envelope and is bounded by the
probability that all opponents of `i` Continue.

No public correlation, bounded horizon, stationarity of the deviator, or
interchange of supremum and expectation is used.

## Source correspondence

The exact game-facing objects in (2)--(5) are already defined in
`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`:

- `QuittingChronologicalDebtData` stores roots, prescribed annotations, debt,
  and generated secants;
- `candidateSuccessorPair`, `prescribedDefect`, and `directDebtDefect` are
  exactly (4)--(5);
- `exists_quittingTerminalSemanticPrefix_secant` supplies (2)--(3);
- `prescribedError_recursion` and `bestResponseError_recursion` are the exact
  two backward recursions; and
- the cap conversion in
  `QuittingChronologicalDebtShadowingCertificate.isAsymptoticNash` is against
  the full behavioral strategy class.

`twoDiscountDebtError_eq` and the survival-weighted Abel estimate are checked
in `MathUE/Probability/OneSidedDebtShadowing.lean`. The new content is the
periodic weighted-forcing estimate below and its direct use with a nonzero
`O(h^2)` period mean.

The fixed-payoff conclusion uses
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

## Proof

### Periodic weighted forcing

Let `a_k` be `K`-periodic and satisfy

\[
|a_k|\le Ah,
\qquad
R:=\sum_{k=0}^{K-1}a_k,
\qquad |R|\le Bh^2.
\]

Write

\[
b_k=a_k-R/K.
\]

The sequence `b` has zero period sum. Every finite prefix contains complete
zero-sum periods and at most one partial period, so

\[
\left|\sum_{k<N}b_k\right|
\le KAh+Bh^2. \tag{12}
\]

Let `c_k in [0,1]` be `K`-periodic, let

\[
W_n=\prod_{j<n}c_j,
\qquad q=\prod_{k<K}c_k,
\]

and assume `q <= 1-rho h`. Since `W_n` is nonnegative and decreasing, Abel
summation and (12) give

\[
\left|\sum_{n\ge0}W_nb_n\right|
\le KAh+Bh^2. \tag{13}
\]

Dividing the nonzero mean into periods gives

\[
\sum_{n\ge0}W_n\le\frac K{1-q}\le\frac K{\rho h},
\]

and hence

\[
\left|\sum_{n\ge0}W_n\frac RK\right|
\le\frac B\rho h. \tag{14}
\]

Because `h <= 1`, (13)--(14) imply

\[
\boxed{
\left|\sum_{n\ge0}W_na_n\right|
\le\Phi(A,B)h.} \tag{15}
\]

The argument is unchanged after a cyclic phase rotation: the period sum and
the product of scalar clock factors are rotation invariant.

### Exact two-clock account

For one player, let

\[
e^U_k=U_k^h-u_k,
\qquad
e^B_k=B_k^h-(u_k+d_k).
\]

Literal prefixing and the generated secant identity give

\[
e^U_k=\beta_ke^U_{k+1}-p_k, \tag{16}
\]

\[
e^B_k=s_ke^B_{k+1}-(p_k+f_k). \tag{17}
\]

Unrolling these recursions separately yields the checked exact identity

\[
e^B_0-e^U_0
=-
\sum_{n\ge0}W_n^s f_n
+
\sum_{n\ge0}(W_n^\beta-W_n^s)p_n. \tag{18}
\]

The terminal remainders vanish: (9)--(10) give geometric decay over period
blocks; actual payoffs and caps are bounded by the finite reward table; and
the periodic candidate annotations are bounded.

Apply (15) once to `f` under the secant clock and twice to `p`, under the joint
and secant clocks. Since actual debt minus candidate debt is
`e^B-e^U`,

\[
d_i(\Sigma_0^h)-d_{0,i}
\le
\Phi(A_f,B_f)h+2\Phi(A_p,B_p)h.
\]

Equation (8) proves (11). The cap used above is the unrestricted behavioral
cap, so this is a terminal Nash bound against every behavioral deviation.

For every requested positive error, choose a sufficiently small `h`.
Terminal approximate Nash profiles then exist at all errors. Compact payoff
selection and the checked terminal-to-uniform theorem produce one payoff
chosen before the accuracy, proving the final conclusion.

## Boundary tests and falsification attempts

1. **The `B/rho` term is necessary.** For `K=1`, forcing `a=Bh^2` and
   clock factor `1-rho h` give total weighted forcing exactly `(B/rho)h`.
2. **Zero period mean still costs order `h`.** For `K=2`, forcing `(h,-h)`
   and a clock that loses survival after the first phase leave weighted forcing
   `h`.
3. **An `O(h)` mean is insufficient.** Constant forcing `h` under a
   `1-rho h` clock accumulates to `1/rho`, not `O(h)`.
4. **Both contractions matter.** Without contraction of either recursion, a
   bounded nonzero terminal homogeneous mode can survive even when `p=f=0`.
5. **Generated secants are essential.** Arbitrary coefficients in `[0,1]`
   would prove only an abstract recursion estimate. Identity (3) is what
   identifies the second recursion with the full behavioral best-response
   cap.

These tests were included in two independent attempts to falsify the theorem.

## Adapter and consumer

The actual-data adapter is a periodic
`QuittingChronologicalDebtData` together with the exact generated-secant,
residual, and contraction hypotheses (2)--(10). This is an executable root
sequence, not a carrier or occupation-measure relaxation.

The theorem's direct consumer is the checked all-behavior terminal-Nash
criterion, followed by terminal-to-uniform payoff selection. Its outstanding
producer is the construction of these data from arbitrary-game structure or
from the two Fin4 endpoint-monodromy geometries.

## Lean handoff

First prove in `MathUE/Probability` a generic periodic weighted-forcing lemma
implementing (15), with `0 < K` explicit. Then define a quitting-specific
periodic structure containing:

```lean
roots prescribed debt secant
debt_nonneg
secant_nonneg secant_le_opponentContinue secant_generated
prescribedDefect_bound prescribedDefect_periodSum_bound
directDebtDefect_bound directDebtDefect_periodSum_bound
joint_period_contraction secant_period_contraction
initial_debt_le
```

Instantiate `twoDiscountDebtError_eq` directly. The existing
`QuittingChronologicalDebtShadowingCertificate` should not be used as the
intermediate result, because a nonzero period mean does not satisfy its
uniform unweighted all-suffix discrepancy field.

Conclude through the existing behavioral-cap bound and
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`.

## Scope and nonclaims

This is a sound periodic compiler, not a completeness theorem for periodic
strategies and not an arbitrary-game producer. It does not construct the
small-`h` data from a horizontal endpoint cycle, show that either Fin4 cycle
geometry admits them, or turn failure of their construction into a rank drop.
It does not weaken the requirement that both clocks contract.
