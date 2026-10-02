# Independent audit of the HOPF owner-unsafe stationary closure

Reviewer: `CODEX_RIEMANN`

## Verdict

**PASS**, with one Lean-facing sign-convention clarification.

I independently checked the reward-table reduction, all four stationary
indifference polynomials, the rational Poincare--Miranda certificate, and the
compilation from a full-support zero of those polynomials to exact terminal
Nash against unrestricted behavioral deviations.  I found no unresolved
mathematical gap.

The note's face orientation is

\[
G_j<0\quad\text{on the lower }j\text{-face},\qquad
G_j>0\quad\text{on the upper }j\text{-face}.
\]

The checked theorem
`Math.Topology.exists_cube_zero_interior_of_strict_opposite_face_signs` in
`MathUE/Topology/PoincareMirandaCube.lean` uses the opposite convention.
Formalization should therefore apply it to the affine pullback of `-G`, not
literally to `G`.  This changes neither the zero set nor the mathematics.

## 1. Exact stationary equations

For player `i`, let

\[
s_i=\prod_{j\ne i}(1-x_j),\qquad h_i=1-s_i,
\]

let `A_i` be the unconditional absorbing contribution when `i` Continues,
and let `\bar g_i` be the expected gain from adding `i` to the current
opponent coalition.  Then

\[
Q_i=A_i+\bar g_i,\qquad N_i=A_i/h_i,
\]

and hence

\[
h_i(Q_i-N_i)=h_i\bar g_i-s_iA_i.
\]

The completion gives, exactly,

\[
\begin{aligned}
A_0&=(1-x_3)(-\tfrac12x_1+x_2),\\
A_1&=(1-x_3)(-\tfrac12x_0+x_2)
 +(d-1)x_0x_3(1-x_2),\\
A_2&=(1-x_3)(-\tfrac15(x_0+x_1)).
\end{aligned}
\]

These follow from the active passive matrix `M=-J/2` and the three specified
passive values on backgrounds containing player `3`; every other such active
passive value is zero.  Substitution gives the displayed `F_0,F_1,F_2`
without an omitted interaction term.

For player `3`, on a nonempty active coalition,

\[
A_3=s_3h_3+Rx_0-(R+1)x_1,
\]

while the empty active background contributes
`s_3 s_3^{surv}` to its membership expectation.  The two singleton terms
cancel in `h_3\bar g_3-s_3^{surv}A_3`, leaving exactly

\[
F_3=h_3(-x_0-x_1+x_2)
 -s_3^{surv}(Rx_0-(R+1)x_1).
\]

Thus the four polynomials in the note are correct for every real `s_3`, and
in particular for the positive singleton level used by the completion.

The orbit estimate used to make the certificate uniform is also sound:
`t_k <= 5b_k/4`, `b_{k+1} <= b_k/2`, and `b_0=1/100` give
`sum t_k <= 1/40`.  The root absorption at stage `k` is at most
`2t_k+z_k <= 3t_k`, so the elementary product/union bound gives
`P_{k+1} >= 37/40`.  Therefore

\[
0<R=\sum_k t_k/P_{k+1}\le 1/37.
\]

## 2. Independent exact face certificate

I recomputed the determinant of the displayed rational matrix `A`:

\[
\det A=
\frac{443076546006639}{156250000000000}>0.
\]

I then checked the eight face signs independently of the derivative boxes in
the note.  On each face, substitute the rational face coordinate and affinely
map the other three box coordinates and `R in [0,1/37]` to the unit cube.
Expanding the resulting polynomial in the tensor Bernstein basis gives exact
rational range enclosures.  The relevant endpoint bounds are:

\[
\begin{array}{c|cc}
j&\sup(G_j\text{ on lower face})&
   \inf(G_j\text{ on upper face})\\ \hline
0&-0.001187349960\ldots& 0.001212306000\ldots\\
1&-0.001399448683\ldots& 0.001445057526\ldots\\
2&-0.001322012772\ldots& 0.001334848889\ldots\\
3&-0.002024085365\ldots& 0.002089238265\ldots
\end{array}
\]

All calculations were performed over exact rational coefficients; the
decimals above only display the resulting strict margins.  In particular,
every lower-face value is at most `-1/1000` and every upper-face value is at
least `1/1000`, uniformly for the whole interval `R in [0,1/37]`.

After affine normalization of the box, apply
`Math.Topology.exists_cube_zero_interior_of_strict_opposite_face_signs` to
`-G`.  It supplies an interior zero of `G`.  Invertibility of `A` then gives
`F=0` at a point whose four hazards lie strictly in `(0,1)`.

## 3. Unrestricted behavioral compilation

At that full-support stationary root, every player's opponents have positive
one-period absorption probability.  Opponent absorption is therefore almost
sure.  For any unilateral behavioral strategy, before absorption the public
history is only the all-Continue history, while the opponents make fresh
independent draws from the same stationary product law.

Conditional on the player Quitting at the absorbing date, its expected payoff
is `Q_i`.  Conditional on the player Continuing while a nonempty opponent
coalition absorbs, its expected payoff is `N_i`.  Calendar dependence,
private randomization, and arbitrary history dependence only alter the mixing
weight between these two values.  Both endpoints are attainable by Quit-now
and Never.  Since `h_i>0` and `F_i=h_i(Q_i-N_i)=0`, one has `Q_i=N_i`.
The prescribed stationary mixture has that same value, so no behavioral
deviation gains.

This is represented directly by the checked stationary API:

- `quittingTerminalPayoff_update_stationary_le_unilateralCap` and
  `exists_quitNow_or_never_terminalPayoff_eq_unilateralCap` in
  `UniformEquilibrium/Quitting/Stationary/BestResponse.lean` cover the full
  behavioral strategy class;
- `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
  `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` in
  `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` provide the
  finite stationary-to-terminal/uniform handoff; and
- alternatively, after terminal Nash is obtained,
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  supplies the final uniform-payoff conclusion.

Thus the stationary closure is genuinely exact against all behavioral
deviations, not merely a stationary or pure-time equilibrium.  The sharp
owner-unsafe HOPF completion has `D_*=0`.

## 4. Additional safe-base check

I also independently checked Proposition 2 of
`CODEX_HOPF__HOPF_COMPLETION_SAFE_BASE_CHAMBERS.md`.  If

\[
J_{32}=r_3(\{2,3\})-r_3(\{2\})\le0,
\]

then the pure date-zero coalition `\{2\}` is exact against every behavioral
deviation:

- players `0` and `1` have join gains `-2`;
- player `3` has join gain `J_{32} <= 0`; and
- if player `2` refuses to Quit, all opponents Never, so every finite or
  randomized stopping law of player `2` pays its zero singleton reward, and
  Never also pays zero.

This is precisely the all-behavior pure-set characterization
`isεAsymptoticNash_pureSetRoot_iff_forall_mem_notMem` (equivalently
`isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet`) in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

The neighboring pure-pair screen is also correct.  Under the two member
no-leave inequalities and the two outsider no-join inequalities, the pure
coalition `\{2,3\}` contains two sure quitters; after any one player's
behavioral deviation at least one sure quitter remains, so the complete tail
is screened and the four Boolean endpoint inequalities are exhaustive.

These safe-base claims and the owner-unsafe stationary closure are ordinary
mathematics in the notes; this review does not claim that their table-specific
algebra has already been encoded or compiled in Lean.
