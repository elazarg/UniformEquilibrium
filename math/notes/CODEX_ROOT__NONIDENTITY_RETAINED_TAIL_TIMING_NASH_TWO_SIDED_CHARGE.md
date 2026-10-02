# Nonidentity retained-tail timing Nash has two-sided charge

**Identity:** `CODEX_ROOT`  
**Status:** ordinary-mathematics lemma; not independently reviewed; no Lean
claim.  This is a sharpening of the checked retained-tail timing-Nash return
floor, not a consumer of the Fin4 residual.

## Question

Fix a finite quitting game with rewards in `[-R,R]`, an actual retained tail
`tau`, and a finite timing game in which the all-`infinity` action profile
returns to `tau`.  Assume the retained payoff is uniformly separated from
singleton quitting:

\[
 U_i(\tau)\ge r_i(\{i\})+\kappa
 \qquad(i\in I),\qquad \kappa>0.
\tag{1}
\]

The all-`infinity` timing profile is then a strict Nash equilibrium.  If the
finite timing game has a different mixed Nash equilibrium, must that
equilibrium carry a quantitative amount of finite absorption?

## Lemma

Let `mu` be a mixed Nash equilibrium of the retained-tail finite timing game.
Write

\[
 S_i=\mu_i(\infty),\qquad
 M=\prod_i S_i,
\tag{2}
\]

so `1-M` is the block absorption probability.  If `mu` is not the pure
all-`infinity` equilibrium, then

\[
 \boxed{
  1-M\ge
  \frac{\kappa}{(|I|-1)(2R+\kappa)}.}
\tag{3}
\]

For `Fin 4`, the denominator `|I|-1` is `3`.

### Proof

Because `mu` is not all-`infinity`, some player `i` assigns positive mass to
a finite timing action `t`.  Choose such a `t` in the support of `mu_i`.
Nash optimality implies that `t` is at least as good as the pure action
`infinity` against `mu_{-i}`.

Put

\[
 H_i:=\prod_{j\ne i}S_j,
 \qquad P_i:=1-H_i.
\tag{4}
\]

On the event that every opponent chooses `infinity`, action `t` makes `i`
quit alone and pays `r_i({i})`, whereas action `infinity` reaches the retained
tail and pays `U_i(tau)`.  By (1), the payoff difference on this event is at
most `-kappa`.  On the complementary event, the difference between the two
pure timing actions is at most `2R`.  Therefore

\[
 0
 \le U_i(t,\mu_{-i})-U_i(\infty,\mu_{-i})
 \le -\kappa H_i+2R(1-H_i).
\tag{5}
\]

It follows that

\[
 P_i=1-H_i\ge \frac{\kappa}{2R+\kappa}=:c.
\tag{6}
\]

The union bound gives

\[
 c\le 1-\prod_{j\ne i}(1-(1-S_j))
 \le \sum_{j\ne i}(1-S_j).
\tag{7}
\]

Hence some opponent `j != i` satisfies

\[
 1-S_j\ge \frac{c}{|I|-1}.
\tag{8}
\]

Since `M <= S_j`, equations (6)--(8) prove (3).  The argument uses only pure
timing deviations in the finite strategic game.

## Combination with the checked return floor

Under a terminal exploitability gap `gamma>0`, punishment separation, and an
actual retained tail, the checked theorem
`terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` gives

\[
 M\ge
 m_0:=\frac{\gamma^2}{2R(\gamma+2R)}>0.
\tag{9}
\]

Thus every nonidentity timing equilibrium satisfies the two-sided estimate

\[
 \boxed{
 m_0\le M\le
 1-\frac{\kappa}{(|I|-1)(2R+\kappa)}.}
\tag{10}
\]

It is therefore a literal finite block which both absorbs and returns to the
same actual tail with source-independent positive probabilities.

## Exact limitation

Equation (10) does **not** prove that a nonidentity equilibrium exists.  The
pure all-`infinity` equilibrium is strict under (1), and the reviewed timing
result does not select a second equilibrium.  Even if a second equilibrium is
supplied, its block payoff

\[
 u=A(\mu)+M U(\tau)
\tag{11}
\]

need not equal `U(tau)`, and the block is Nash against the prescribed tail
payoff rather than the tail cap.  Repetition can therefore destroy the Nash
inequalities.

The useful reduction is consequently:

\[
 \boxed{
 \begin{array}{c}
 \text{select a nonidentity retained-tail timing equilibrium}\
 \text{and close its payoff/cap seam}
 \end{array}
 \Longrightarrow
 \text{a uniformly charged literal return block}.}
\tag{12}
\]

The unresolved part is equilibrium selection and payoff/cap closure, not
clock diffusion or vanishing absorption.

## Inspected sources

- `formalized/FIN4_FULLY_SCREENED_TIMING_NASH_RETURN_FLOOR_NO_GO.md`;
- `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`.

No existing declaration or conference note was found stating the
nonidentity absorption floor (3).  The checked modules supply (9), not (3).

## Next question

Can the source-attached cumulative suffix-cap charge force a second Nash
equilibrium of one retained-tail timing game, or an equilibrium branch whose
block payoff closes to its returned payoff?  A positive answer would turn
(10) into an admissible-return producer; a negative answer should exhibit a
positive-minimum-compatible game in which the strict all-`infinity`
equilibrium is the only timing equilibrium at every finite horizon.
