# Weighted-debt affine Bellman barriers are impossible

Author: `CODEX_HAHN`

## Status

**Exact dimension-independent no-go theorem in ordinary mathematics; not
Lean-checked.**  On the full compact semantic box of any bounded quitting
game with at least two players, no normalized weighted average of the debt
coordinates is a Bellman barrier.  The same holds for a finite minimum of
such weighted averages.

This rules out the most direct affine/min-of-affine implementation of the
controller--tester barrier dual.  It does not rule out affine functions with
separate payoff and cap coefficients and offsets, maxima or general
piecewise-affine functions, semialgebraic invariant sets, or barriers defined
only after adding further state constraints.

## 1. Exact statement

Let `I` be finite with at least two players, let the quitting rewards obey

\[
 |r_i(S)|\le R
\]

for some `R > 0`, and let

\[
 \mathcal Z_R=[-R,R]^I\times[-R,R]^I.
\]

For `z=(u,b)`, write

\[
 \delta_i(z)=b_i-u_i,
 \qquad
 d(z)=\max_i\delta_i(z).
\]

Let `T_x` be the exact terminal-semantic prefix action of an arbitrary
independent product root `x`.

For a probability vector `theta` on `I`, define

\[
 q_\theta(z)=\sum_i\theta_i\delta_i(z).
\tag{1}
\]

This is automatically a pointwise lower bound on maximum debt:

\[
 q_\theta(z)\le d(z).
\tag{2}
\]

### Theorem 1.1

There is no probability vector `theta` satisfying the Bellman monotonicity

\[
 q_\theta(z)\le q_\theta(T_xz)
 \qquad(z\in\mathcal Z_R,\ x\in[0,1]^I).
\tag{3}
\]

More generally, for any nonempty finite family of probability vectors
`theta^1,...,theta^m`, the function

\[
 q(z)=\min_{a\le m}q_{\theta^a}(z)
\tag{4}
\]

does not satisfy

\[
 q(z)\le q(T_xz)
 \qquad(z\in\mathcal Z_R,\ x\in[0,1]^I).
\tag{5}
\]

Thus neither (1) nor (4) can be a feasible target-free function barrier,
regardless of the reward table.

## 2. Deterministic-root debt formula on a nonempty toggle edge

For a nonempty coalition `S`, let `x^S` be the deterministic root at which
exactly the members of `S` Quit.  Every output debt lies in `[0,2R]`.  The
whole semantic output need not be independent of the tail: if `S={i}` and
the sole quitter `i` deviates to Continue, it exposes the continuation cap.

For a player `i` such that both `S` and `S triangle {i}` are nonempty, however,
the prescribed root and the toggled root both absorb immediately.  The
prescribed payoff is `r_i(S)`, and the relevant complete cap is

\[
 \max\{r_i(S),r_i(S\mathbin\triangle\{i\})\}.
\]

Therefore that coordinate's deterministic-root debt is exactly

\[
 g_i(S)
 =\bigl(r_i(S\mathbin\triangle\{i\})-r_i(S)\bigr)_+,
 \qquad 0\le g_i(S)\le2R.
\tag{6}
\]

No finite-horizon or stationary restriction is involved in this coordinate:
both of its possible current actions terminate at the first row.

## 3. Proof of Theorem 1.1

Take the top debt state

\[
 z^\top=(u,b),
 \qquad u_i=-R,
 \qquad b_i=R
 \quad(i\in I).
\tag{7}
\]

Every debt coordinate is `2R`, hence

\[
 q_\theta(z^\top)=2R.
\tag{8}
\]

Let `e_i^S` denote player `i`'s actual debt at `T_(x^S) z^top`.  If (3)
held, then for every nonempty coalition `S`, boundedness of all output debts
would give

\[
 2R\le\sum_i\theta_i e_i^S\le2R.
\tag{9}
\]

Equality in a weighted average of numbers at most `2R` implies

\[
 e_i^S=2R
 \qquad\hbox{for every }i\hbox{ with }\theta_i>0.
\tag{10}
\]

Choose one `i` with `theta_i > 0` and another player `j != i`.  Apply (10)
first to `S={j}` and then to `S={i,j}`.  In both cases toggling player `i`
leaves a nonempty coalition, so `e_i^S=g_i(S)` by formula (6).  The first
equality says

\[
 r_i(\{i,j\})-r_i(\{j\})=2R,
\]

so boundedness forces

\[
 r_i(\{i,j\})=R,
 \qquad r_i(\{j\})=-R.
\tag{11}
\]

The second equality reverses the same edge and says

\[
 r_i(\{j\})-r_i(\{i,j\})=2R,
\]

which forces the opposite assignments.  This contradiction proves the
single-weight case.

For the finite minimum (4), every branch has value `2R` at `z^top`, so
`q(z^top)=2R`.  Monotonicity and (2) give

\[
 2R\le
 \min_a\sum_i\theta_i^a e_i^S
 \le2R.
\]

Hence every branch separately has value `2R` at every pure coalition.  Pick
any branch and any positive coordinate of its probability vector, and repeat
the adjacent-coalition contradiction (11).  QED

## 4. What this removes from exact negative search

The exact controller--tester dual asks for a bounded upper-semicontinuous
function `q` satisfying

\[
 q\le d,
 \qquad q\le q\circ T_x
 \quad\hbox{for every product root }x.
\]

A weighted debt average is the canonical affine lower support of the maximum
debt, and a finite minimum of such supports is the first natural
piecewise-affine ansatz.  The theorem shows that universal prefix
monotonicity fails before the all-Never seed or any Fin4 hard-residual
condition is considered.

The failure comes from noncarrier states of the full semantic box, especially
`z^top`.  This is unavoidable for the function-barrier formulation, whose
Bellman inequality is quantified on the full box.  It does not invalidate a
closed invariant-set certificate: such a set can omit `z^top` while still
containing the all-Never seed and the whole terminal-semantic carrier.

Consequently the next exact templates should be one of:

1. a closed semialgebraic invariant set, such as the linearly relaxed contact
   cones in the companion note;
2. a function barrier with offsets and separate payoff/cap coefficients,
   checked against its true pointwise minorant conditions; or
3. a max/piecewise selection whose active affine branch may change between
   adjacent pure coalitions.

The theorem gives no evidence against those richer classes.

## 5. Source and implementation correspondence

The function-barrier inequality and full-box quantifier are the checked
target-free dual recorded in
`formalized/QUITTING_CONTROLLER_TESTER_VALUE_AND_BARRIER_DUALITY.md`.
The exact prefix map is `quittingTerminalSemanticPrefix`.  The pure-root
calculation (6) is the deterministic specialization of that map and uses no
additional project hypothesis.

The existing Python direct-hazard lower tree does not search function
barriers.  Its interval objective is the exact finite-clock maximum debt,
followed by the checked `24/N` transport.  This no-go therefore changes only
a proposed barrier-synthesis grammar; it does not remove or weaken the
complete exact finite-clock resolver.

## 6. Boundary tests and nonclaims

- At least two players are essential to choose the adjacent nonempty
  coalitions `{j}` and `{i,j}`.  No one-player claim is made.
- Reward boundedness is used sharply: debt `2R` at a pure root forces the two
  endpoint rewards to be opposite extremes.
- Restricting (3) to exact Nash roots would evade the proof but would not be
  a sound controller barrier.
- Requiring monotonicity only on the carrier would also evade `z^top`; that is
  a different certificate whose carrier membership is itself the original
  global problem.
- The result proves no uniform-equilibrium payoff and produces no positive
  gap table.  It only eliminates one finite barrier grammar exactly.
