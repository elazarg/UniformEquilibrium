# Controller versus tester

The quitting-game synthesis problem has an exact controller–tester
formulation. The controller chooses a product-root chronology. The tester
chooses a player and an unrestricted behavioral stopping strategy, including
Never and arbitrarily late dates.

This formulation is complete: it has the same value as the original
uniform-horizon quantifiers. It does not determine the sign of that value for
four players.

## Exact forward tester state

For a prescribed chronology, a forward state records:

- accumulated prescribed payoff and joint survival;
- for each player, accumulated payoff from earlier opponent absorption;
- each player's opponent-survival probability; and
- the best payoff among all elapsed pure stopping dates.

The state has dimension \(4|I|+1\), hence \(17\) for four players. Its
reachable closure is compact. Its limit gives both the prescribed payoff and
the complete behavioral cap:

\[
B_i
=
\max\{\text{best finite stopping-date value},\text{Never value}\}.
\]

The tester also has an exact occupation-flow primal. Its Bellman dual requires
the transversality condition

\[
\liminf_{t\to\infty}L_{i,t}w_{i,t}\ge0,
\]

which prevents the recursive equation from discarding the unresolved Never
branch. The full construction and duality proof are in
TESTER_LEDGER_AND_FLOW.md.

## Exact finite-window controller

Optimize a finite product-root word, then prescribe all players to Continue
forever. The endpoint ledger evaluates the full terminal payoff and every
behavioral deviation, not merely deviations confined to the finite window.

For target \(v\), the length-\(m\) value \(V_m(v)\) decreases to

\[
W_r(v)
=
\min_{(u,b)\in\mathcal K_r}
\max\left\{
\|u-v\|_\infty,
\max_i(b_i-u_i)
\right\},
\tag{1}
\]

where \(\mathcal K_r\) is the compact terminal-semantic carrier.

For each fixed profile, finite-horizon exploitability converges to terminal
exploitability uniformly over horizon-dependent choices of the deviator:

\[
\max_i\sup_{\tau_i}
\left[
U_i^H(\sigma[i\leftarrow\tau_i])-U_i^H(\sigma)
\right]
\longrightarrow
\max_i(B_i(\sigma)-U_i(\sigma)).
\tag{2}
\]

Thus \(W_r(v)\) is exactly the original offline uniform-horizon value with
prescribed target \(v\). The fixed-target quantifier is retained.

Allowing the controller to select the target gives

\[
\boxed{
\eta(r)
=
\min_{(u,b)\in\mathcal K_r}\max_i(b_i-u_i),}
\tag{3}
\]

and

\[
\boxed{
\eta(r)=0
\quad\Longleftrightarrow\quad
r\text{ has a uniform-equilibrium payoff}.}
\tag{4}
\]

The proof, including finite-word semantic density and the Never boundary, is
in FINITE_WINDOW_SEMANTIC_VALUE.md.

## Exact barrier dual

Let \(T_x\) be semantic prefixing and

\[
d(u,b)=\max_i(b_i-u_i).
\]

The target-free value has two exact dual forms:

\[
\eta(r)
=
\max_q q(e_\infty),
\tag{5}
\]

where \(q\) ranges over bounded upper-semicontinuous functions satisfying

\[
q\le d,
\qquad
q\le q\circ T_x
\quad\text{for every root }x,
\]

and

\[
\eta(r)
=
\max\left\{
\gamma:
\begin{array}{l}
e_\infty\in C,\ C\text{ closed},\\
T_x(C)\subseteq C\ \forall x,\\
d\ge\gamma\text{ on }C
\end{array}
\right\}.
\tag{6}
\]

The canonical greatest function barrier is the infimum of future finite-word
debts. The smallest closed invariant set is exactly \(\mathcal K_r\).
SEMANTIC_BARRIER_DUALITY.md contains the proofs and the positive-gap decoder.

## Relation to the sufficient-state no-go

There is no contradiction with SUFFIX_INFORMATION_OBSTRUCTION.md. The forward
ledger evaluates a chronology from its beginning. It does not make arbitrary
calendar suffixes into one equicontinuous family on a compact state.

The controller formulation therefore realizes one of the viable architectures
left by the no-go: a compact forward semantic state whose legal program is
prefix construction, with complete tester information accumulated along that
program.

## Remaining theorem

The reformulation is exact but not a proof of existence. For four players one
must still prove

\[
\eta(r)=0
\]

for every reward table, or produce one concrete table and a positive barrier.
The canonical carrier and barrier encode the original value and need not have
an effective finite description.
