# Exact joint-reset lift

## Scope

The terminal semantic prefix dynamics of a finite quitting game admits a lift
to a finite state space that does not independently recombine the histories of
different semantic coordinates.

The lift reproduces every finite semantic chronology exactly. It need not
produce a positive-debt barrier or show that the selector-consistent reachable
closure has a finite semialgebraic description.

## Checked interface

A finite law on joint coordinate-reset maps semiconjugates exactly to the
terminal semantic prefix map. The central construction is proved in Lean in
[`TerminalSemanticJointResetLift`](../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticJointResetLift.lean):
it defines the finite reset modes and tagged transition, proves the
left-regular-band and reset-support laws, maximizing-selector branch identity,
and law-level semiconjugacy. It also proves total-debt linearity, arbitrary-law
two-anchor sensitivity, and the explicit iterated payoff-spine and
cap-retention products (15)--(17).

The lift avoids false coordinatewise recombination at the representation
level. It does not prove a positive debt barrier.

## 1. Semantic branch maps

Let \(I\) be a finite player set and let \(r(S)\in\mathbb R^I\) be the
terminal reward for each nonempty \(S\subseteq I\). A semantic state is

\[
z=(u,b)\in\mathbb R^I\times\mathbb R^I.
\]

For a product root \(x\), put \(q_i=x_i(\mathrm Q)\). For a pure root
outcome \(\omega\in\{\mathrm C,\mathrm Q\}^I\), define

\[
S(\omega)=\{i:\omega_i=\mathrm Q\},\qquad
p_x(\omega)=
\prod_{i\in S(\omega)}q_i
\prod_{i\notin S(\omega)}(1-q_i).
\]

For player \(i\), write \(Q_i(x_{-i})\) and \(C_i(x_{-i};b_i)\) for the
forced-Quit and forced-Continue endpoint values. Choose one selector vector
\(\varepsilon\in\{\mathrm Q,\mathrm C\}^I\) satisfying

\[
\begin{cases}
Q_i(x_{-i})\ge C_i(x_{-i};b_i),&\varepsilon_i=\mathrm Q,\\
C_i(x_{-i};b_i)\ge Q_i(x_{-i}),&\varepsilon_i=\mathrm C.
\end{cases}
\tag{1}
\]

Ties may be resolved arbitrarily.

For \(A_i(\omega)=S(\omega)\setminus\{i\}\), define the affine coordinate-
reset map \(E_{\varepsilon,\omega}\) by

\[
E_{\varepsilon,\omega}(u,b).u=
\begin{cases}
u,&S(\omega)=\varnothing,\\
r(S(\omega)),&S(\omega)\ne\varnothing,
\end{cases}
\tag{2}
\]

and

\[
E_{\varepsilon,\omega}(u,b).b_i=
\begin{cases}
r_i(A_i(\omega)\cup\{i\}),&\varepsilon_i=\mathrm Q,\\
b_i,&\varepsilon_i=\mathrm C,\ A_i(\omega)=\varnothing,\\
r_i(A_i(\omega)),&\varepsilon_i=\mathrm C,\ A_i(\omega)\ne\varnothing.
\end{cases}
\tag{3}
\]

Put

\[
G_{x,\varepsilon}(z)=
\sum_{\omega}p_x(\omega)E_{\varepsilon,\omega}(z).
\tag{4}
\]

For every \(i\), summing over player \(i\)'s sampled action in (3) leaves
exactly the opponents' product law. Hence

\[
G_{x,\varepsilon}(u,b).b_i=
\begin{cases}
Q_i(x_{-i}),&\varepsilon_i=\mathrm Q,\\
C_i(x_{-i};b_i),&\varepsilon_i=\mathrm C.
\end{cases}
\tag{5}
\]

Equation (2) gives the prescribed-payoff prefix recursion. Therefore a
selector satisfying (1) gives the branch identity

\[
T_x(z)=G_{x,\varepsilon}(z).
\tag{6}
\]

The pure outcome \(\omega\) is one coupled sample used in every coordinate.
The cap coordinates still describe different forced-action counterfactuals,
so this is not one jointly realized deviation history.

## 2. Finite reset band

Let \(\mathcal M\) be the finite monoid of all reset modes: every semantic
coordinate is either unchanged or reset to one of finitely many reward
constants. It contains the maps \(E_{\varepsilon,\omega}\) and the identity.
For \(n=|I|\),

\[
|\mathcal M|\le (2^n)^{n+1}=2^{n(n+1)}.
\tag{7}
\]

This is \(2^{20}=1{,}048{,}576\) for four players. Every one-step transition
has at most \(2^n\) successors before equal modes are merged.

Write multiplication as outer composition, \(mn=m\circ n\). A later outer
reset overwrites an earlier label, while an outer identity retains it. Thus

\[
m^2=m,\qquad mnm=mn.
\tag{8}
\]

The mode monoid is a finite left-regular band. If
\(\operatorname{supp}(m)\) records the payoff block and cap coordinates reset
by \(m\), then

\[
\operatorname{supp}(mn)=
\operatorname{supp}(m)\cup\operatorname{supp}(n).
\tag{9}
\]

Consequently transitions are upper triangular by the \(2^{n+1}\) reset-
support strata.

## 3. Exact law-level semiconjugacy

Fix an initial semantic state \(z_0\), and set \(v_m=m(z_0)\). For a
probability law \(\mu\) on \(\mathcal M\), define

\[
\Pi_{z_0}(\mu)=\sum_{m\in\mathcal M}\mu_m v_m.
\tag{10}
\]

For a root \(x\) and one global selector \(\varepsilon\), define

\[
P_{x,\varepsilon}(m,m')=
\sum_{\omega:E_{\varepsilon,\omega}\circ m=m'}p_x(\omega).
\tag{11}
\]

This is a stochastic matrix. Since each \(E_{\varepsilon,\omega}\) is affine
and \(\mu\) has total mass one,

\[
\begin{aligned}
\Pi_{z_0}(\mu P_{x,\varepsilon})
&=\sum_{m,\omega}\mu_m p_x(\omega)
  (E_{\varepsilon,\omega}\circ m)(z_0)\\
&=\sum_\omega p_x(\omega)E_{\varepsilon,\omega}
  \left(\sum_m\mu_m m(z_0)\right)\\
&=G_{x,\varepsilon}(\Pi_{z_0}(\mu)).
\end{aligned}
\tag{12}
\]

If \(\varepsilon\) is maximizing at \(\Pi_{z_0}(\mu)\), (6) gives

\[
\Pi_{z_0}(\mu P_{x,\varepsilon})
=T_x(\Pi_{z_0}(\mu)).
\tag{13}
\]

Starting from the point mass at the identity and iterating (13) reproduces
every finite semantic chronology exactly. One selector is chosen from the
projected semantic state, not separately for each mode.

## 4. Exact observables and tail dependence

Total semantic debt is linear on the law:

\[
D(\Pi_{z_0}(\mu))=
\sum_m\mu_m D(m(z_0)).
\tag{14}
\]

Individual mode values need not be attainable semantic states and can have
negative debt.

The mass of modes whose payoff block is still the identity after roots
\(x_1,\ldots,x_k\) is

\[
\prod_{t=1}^k\Pr_{x_t}[\text{all players Continue}].
\tag{15}
\]

More generally, use the same lifted law with two anchors \(z_0,z_0'\). For
any scalar semantic coordinate \(a\),

\[
\Pi_{z_0}(\mu)_a-\Pi_{z_0'}(\mu)_a
=\mu\{m:m\text{ leaves }a\text{ unchanged}\}
  (z_{0,a}-z_{0,a}').
\tag{16}
\]

For payoff coordinates, the coefficient is (15). For cap coordinate \(i\)
under a fixed selector chronology, it is exactly

\[
\prod_{t=1}^k
\mathbf 1_{\{\varepsilon_{t,i}=\mathrm C\}}
\prod_{j\ne i}(1-q_j^t).
\tag{17}
\]

A single forced-Quit selection for \(i\) therefore kills all dependence on
the tail cap coordinate.

## 5. What the invariant polytope does and does not give

The convex hull

\[
\mathcal P(z_0)=
\operatorname{conv}\{m(z_0):m\in\mathcal M\}
\tag{18}
\]

is bounded, contains \(z_0\), and is invariant under every semantic root
map: represent a point by a law, choose a maximizing selector at its
projection, and apply (13). If both the reward table and \(z_0\) are
rational, then (18) is a rational polytope.

This polytope is only a neutral ambient carrier. It generally contains
negative-debt vertices, so it supplies neither a positive debt floor nor the
positive barrier required by the semialgebraic barrier question.

For fixed \(\varepsilon\), transition entries are polynomial in the root
probabilities; selector consistency is polynomial and affine in the lifted
law; debt and the identity masses are linear. Thus finite chronology search
becomes a finite-dimensional semialgebraic controlled system without false
coordinatewise recombination.

The lift does not prove, from \(D_*>0\), that the selector-consistent reachable
part of this law space admits a rational semialgebraic positive-debt invariant,
or that another finite certificate is forced by \(D_*>0\).

## Reproducible evidence

The exact-rational regression is documented in
[`Experiments/joint_reset_law`](../Experiments/joint_reset_law/README.md).
It checks the branch/law equality, the debt and identity-mass observables,
the tail coefficients, and the left-regular-band laws on bounded instances.
It is evidence for the formulas, not a proof of them.

## Lean surface

The integrated Lean module:

1. defines the finite joint reset modes and their stochastic transition;
2. proves their identity, associative composition, left-regular-band, and
   reset-support-union laws;
3. proves the branch identity against `quittingTerminalSemanticPrefix`;
4. proves the law-level semiconjugacy (12)--(13);
5. proves debt linearity, the arbitrary-law payoff/cap anchor-sensitivity
   identity (16), and the iterated products (15)--(17); and
6. is reachable from the production diagnostics umbrella.

The finite mode and transition laws use `FinDist`. The sole conversion of the
PMF-valued quitting root uses the opt-in finite-carrier bridge at this concrete
consumer; countably supported stopping laws are not converted to `FinDist`.

The finite representation does not imply a positive debt barrier.
