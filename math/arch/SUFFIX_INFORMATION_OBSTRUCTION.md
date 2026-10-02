# Suffix information obstructions

This file records two exact limitations on a recursive state for quitting
games.  The first is informational: complete current unilateral payoff-response
data can forget chronology.  The second is topological: retaining all
calendar-indexed suffix probes with one common continuity modulus is
incompatible with compactness.

## 1. A probe table

Let \(I=\{1,2,3,4\}\). For every nonempty \(S\subseteq I\), define

\[
r^\star(S)
=
\left(1,\mathbf 1_{\{2,3\}\subseteq S},0,0\right),
\]

and give the all-Never outcome payoff \(0\). For a behavioral profile
\(\sigma\), let \(x_i^n\) be player \(i\)'s Quit probability at the live
history at date \(n\), and let \(S_n\sigma\) be the literal suffix after \(n\)
all-Continue outcomes. Let \(Q_3^0\) make player \(3\) Quit surely at the
first date of that suffix.

Then

\[
U_2\bigl((S_n\sigma)[3\leftarrow Q_3^0]\bigr)=x_2^n.
\tag{1}
\]

Player \(3\) forces immediate absorption, and player \(2\) receives one
exactly when player \(2\) Quits at the same root. Thus the family of ordered
operations

\[
\text{suffix at }n\quad\text{then}\quad(3\leftarrow Q_3^0)
\]

observes the complete calendar hazard stream of player \(2\).

## 2. Current payoff-response laws do not determine a suffix

Let \(a\in(0,1)\). Define two profiles in which players \(2,3,4\) always
Continue and player \(1\) has one Quit hazard of size \(a\): at date \(0\) in
\(\sigma\), and at date \(1\) in \(\rho\).

For a profile \(z\), let

\[
\mathfrak R(z)
=
\left(
\operatorname{LawPay}(z),
\bigl(\operatorname{LawPay}(z[i\leftarrow\tau_i])\bigr)_{i,\tau_i}
\right),
\tag{2}
\]

where \(\operatorname{LawPay}\) is the law of the terminal payoff vector and
\(\tau_i\) ranges over every behavioral replacement, including Never and
arbitrarily late stopping.

Every absorbing outcome reachable from either profile after at most one
replacement has payoff vector

\[
e_1=(1,0,0,0).
\]

If player \(1\) is replaced, the original clock disappears. If another
player is replaced, at most one of players \(2,3\) can be active, so the
second payoff coordinate remains zero.  Writing \(\alpha(\tau_i)\) for the
replacement's eventual Quit probability along the all-Continue path, the
probability of Never is \((1-a)(1-\alpha(\tau_i))\) on both sides.  Hence

\[
\mathfrak R(\sigma)=\mathfrak R(\rho).
\tag{3}
\]

After one all-Continue outcome, however,

\[
U(S_1\sigma)=0,
\qquad
U(S_1\rho)=a e_1.
\tag{4}
\]

The suffix history has reach probabilities \(1-a\) and \(1\), respectively.
This is therefore a positive-reach collision, not an off-path artifact.

### Collision theorem

There is no state map \(\Phi=f\circ\mathfrak R\) satisfying all three
properties:

1. \(\Phi\) determines prescribed terminal payoff, or its payoff law;
2. the labelled operation “take the literal one-step suffix” has an exact
   state successor depending only on \(\Phi\); and
3. that successor is the state of the actual literal suffix.

Indeed, equation (3) forces equal successor states, payoff observability
forces equal successor payoffs, and equation (4) contradicts this. The
payoff-observability
assumption is essential: a constant state is a congruent but strategically
useless quotient.

This theorem concerns payoff-vector response laws.  It does not identify the
richer labelled terminal-coalition response laws used in the counterfactual
hierarchy of `MARKOV_COMPLETE.md`.

## 3. No compact state with one all-depth suffix modulus

The topological obstruction can be stated without choosing a particular
encoding. Let \(X\) be a metric state space and let \(\Phi\) map actual
profiles into \(X\). Suppose there is a function

\[
\omega(\delta)\longrightarrow0
\qquad(\delta\downarrow0)
\]

such that, for every pair of profiles and every date \(n\),

\[
\left|
U_2\bigl((S_n\sigma)[3\leftarrow Q_3^0]\bigr)
-
U_2\bigl((S_n\rho)[3\leftarrow Q_3^0]\bigr)
\right|
\le
\omega\bigl(d_X(\Phi(\sigma),\Phi(\rho))\bigr).
\tag{5}
\]

The same labelled suffix depth is used on both sides, and the modulus is
independent of \(n\).

Fix \(p\in(0,1)\). For every \(m\ge0\), let \(\sigma^m\) have the single
hazard

\[
x_2^m=p
\]

and let every other hazard be zero.  Every finite live history has reach at
least \(1-p\). By equation (1), for \(m\ne\ell\), the probe at depth \(m\)
differs by \(p\). Choose \(\delta>0\) so that \(d<\delta\) implies
\(\omega(d)<p\).  Equation (5) gives

\[
d_X\bigl(\Phi(\sigma^m),\Phi(\sigma^\ell)\bigr)\ge\delta.
\tag{6}
\]

Thus the image of the actual profiles contains an infinite uniformly
separated family.  It is not totally bounded and, in a metric space, cannot
have sequentially compact closure.

### Uniform-suffix compactness theorem

For the bounded four-player table \(r^\star\), no sequentially compact metric
state can satisfy the all-depth estimate (5). This remains true when the
tested suffix histories have reach uniformly bounded below.

The theorem assumes labelled program semantics and a depth-independent
modulus.  It does not rule out a modulus for each fixed depth or each fixed
finite family of programs.

## 4. Finite global approximation also fails

For \(N\ge1\) and \(a\in\{0,1\}^N\), let player \(2\) have hazards

\[
x_2^t=p a_t\quad(0\le t<N)
\]

and zero hazards afterward; all other players always Continue.  Any two
different words differ at a coordinate detected by equation (1), so their state images
are \(\delta\)-separated under (5).  Hence every global strategic net of
radius strictly smaller than \(\delta/2\) contains at least \(2^N\) points
for every \(N\), which is impossible for a finite net.

This conclusion concerns one finite set intended to approximate every state
uniformly over all suffix probes.  It does not contradict per-profile
rational finite-clock approximation.

## 5. Exact boundary

The obstruction is the familiar topology tradeoff:

- quotienting away calendar chronology can be compact but loses suffix
  congruence;
- the full hazard stream in the product topology is compact, and every fixed
  suffix is continuous, but the family of all suffixes is not equicontinuous;
- a supremum-type topology makes all suffixes uniformly stable, but isolated
  late spikes destroy compactness.

Consequently an exact state supporting the probe programs must determine, at
least implicitly, the necessary observable

\[
\left(
U_2\bigl((S_n\sigma)[3\leftarrow Q_3^0]\bigr)
\right)_{n\ge0}.
\]

This is an information lower bound, not a proof that this scalar tower is a
complete or minimal state.
