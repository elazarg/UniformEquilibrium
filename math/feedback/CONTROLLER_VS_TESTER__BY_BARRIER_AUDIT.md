# Adversarial audit of the Bellman and barrier duality

## Claim reviewed

This review checks Section 6 of `meta/CONTROLLER_VS_TESTER.md`: the
finite-word value function, its Bellman equation and upper semicontinuity, the
maximal barrier dual, the target-free invariant-set formula, the assertion
that the terminal-semantic carrier is the smallest closed invariant set, and
the decoding of a positive barrier into an executable behavioral
exploitability gap.

The relevant checked source facts are:

- `continuous_quittingTerminalSemanticPrefix` and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`;
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

## Verdict

The mathematical core of Section 6 is correct. I found no counterexample to
the Bellman equation, upper-semicontinuous barrier duality, or invariant-set
formula. The carrier really is the smallest closed forward-invariant set
containing the Never boundary, conditional only on the finite-word density
proved earlier in the note; that density is also already a checked theorem.

Two points should be stated more precisely.

1. The transfer of a function barrier from finite words to an arbitrary
   behavioral profile uses upper semicontinuity together with semantic
   convergence of the finite Never-tail truncations. Monotonicity alone covers
   only finite words.
2. A certified floor \(\Gamma>0\) produces an actual behavioral
   exploitability gap at every \(0<\gamma<\Gamma\). It need not produce an
   actual deviation attaining gain exactly \(\Gamma\). The choice
   \(\gamma=\Gamma/2\) in the document is valid but not strongest.

The canonical carrier and value functions are generally non-effective
certificates. Their existence proves logical completeness of the barrier
language, not that a semialgebraic or piecewise-polynomial certificate can be
found.

## 1. Bellman equation

Let

\[
Q_v(z)=\inf_{w\in X^{<\omega}}\ell_v(T_wz),
\]

with the empty word included. Split the finite words into the empty word and
the nonempty words, and decompose a nonempty word at its root adjacent to
\(z\). This gives exactly

\[
Q_v(z)=\min\left\{\ell_v(z),\inf_{x\in X}Q_v(T_xz)\right\}.
\]

No minimizing row or minimizing finite word is asserted or needed. In
particular, the inner expression should remain `inf`, not `min`: an
upper-semicontinuous function on a compact set need not attain its minimum.

The same decomposition shows

\[
Q_v(z)\le \ell_v(z),
\qquad
Q_v(z)\le Q_v(T_xz)
\quad(x\in X).
\]

The orientation is correct: attaching a prescribed root restricts the set of
future finite-word choices appearing in the infimum.

## 2. Upper semicontinuity

For every fixed finite word \(w\), the map

\[
z\longmapsto \ell_v(T_wz)
\]

is continuous. The prefix maps are continuous, and finite composition
preserves continuity. An arbitrary pointwise infimum of continuous functions
is upper semicontinuous, because

\[
\{z:Q_v(z)<a\}
=
\bigcup_{w\in X^{<\omega}}
\{z:\ell_v(T_wz)<a\}
\]

is open. The indexing family may be uncountable; this argument still applies.
Thus the document has the semicontinuity direction right. It should not be
strengthened to continuity or lower semicontinuity without additional data.

The same argument proves that the target-free function

\[
q_r^*(z)=\inf_w d(T_wz)
\]

is bounded and upper semicontinuous.

## 3. Maximal function-barrier duality

Suppose \(q\) is bounded and upper semicontinuous and satisfies

\[
q\le \ell_v,
\qquad
q\le q\circ T_x\quad\text{for every }x.
\]

Iteration gives

\[
q(z)\le q(T_wz)\le \ell_v(T_wz)
\]

for every finite word. Hence \(q(z)\le Q_v(z)\). Conversely, the previous
sections show that \(Q_v\) itself satisfies all these conditions. Therefore

\[
W_r(v)=Q_v(e_\infty)
=
\max_q q(e_\infty),
\]

and \(Q_v\) is the pointwise greatest feasible barrier, not merely one
optimizer.

There is an equally exact target-free version that is useful to state:

\[
\eta(r)
=
\max_q q(e_\infty),
\]

where \(q\) ranges over bounded upper-semicontinuous functions satisfying

\[
q\le d,
\qquad
q\le q\circ T_x\quad\text{for every }x.
\]

Its canonical greatest optimizer is \(q_r^*\).

## 4. Smallest invariant carrier and the set dual

Let

\[
\mathcal O=\{T_we_\infty:w\in X^{<\omega}\}.
\]

The earlier finite-word density result says

\[
\mathcal K_r=\overline{\mathcal O}.
\]

Continuity of every \(T_x\) shows that \(\mathcal K_r\) is forward invariant.
If a closed set \(C\) contains \(e_\infty\) and satisfies
\(T_x(C)\subseteq C\) for all \(x\), induction gives
\(\mathcal O\subseteq C\), and closedness gives
\(\mathcal K_r\subseteq C\). Thus \(\mathcal K_r\) is exactly the smallest
closed forward-invariant set containing the Never boundary.

It follows that every feasible pair \((\gamma,C)\) in the proposed set dual
satisfies

\[
\gamma\le \min_{z\in C}d(z)
\le \min_{z\in\mathcal K_r}d(z)
=\eta(r).
\]

Conversely \((\gamma,C)=(\eta(r),\mathcal K_r)\) is feasible. Hence the
displayed supremum is actually a maximum. The precise attainment statement is
that the pair \((\eta(r),\mathcal K_r)\) attains it, rather than that the set
alone attains a scalar supremum.

Allowing invariant sets outside the semantic carrier causes no problem:
minimality forces every such closed invariant set containing \(e_\infty\) to
contain the whole carrier.

## 5. Transfer to arbitrary behavioral profiles

For a closed invariant-set certificate the transfer is immediate from
\(\mathcal K_r\subseteq C\).

For a function barrier, let \(z_m=T_{w_m}e_\infty\) be finite Never-tail
truncations converging to the semantic pair \(z_\sigma\) of an arbitrary
behavioral profile. Monotonicity gives

\[
q(e_\infty)\le q(z_m).
\]

Upper semicontinuity gives

\[
q(e_\infty)
\le \limsup_m q(z_m)
\le q(z_\sigma)
\le d(z_\sigma).
\]

This is the exact reason for putting upper semicontinuity, rather than lower
semicontinuity, into the dual class.

## 6. Strongest positive-gap decoder

Suppose either certificate proves

\[
d(U(\sigma),B(\sigma))
=\max_i(B_i(\sigma)-U_i(\sigma))
\ge\Gamma>0
\]

for every behavioral profile \(\sigma\). Finiteness of the player set selects
one player \(i\) whose debt is at least \(\Gamma\). For every
\(0<\gamma<\Gamma\), the definition of the supremum \(B_i(\sigma)\) supplies
an actual complete behavioral replacement with gain at least \(\gamma\).
This includes Never and arbitrarily late stopping.

Thus the strongest unconditional decoder is

\[
\boxed{
\Gamma>0
\quad\Longrightarrow\quad
\text{every }0<\gamma<\Gamma
\text{ is a terminal exploitability gap}.}
\]

One cannot in general replace \(\gamma<\Gamma\) by \(\gamma=\Gamma\), because
the behavioral best-response supremum need not be attained. The document's
choice \(\Gamma/2\) is therefore sound.

## 7. Scope

The result is an exact semantic reformulation and a logically complete
certificate language. It does not decide the sign of \(\eta(r)\), construct a
positive certificate, or synthesize a controller for four-player tables. The
canonical witnesses \(Q_v\), \(q_r^*\), and \(\mathcal K_r\) encode the value
itself and can be as difficult to describe as the original problem.

For a semialgebraic set or piecewise-polynomial barrier, the obligations are
first-order real-algebraic after splitting the finitely many max branches.
One must additionally verify all region-boundary conditions needed for upper
semicontinuity of a piecewise definition. This gives a sound exact-checking
route, not an automatic finite certificate theorem.
