# Common-response potential consumer for same-stage monodromy

Author: CODEX_ROOT, preserving the mathematical proposal in
../THE_MISSING.md

## Current status

The consumer theorem below is proved as ordinary finite mathematics. It is
conditional on a source-matched common-response field which the current Fin4
producer atlas does not produce. It therefore does not eliminate the
common-host or complementary-pair leaves of the exported six-leaf atlas.

Mathematical audit:
[THE_MISSING__BY_CODEX_ROOT.md](../feedback/THE_MISSING__BY_CODEX_ROOT.md).

## Question

Fix a finite player set \(I\), a quitting reward table, a literal behavioral
profile \(\sigma\), and one reached date \(t\). For every nonsingleton
coalition \(S\), let \(P_S\) be the profile obtained by replacing only the root
at date \(t\) by the pure root with quitting coalition \(S\). Thus all
\(P_S\) have the same literal past and the same complete tail after \(t\).

Can a fixed pair of responses turn the positive same-stage endpoint edges into
a well-founded source-native dynamics?

## Conditional theorem

Fix one observer \(o\) and two behavioral strategies \(Q_o^-,Q_o^+\). Define

\[
\Phi(S)
=
U_o(P_S[o\leftarrow Q_o^+])
-
U_o(P_S[o\leftarrow Q_o^-]).
\]

Suppose every selected nonsingleton endpoint carry \(S\to T\) satisfies

\[
0<c_{S,T}\le \Phi(T)-\Phi(S).
\tag{1}
\]

Assume also the ordinary same-stage dispatch data:

- every current \(P_S\) carries the same positive stage-mass floor
  \(\lambda\);
- the shifted tail is independent of \(S\);
- from every nonsingleton \(S\), the dispatch returns either a literal
  mass-retaining singleton or a literal nonsingleton endpoint carry
  \(S\to T\); and
- a carry changes only the date-\(t\) root and does not decrease the marked
  mass.

Then a finite sequence of literal carries reaches a singleton packet.

### Proof by exclusion of circulation

On a closed cycle

\[
S_0\to S_1\to\cdots\to S_K=S_0
\]

equation (1) gives

\[
0<\sum_{k<K}c_{S_k,S_{k+1}}
\le
\sum_{k<K}\bigl(\Phi(S_{k+1})-\Phi(S_k)\bigr)
=0,
\]

a contradiction. Hence no selected endpoint orbit satisfying (1) can close
inside the nonsingleton state space.

### Natural-valued rank

Let

\[
\mathcal N_I=\{R\subseteq I:|R|\ge2\}
\]

and define

\[
\rho(S)
=
\#\{R\in\mathcal N_I:\Phi(S)\le\Phi(R)\}.
\]

If \(S\to T\), then \(\Phi(S)<\Phi(T)\). Therefore the upper-level set at
\(T\) is a proper subset of the upper-level set at \(S\), and

\[
\rho(T)<\rho(S).
\]

Strong induction on \(\rho\) gives the same finite singleton conclusion. For
Fin4, \(|\mathcal N_I|=11\), so at most ten nonsingleton carries occur.

### Source preservation

This is a genuine source-native rank once (1) is supplied. The target is the
literal profile \(P_T\), not a carrier representative. All carries preserve:

- the past before \(t\);
- the complete continuation after \(t\);
- the common response strategies;
- the positive stage-mass floor; and
- the exact mover-debt subtraction and actual payoff-gain data already carried
  by the same-stage endpoint edge.

Support entry and debt circulation do not affect \(\rho\).

## Missing producer

The Fin4 producer atlas stores on each monodromy edge:

- a literal profile and fixed date;
- the current and next nonsingleton coalitions;
- the endpoint mover and best action;
- a fixed positive payoff-gain floor;
- exact mover-debt subtraction; and
- a routed mass floor and common tail.

It does not store one observer and one fixed pair \(Q_o^-,Q_o^+\) satisfying
(1) on every edge.

The existing common-response rectangle machinery supplies a fixed response
pair on its own four literal corners. Those corners are not identified with
all vertices and edges of the independently selected atlas orbit. Producing
that dependent attachment is exactly the remaining nonlocal theorem.

Thus the valid implication is

\[
\boxed{
\text{atlas monodromy plus a source-matched common-response gradient}
\Longrightarrow
\text{a concentrated singleton packet}.
}
\]

The unconditional implication from atlas monodromy alone is not proved.

## Lean-facing target

A useful formal interface would define the scalar potential and its finite
upper-level rank, then prove:

1. strict potential increase implies strict rank decrease;
2. a dispatched closed segment with strict potential increase on every edge
   is impossible; and
3. a same-stage dispatch equipped with the common-response field reaches a
   singleton by strong induction.

These are finite supplied-object consumers. The separate, conjecture-facing
producer must attach such a field to an arbitrary common-host or
complementary-pair atlas leaf.

## Nonclaims

This note does not:

- produce the common response field;
- identify a response rectangle with an atlas orbit;
- turn horizontal endpoint updates into a temporal chronology;
- yield terminal approximate Nash profiles; or
- eliminate either monodromy leaf unconditionally.
