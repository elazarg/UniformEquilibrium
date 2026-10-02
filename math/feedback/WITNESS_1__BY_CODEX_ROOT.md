# Review of `WITNESS_1.md`

Reviewer: `CODEX_ROOT`  
Date: 2026-08-30

## Verdict

The explicit rational algebra is correct, but the advertised behavioral Zeno
chronology is not.  The packet therefore fails the export gate in its present
form.  Its strongest surviving content is a useful internal regression: an
exact outward cap-prefix tower converging to a cap whose only exact product
root is all Continue.

This verdict agrees with the independent reviews
`WITNESS_1__BY_CODEX_ADVERSARY.md` and
`WITNESS_1__BY_CODEX_STRENGTHEN.md`.

## Exact calculations that survive

For the displayed matrices, exact rational calculation gives

\[
\det C=17,\qquad M\mathbf 1=\mathbf 1,\qquad
C\mathbf 1=-2\mathbf 1.
\]

Thus, for \(x=\mathbf 1/4\),

\[
Mx=x,\qquad Cx=-2x,
\qquad C^{-1}(M+C)x=\tfrac12x.
\]

The reward formula also gives the asserted endpoint and cap-prefix identities

\[
G_i(q,b)=(Cq)_i-b_i\prod_{k\ne i}(1-q_k)
\]

and

\[
F_i(s+b,q)-s_i=
\Bigl(\prod_k(1-q_k)\Bigr)b_i+(Mq)_i+q_i(Cq)_i.
\]

Consequently the uniform root \(q_i(a)=a/4\) is an exact fully mixed root
against the *supplied* cap \(V(a)=s+b(a)\mathbf 1\), and

\[
\operatorname{Prefix}_{q(a)}V(a)=s-\frac a4\mathbf 1.
\]

The proof that all Continue is the unique exact product root at the limiting
cap \(s\) is also correct.  With at least two active coordinates,
\(q^TCq<0\) contradicts exact complementarity; with exactly one active
coordinate, its designated collider strictly wants to join.

## Fatal orientation error

Let \(a^+\) solve the packet's recurrence.  The verified identities imply

\[
\boxed{V(a^+)=\operatorname{Prefix}_{q(a)}V(a)},
\qquad a^+<a/2.
\]

This is outward prefix construction.  A finite executable block has roots in
the chronological order

\[
q(a_{N-1}),q(a_{N-2}),\ldots,q(a_0),
\]

and increasing \(N\) prepends a new, smaller root.  It does not append a next
date to one fixed behavioral profile.  Reversing the recurrence makes the
parameter grow by more than a factor two and leaves the stated interval after
finitely many steps.  The coordinatewise limit of the growing finite words is
therefore all Continue at every fixed chronological date: the nonzero clock
escapes to temporal infinity.

Accordingly, the packet has not constructed one infinite forward exact
Nash--Bellman chronology, let alone a behavioral Zeno profile.

## Independent missing semantic data

The construction supplies roots and declared caps only.  It does not supply

- prescribed payoff coordinates;
- actual behavioral tail profiles;
- membership in the terminal-semantic carrier;
- terminal or deleted-player laws; or
- a source-attached minimum or positive atom.

Thus it does not build a terminal-semantic source even at a finite level.
Supplying finite carrier realizations would still leave the outward-prefix
orientation problem; extension-compatible realization of all finite blocks
would be a separate theorem.

## Generic pencil claim

The source-conditional algebraic reduction survives with narrower wording.
Eventual strict positivity of every finite current hazard makes the finite
complementarity slack zero, hence the omega work is zero coordinatewise.  If
\(C\) is invertible, the invariant cone then contains a nonzero
\(x\ge0\) and an \(r\) in the stated compact interval with

\[
(M+rC)x=0.
\]

The vector may lie on a proper face and may be a conic average rather than an
actual source state.  This is normalized algebra, not face descent or an
absolute chronological lift.  Much of the interior conclusion overlaps the
existing weighted-cocycle reduction; the useful extra observation is the
zero-work conclusion under eventual finite full support.

## Recommended retained statement

The note can be corrected and retained internally as two claims:

1. eventual finite full support upgrades the normalized omega relation to
   exact work equality and yields a nonnegative stable pencil mode when
   \(C\) is invertible;
2. the rational quadratic table realizes a strictly positive stable mode by
   exact one-stage roots and an exact summable **outward cap-prefix tower**,
   converging to a cap with unique all Continue.

It must not call the tower a forward chronology, a behavioral Zeno orbit, a
source producer, or a counterexample mechanism.  Without an actual-data
adapter or consumer it remains below the export boundary.
