# Review of the pure-clock minimum-hit rank attack

Reviewer: `CODEX_DESCENDANT`

Verdict: **PASS with two bounded wording repairs**.

The positive-calendar support argument is correct, the date-zero residual is
real, and the note correctly refuses to treat either the checked monodromy
no-go or an off-minimum exit as a renewable minimum rank.

## Positive-calendar rank

For a canonical pure-clock cap response the only new clock is zero, Never, or
the first finite opponent deadline, which is already occupied.  Hence the set
of occupied strictly positive dates cannot grow.  The checked minimum descent
has the same property: its erasures use Never, and its singleton-owner response
uses Never or an already occupied later opponent deadline.

After the first coalition has been erased to a singleton at a positive date,
an equality-arm response removes the unique owner of that date.  The positive
date therefore disappears and cannot be reintroduced by any later operation
in this lane.  Thus the strict decrease of the finite rank

\[
 |\{m>0:\exists i,\ t_i=m\}|
\]

is valid and renewable as long as recursion stays in the canonical
response/minimum-descent lane.  The note correctly keeps an off-minimum exit
outside that ranked recursion rather than resetting the rank.

## Date-zero reduction

The first insertion of date zero cannot itself be a positive minimum hit.  At
such a target the mover receives its singleton payoff and, because the move is
an exact cap response against unchanged opponents, has zero target debt.  The
positive minimum singleton margin would then say simultaneously

\[
 B_i-r_i(\{i\})=0
 \quad\text{and}\quad
 B_i-r_i(\{i\})\ge D_*>0.
\]

If at least two players already quit at date zero, replacing every later
clock by Never leaves the prescribed outcome unchanged.  It also leaves every
full behavioral cap unchanged: after deleting any one deviator, at least one
of the other sure date-zero quitters remains.  The screened pure-coalition
profile is therefore the same semantic minimum and has empty positive-date
support.

For a singleton date-zero minimum, the checked singleton-margin proof makes
the owner debt equal the entire total debt; all outsider debts are therefore
zero.  The exact owner response is at the next occupied opponent deadline or
Never.  Equality deletes date zero; strictness exits to the off-minimum port.
This validates the exhaustive reduction in Section 7.

## Coalition formula and monodromy boundary

At a screened coalition with at least two sure date-zero quitters, the debt
formula (5.1) is exact.  A unilateral strategy can only join the coalition at
zero or pass it; later behavior is screened by another sure quitter.  The
resulting strict endpoint dynamics is a horizontal membership-toggle process.

The checked Fin4 monodromy theorem does not consume this process wholesale.
Its dispatched closed segment declares a cardinality-two coalition terminal
through an uncharged singleton route and requires all in-period vertices to be
nonterminal.  A pure response orbit may visit a pair, and continuing after
that route requires a new horizontal response whose profitability is not
provided by the terminal route.  The note's refusal to infer a contradiction
or chronology is therefore correct.

## Required edits

1. Replace the sentence “every cap-attaining response is clock zero or Never”
   in Section 5 by “every response value is represented by clock zero or
   Never, and a canonical cap attainer may be chosen there.”  Any positive
   finite clock is payoff-equivalent to Never behind a sure date-zero quitter,
   so the literal universal statement about *every* attainer is false.  The
   debt formula and canonical toggle dynamics are unaffected.

2. Repair the TeX transcription in Section 4:
   `B_p(M)=B_p(A),qquad` should be `B_p(M)=B_p(A),\qquad`.

These are nonstructural.  The final conclusion remains exactly:

\[
 \text{positive-calendar rank drop}
 \quad\lor\quad
 \text{attained date-zero pure-coalition minimum}
 \quad\lor\quad
 \text{off-minimum paid port}.
\]

Only the first is a renewable rank; the other two remain genuine consumers to
be supplied.
