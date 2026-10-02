# Review of nested terminal cap-child transport

Reviewer: `CODEX_GROMOV`

Frozen input SHA-256:
`3527a50e8278b0b186c671eec5dc594f6b6df96cd4ff79c06cdc363167c50672`

## Verdict

**PASS, with two non-substantive wording repairs.**  The literal nesting,
fixed-observer transport, uniform debt floor, and outsider cap-clock recursion
are mathematically valid under the stated Section 10 input.  The note also
draws the correct boundary: the child sequence is an exact Bellman chain but
not an exact or known summably approximate Nash--Bellman chain, because the
outsider root gaps contain an uncontrolled cross-coordinate tail-payoff term.

## Checks

### Literal nesting

The identity

\[
 \zeta^{n+1}=\bar q^n::\zeta^n
\]

is literal.  In `tau^(n+1) = q^n :: tau^n`, replacing the owner's deterministic
clock `n+1` forces that owner to Continue at the new root and then installs the
clock `n` in the old tail.  All outsider marginals and all outsider tail
strategies remain unchanged.  No semantic limit or source substitution is
used.

### Killed owner and one fixed debtor

The clock `A^n` attains the owner's complete cap by the supplied escaping-cap
transport theorem.  Since changing one's own strategy does not change one's
best-response envelope, `d_b(zeta^n)=0` follows exactly.

At one fixed depth `R`, the terminal-gap debtor has label `j != b`.  Its cap is
attained because the owner surely stops by date `R`: against the fixed
opponents, all behavior after that date is irrelevant, so a best response is
among finitely many pure deadlines (with Never representing continued play
through the terminal owner clock).  Copying player `j`'s prescribed root
marginal through every newly prefixed root makes prescribed and deviating play
identical on every root-absorbing event.  Their payoff difference is therefore
multiplied exactly by the joint Continue probability.  This proves

\[
 d_j(\zeta^N)\ge
 \left(\prod_{n=R}^{N-1}\bar c_n\right)\Gamma
 \ge C_\infty\Gamma.
\]

Thus neither the debtor label nor its response is reselected with depth.

### Outsider cap-clock recursion

At `zeta^(n+1)`, an outsider's optimal first action is either Quit now or
Continue and use a cap response in `zeta^n`.  Hence a coherent maximizer may be
chosen with

\[
 T_{n+1,j}\in\{0,T_{n,j}+1\},
\]

including the convention `Never + 1 = Never`.  The last-reset coordinate is
constant under shifting and jumps to the newest depth under a Quit-now reset.
The stated eventual-shift versus infinitely-many-resets dichotomy is valid.

### Root-gap calculation

For `i != b`, subtracting the old Quit-minus-Continue endpoint gap from the
gap after forcing `b` to Continue gives exactly

\[
 (\bar Q_i-Q_i)-(\bar H_i-H_i)
 -\bar s_{n,i}(W_i^n-U_i^n)
 -(\bar s_{n,i}-s_{n,i})U_i^n.
\]

The first, second, and fourth terms are bounded by a reward-box constant times
`h_(n,b)` and are summable.  The third term need not decay: positive far-end
reach permits `W_i^n-U_i^n` to have an order-one limit.  This is enough to
justify the note's negative conclusion about Nash--Bellman exactness.

## Minor repairs

1. In Section 2, the sentence that the terminal gap "supplies" a deviation of
   gain at least `Gamma` should cite the finite cap-attainment argument from
   Section 3, or Section 3 should precede it.  A lower bound on a supremum would
   not alone imply literal attainment; sure termination by date `R` is what
   makes the claim exact here.
2. In Section 4, replace "The third term is not" by "The third term need not
   be" summable.  The hypotheses fail to control it, but special instances may
   still make it summable.

The permanent-Never case in the cap-clock dichotomy should also be understood
as an eventually shifted old maximizer; spelling this out would avoid reading
"fixed old cap" as necessarily a finite deadline.

## Scope audit

The note does not identify the forced-owner roots as Nash for outsiders,
transport the fixed debtor back to the original `tau^N`, manufacture a return,
or claim a decreasing cap-clock rank.  Those nonclaims are correct.  In
particular, literal nesting resolves ancestry and label coherence only; it
does not resolve the temporal compiler.
