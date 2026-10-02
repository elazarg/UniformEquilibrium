# Review of two-sure-clock universal descendant theorem

Reviewer: `CODEX_SPINOZA`

Reviewed artifact:
`notes/CODEX_HAHN__TWO_SURE_CLOCK_CHILD_IS_UNIVERSAL_PREFIX_DESCENDANT.md`

Exact SHA-256:
`8296721fcfad9e373c012b01481ae414ef0f7c0cda86f7a1868a46ec563f82ad`

## Verdict

**PASS.**  Two distinct prescribed finite sure-clock players make the full
terminal semantic value of their finite literal word independent of the
tail, including every unrestricted behavioral cap coordinate.  Consequently
a deterministic finite-clock cap child is exactly a universal-prefix
descendant of its actual parent, and the stated barrier monotonicity and
summability follow with the correct orientation.  The note correctly stops
short of controlling exact-block capacity recharge.

## Tail-independence audit

Prescribed play absorbs by the common deadline.  Under a unilateral
replacement by one of the two clock owners, the other owner's sure clock
remains; under replacement by any outsider, both remain.  Thus every
complete deviation profile also absorbs by the deadline.  Its payoff is
therefore independent of the continuation tail before taking the supremum,
so taking the supremum over the identical unrestricted behavioral class
preserves equality.  This proves both the payoff and cap halves of Theorem
1.1; no finite-deviation reduction is hidden.

Replacing one player by a deterministic finite clock preserves two distinct
sure-clock labels: either both old clocks remain or the changed owner's old
clock is replaced by its new finite clock while the other label remains.
The child's literal word therefore computes its semantic pair over every
tail.  Substituting the parent's semantic pair gives exactly

\[
 \operatorname{Sem}(\tau)=T_w\operatorname{Sem}(\sigma),
\]

not merely an equality of prescribed payoffs.  Prefixing an actual source by
a finite exact block only shifts the two old deadlines, so the same argument
is available at the subsequent horizontal update.

## Barrier and series audit

For `Q(z)=inf_u d(T_u z)`, fixing a prefix restricts the words available
after evaluation and hence gives `Q(z) <= Q(T_w z)`.  Applying this first to
the exact vertical word and then to the finite cap-child word yields

\[
 Q(s_m)\le Q(p_m)\le Q(s_{m+1}).
\]

All displayed increments are nonnegative.  Their finite partial sums
collapse to `Q(s_N)-Q(s_0)` (up to the final interleaving convention), so
boundedness of `Q` proves the two series in (5) are summable and each
increment tends to zero.

This still gives no estimate of
`Phi(s_(m+1))-Phi(p_m)` in terms of the barrier increment.  In particular,
flat `Q` is compatible with the proved statements, so the packet does not
silently promote the horizontal word to an exact Nash--Bellman edge or claim
a capacity consumer.  The exclusions of Never responses and of the
one-sure-clock case are necessary and correctly stated.

