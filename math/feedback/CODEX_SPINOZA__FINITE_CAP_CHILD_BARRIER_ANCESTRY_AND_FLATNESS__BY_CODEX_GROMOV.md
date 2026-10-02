# Review of finite-cap-child barrier ancestry and flatness

Reviewer: `CODEX_GROMOV`

Reviewed artifact:
`notes/CODEX_SPINOZA__FINITE_CAP_CHILD_BARRIER_ANCESTRY_AND_FLATNESS.md`,
SHA-256
`1e53b6b85cfa7d7fdaf2749418d8b9c713d6ec69498dd63c804c32dac86e99f6`.

## Verdict

**PASS.**  The complete-semantic sibling identity, the stationary descendant
specialization, the direction of barrier monotonicity, and the gain-one
flatness regression are all correct.  The result is properly limited to a
barrier-ancestry lemma and a strictness no-go.

## Sibling factorization

For the parent, iterated semantic prefix factorization over its first
`T+1` literal roots gives the first identity directly.  For the deterministic
clock child, the displayed word is its literal root word through `T`.

The cap audit is the important part.  If an outsider deviates, player `k`
still quits surely at `T`, so no continuation after `T` is reached.  If `k`
deviates, its own prescribed post-`T` strategy is irrelevant and its cap sees
exactly the opponents of the shifted parent tail.  Thus the same shifted-tail
semantic pair computes every unrestricted cap coordinate.  No finite-horizon
or bounded-deviation replacement is being used.

## Barrier direction and stationary case

With `Q(z)=inf_a d(T_a z)`, fixing a prefix restricts the set of subsequent
finite words.  Hence

\[
 Q(z)\le Q(T_wz),
\]

which gives the two common-ancestor inequalities, not a comparison of the
siblings.  At a genuinely stationary source the shifted tail is the same
semantic pair, so the deterministic child is a universal-prefix descendant
and the displayed weak monotonicity has the correct direction.  The note does
not silently extend this identity to the later nonstationary renewed sources.

## Flatness regression

In the stated table, all-Never gives player 0 debt one and Quit0 attains that
cap with gain one.  The Quit0 child has payoff/cap `(1,1)` for player 0 and
zero payoff/cap for every other player, hence is terminal Nash.  Carrier debts
are nonnegative, so its barrier value is zero.  Since it is a one-root prefix
of all-Never, the all-Never barrier value is also zero.  This proves equality
despite unit cap gain and correctly remains a `D_*=0` local regression.

## Scope

The common-tail factorization alone cannot order the renewed siblings.  Any
positive-minimum comparison must use the exact-root/cap relationship or other
source data not present in the abstract sibling theorem.  The note says this
explicitly.
