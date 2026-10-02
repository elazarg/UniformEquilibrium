# Review of nested terminal cap-child transport

Reviewer: `CODEX_HAHN`

Reviewed file:
`notes/CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT.md`

Reviewed SHA-256:
`3527a50e8278b0b186c671eec5dc594f6b6df96cd4ff79c06cdc363167c50672`

## Verdict

**PASS.** I independently reconstructed the literal child recursion, the
fixed-observer behavioral-deviation transport, the cap-clock reset/shift
classification, and the outsider root-gap identity. I found no mathematical
or provenance objection. The note correctly stops before claiming an exact or
summably approximate Nash--Bellman spine.

## Literal genealogy and fixed debtor

Replacing player `b` in `tau^(n+1) = q^n :: tau^n` by the deterministic
deadline `n+1` forces `b` to Continue at the new root and leaves deadline `n`
in the old suffix. Hence

```
zeta^(n+1) = bar(q^n) :: zeta^n
```

is an equality of actual profiles, not a semantic rebasing. Its joint
Continue probability is the product of the outsider Continue probabilities
and is at least the original joint Continue probability.

If a deviation of one outsider `j` is copied at every newly prefixed root and
used only after joint Continue to the fixed suffix, the prescribed and
deviating profiles have exactly the same distribution on every earlier
absorbing history. Their payoff difference is therefore multiplied by the
literal joint-survival product. The positive infinite product gives the
claimed uniform lower bound. Since `b` has zero debt in every cap child, the
terminal gap at one finite child indeed selects an outsider, and the same
actual deviation supplies that fixed outsider's debt floor at all later
children.

This argument covers complete behavioral deviations. It does not silently
replace them by stationary or one-stage responses.

## Exact cap-clock recursion

Because `b` Quits surely by date `n`, an outsider's pure stopping times after
`n` are outcome-equivalent to Never. The complete response maximum is thus
attained in the finite set `0,...,n,Never`. At the newly prefixed root its
dynamic program has exactly two branches: Quit now, or Continue and use a cap
in the old child. A maximizing time can consequently be chosen recursively as
`0` or `T_(n,j)+1`. The last-reset coordinate therefore stays fixed on a
shift and jumps to the current depth on a reset, giving the stated exhaustive
classification. This is a monotone clock descriptor, not a decreasing rank.

## Outsider Nash seam

For outsider `i`, subtracting the old Quit-minus-Continue comparison from the
new one gives exactly

```
(bar Q_i - Q_i) - (bar H_i - H_i)
  - bar s_(n,i) * Delta_i^n
  - (bar s_(n,i) - s_(n,i)) * U_i^n.
```

The terms caused solely by deleting `b`'s current hazard are bounded by a
constant times `M h_(n,b)` and are summable. The tail-payoff term is not:
`bar s_(n,i)` tends to one, while positive far-end reach permits
`Delta_i^n` to remain order one. Thus exact Bellman nesting of the children
does not imply root Nash for outsiders and does not meet a chronological
consumer's hypotheses.

## Scope

The frozen source SHA matches the note's citation. The punishment-floor split
uses independently re-solved exact tails and supplies no identification with
this child genealogy. The note makes no unsupported return, renewal, or
finite-clock-semantic claim.

## Delta audit

I also checked the repaired note at SHA-256
`6d813418986400654a0c93fd8e54469b9d965fd61fdefee848cf7c9803c9e956`.
It adds the finite cap-attainment argument before selecting gain at least
`Gamma`, weakens “is not summable” to the correct “need not be summable,” and
names the permanent-Never subcase of the cap-clock classification. These are
faithful repairs and introduce no new objection. **PASS** at the repaired SHA.
