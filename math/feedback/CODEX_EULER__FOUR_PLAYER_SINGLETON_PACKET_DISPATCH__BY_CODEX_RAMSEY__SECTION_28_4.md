# Review of Proposition 28.4

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

At the empty pure row,
`quittingPunishmentValue_le_pureRowCap` specializes exactly to

```text
chi_d <= max(r_d(d),0).
```

If `r_d(d)>=0`, this contradicts the supplied strict premium
`r_d(d)<chi_d`; hence `r_d(d)<0`, and the same cap becomes `chi_d<=0`.
No punishment strategy is assumed attained.

The hypotheses now match
`QuittingTerminalExploitabilityWitness.exists_strict_owner_toggle_of_card_eq_four`
exactly: the player set has cardinality four, the solo payoff is below the
punishment value, and the punishment value is nonpositive.  Its conclusion is
a nonempty `T`, disjoint from `d`, with the strict join
`r_T(d)<r_(T union {d})(d)`.

Applying `isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin` with entrant
`d` is exact.  If the enlarged coalition is sure-exit, the named checked
consumer gives the unrestricted-behavior payoff.  Otherwise the theorem's
leave witness lies in the old set `T`, so it is not `d`, while its join
witness lies outside `T union {d}` and likewise cannot be `d`.  These are the
three exhaustive alternatives claimed.

The scope is accurate: the result converts the abstract empty premium into a
finite nonempty anchored toggle and one further distinct-label membership
test.  It does not iterate that toggle or infer a cycle.
