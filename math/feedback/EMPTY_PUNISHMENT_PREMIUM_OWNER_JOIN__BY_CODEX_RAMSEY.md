# Export-gate review: Empty punishment premium forces an owner join

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

I checked the packet against every mandatory item in
[`exports/README.md`](../exports/README.md).  No repair or removal is
recommended.

## Exact source-to-toggle proof

At the empty opponent row,
`quittingPunishmentValue_le_pureRowCap` specializes exactly to

```text
chi_d <= max(s_d,0).
```

The strict premium `s_d<chi_d` rules out `s_d>=0`; hence `s_d<0`, and the
same cap gives `chi_d<=0`.  This uses only the scalar punishment value and
does not assume an attaining opponent profile.

Those signs, the terminal exploitability witness, and cardinality four are
precisely the hypotheses of
`QuittingTerminalExploitabilityWitness.exists_strict_owner_toggle_of_card_eq_four`.
Its conclusion is the claimed nonempty opponent coalition `T`, disjoint from
`d`, with `d`'s strict join.

The call to
`isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin` is then exact.  Its
leave witness belongs to the old set `T`, so it is not the entrant `d`; its
join witness lies outside `T union {d}`, so it is likewise not `d`.  The
three alternatives are exhaustive.  In the sure-exit arm, the named checked
consumer supplies the unrestricted-behavior payoff; the finite toggle lemma
itself is not overstated as an all-timing result.

## Source, novelty, and boundary audits

The actual source is exactly the empty premium left by the accepted
`REPAIRED_RESIDUAL_PURE_EXIT_DESCENT` packet, ultimately on the checked
four-player semantic-dispatch branch.  The new adapter is not a restatement
of `ThreeRoleSpectator.lean`: that file supplies the owner-toggle theorem only
after receiving `s_d<chi_d` and `chi_d<=0`; this packet proves the second
hypothesis automatically from the accepted empty premium and immediately
passes the output through anchored sure-exit promotion.

The boundary tests are correct.  The zero table shows strictness is needed.
In the sharp negative example, Never guarantees player `d` zero against
every opponent profile because all coalitions excluding `d` pay it zero,
while the all-Continue row has cap `max(-1,0)=0`; hence `chi_d=0>s_d=-1` even
though one joined coalition pays one.  Changing only other players' reward
coordinates realizes the sure-exit, old-member-leave, and outsider-join
promotion arms without changing the premium or anchored join.

The seven possible coalitions are exactly the nonempty subsets of the other
three players.  No randomization, correlation, bounded controller, or
punishment-strategy selection is introduced.

## Gate conclusion

This is a strict finite narrowing accepted by
`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`: it eliminates the sole
noncoalitional empty-premium residual in favor of a checked all-behavior
output or explicit finite reward-table toggles.  The Lean handoff identifies
the exact simplification, declaration hypotheses, promotion, and consumer,
without storing the target as an input.  The nonclaims are complete: no
toggle iteration, cycle, chronology, or result beyond the exact four-player
terminal-witness branch is asserted.
