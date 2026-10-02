# Export-gate review: Repaired residual pure-exit descent

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

I independently checked the full packet against every mandatory item in
[`exports/README.md`](../exports/README.md).  No repair or removal is
recommended.

## Exact weighted descents

The only averaging input is `W_he>=0`, `sum W_he=H>0`.  Hence a positive
weighted sum of either `k_d^he` or the oriented `y` gain has a
positive-weight cell at least as large as the normalized average.  This gives
the displayed inequalities `H*k>=K_d` and `H*g>=G_y`; zero-weight cells are
correctly excluded.

In the owner branch, `T=empty` gives exactly
`chi_d-r_d(d)>=K_d/H`, with no fictitious empty terminal reward and no assumed
attainment of the punishment value.  For nonempty `T`, the same inequality is
exactly `d`'s strict outsider no-join margin.  Testing every member and every
other outsider is exhaustive.  If all tests pass they are precisely
`IsQuittingSureExitSet reward T`; if not, the failing label cannot be `d`, so
(9) is the exact finite negation.

In the endpoint branch, both orientations are correct.  When `j=0`, `y`
joins `O_he` and has no-leave margin `Delta_y^he`; when `j=1`, it leaves and
has no-join margin `-Delta_y^he`.  The preferred coalition remains nonempty
because `d` is always in `O_he`.  After fixing `y`'s strict test, the other
membership inequalities either give an exact sure-exit set or yield exactly
the distinct-label residual (13).  Singleton erasure is handled by
`hat_r_empty=0`.

## Source, probability, and consumer audits

The actual-data source is the accepted
`PAID_SIGN_FAILURE_BINARY_REEQUILIBRATION` output, through the earlier pure
paid-leave adapter.  Its `W/H` are ordinary independent product-root
probabilities, but the theorem needs only their finite weighted-average
properties; it introduces no correlated randomization or sampled cell during
play.

The extracted coalitions are deterministic pure exit sets.  The only
unrestricted-strategy conclusion comes from the named checked
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` consumer,
which tests every player's two membership actions and covers arbitrary
behavioral timing and Never.  The packet does not mistake the finite
extraction for that all-behavior theorem.

The checked anchored-join theorem covers the joining orientation, while the
direct membership argument correctly supplies the leaving orientation.  The
weighted extraction, empty punishment arm, and quantitative stable-label
margins are not duplicated by those declarations.

## Boundary, narrowing, and Lean handoff

The boundary tests realize the empty premium, a positive sure-exit case, a
failed outsider toggle, and both `y` orientations.  They also correctly show
why positive cell weight is necessary and why equality at zero belongs to no
strict arm.

This is a strict finite narrowing accepted by
`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`: both residual signs of
the preceding accepted repaired-root packet become either a checked
all-behavior output, one exact empty punishment premium, or a nonempty pure
coalition with a quantitative stable label and a different-label literal
toggle.

The Lean handoff gives the required weighted-selection lemma, exact
empty/nonempty and join/leave case splits, decidable sure-exit test, named
consumer, and false-branch witnesses without storing the target conclusions
as hypotheses.  The nonclaims are complete: no toggle iteration, cycle,
chronology, general stationary compiler, or consumption of the remaining
premium/mixed chambers is asserted.
