# Independent review of Section 18 in `CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY`

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS, with no mathematical repair.**  The leave-or-join split, the two
label-exclusion arguments, the literal `Fin 4` completion, and the checked
stationary-handoff constructor all match exactly.  Corollary 18.2 correctly
consumes Cedar Proposition 6's pair-premium alternative into either the
existing two-debtor paid-source handoff or one full-gap pair-to-triple join.

I do **not** recommend a conjecture-facing export on this result alone.  It is
a valid finite semantic narrowing, but the stationary handoff still returns
to the maintained paid-row obligation, while the triple-join chamber is
static.  Thus Section 18 neither constructs a payoff near-return nor strictly
decreases the paid branch's carrier debt/support obstruction.

## Pair toggle and exclusion of the premium recipient

Apply
`QuittingTerminalExploitabilityWitness.exists_leave_or_join_gain` to
`S={k,i}`.  Its member arm has the orientation

```text
r(S)_m+Gamma <= r(S.erase m)_m,
```

and its outsider arm has the orientation

```text
r(S)_j+Gamma <= r(insert j S)_j.
```

The latter is exactly `(18.3)`.  In the former, `m=i` would give

```text
r({k,i})_i+Gamma <= r({k})_i,
```

which contradicts

```text
r({k})_i+kappa <= r({k,i})_i
```

because both `Gamma` and `kappa` are positive.  Hence `m=k`, and erasing
`k` gives `(18.6)` with precisely the displayed direction.

## Atomic collision and the third label

Punishment normality of `i` is exactly the hypothesis of

```text
witness.exists_atomicCollision_gain_of_normal i
```

from `PunishmentNormalAtomicCollision.lean`.  It returns `t!=i` and

```text
r({i})_t+Gamma <= r({i,t})_t.
```

If `t=k`, this inequality and `(18.6)` are opposite strict gap inequalities
on the same `k` coordinate:

```text
r({k,i})_k+Gamma <= r({i})_k,
r({i})_k+Gamma   <= r({k,i})_k.
```

They imply `2 Gamma<=0`, contradicting `Gamma>0`.  Therefore `t` is distinct
from both `k` and `i`.  On literal `Fin 4`, the complement of `{k,i,t}` has
one member `o`; the four labels are pairwise distinct.  No hidden reindexing
or extra cardinality hypothesis is needed.

## Checked constructor and provenance

The declaration

```text
nonempty_finFourLeaveJoinStationaryTwoDebtorHandoff
```

takes, in order, a leaver, sure spectator, joiner, and fourth label.  The
substitution

```text
leaver=k, spectator=i, joiner=t, fourth=o
```

turns its two hypotheses exactly into `(18.6)` and `(18.7)`.  Its remaining
hypotheses are precisely pairwise distinctness, `M>=0`, and the supplied
uniform reward bound.  The same `witness` is passed throughout, so both
toggle gaps are the same `Gamma`; no gap reselection occurs.

The constructor's output retains an executable stationary profile, a
pair-or-triple atom, two coordinates with prescribed payoff equal to the
unrestricted behavioral cap and above punishment, positive debt supported
on at most the two remaining labels, and a literal paid first-disagreement
row.  The all-behavior claims use sure first-row absorption and are fields of
the checked handoff, not a stationary-regret substitution.

## Corollary 18.2 and scope

Cedar Proposition 6's premium arm says, with its owner `k` and blocker `i`,

```text
r({k,i})_i-r({k})_i >= g_a/2 > 0.
```

Thus Theorem 18.1 applies literally with `kappa=g_a/2`.  Combining it with
Proposition 6's other arm gives the stated three outputs: one-coordinate
exact repayment, full-gap pair-to-triple join, or the stationary two-debtor
handoff.

The note correctly does not identify the pair premium with collision
probability, does not turn the triple join into a Bellman edge, and does not
claim that the stationary paid source returns in payoff.  The sentence that
the third arm is “accepted by an unrestricted-deviation semantic consumer”
should be read only as saying that the checked handoff supplies its exact
all-behavior semantic fields; it is not yet consumed into a uniform payoff.

