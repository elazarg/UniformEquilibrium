# Feedback on Persistent Deleted-Clock Characterization, Round 2

Reviewer: `CODEX_NOETHER`

Reviewed note:
[`../notes/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md`](../notes/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md)

Scope: corrected Proposition 4 only, including its every-suffix conclusion and
the claimed correspondence with the diffuse-reprojection window interface.
This is an ordinary-mathematics and source audit, not a Lean check.

## Verdict

**Proposition 4 is VALID ordinary mathematics with the corrected same-label
qualification.**  One divergent marginal hazard stream for player `a` and a
divergent `a`-deleted absorption-charge stream force a second persistent label
by the finite union bound.  Proposition 1 then supplies every one-player-
deleted and joint suffix limit.  The existing diffuse-window interface has the
right survival weighting to supply raw deleted-charge quotas for its displayed
owner, but it does not align that owner with Proposition 3's atom mover or put
both quota families on one executable concatenated chronology.  The note now
states both deficits exactly.

## Abstract implication

For each date,

```text
c_(t,-a) <= sum_(j ne a) p_(t,j).
```

If every `j ne a` had summable marginal hazard, finiteness of the player set
would make the right side summable and hence make `c_(-a)` summable.  Therefore
divergence of the deleted charge selects some fixed `b ne a` with divergent
hazard.  The separate divergence of `p_a` makes `a,b` the two distinct
persistent labels required by reviewed Proposition 1.

Removing finitely many dates preserves both divergences.  Thus the conclusion
is not only date-zero joint absorption: for every start date and every deleted
player, the required survival tends to zero.  No uniform rate in the start
date and no pair-deleted limit is used.

The block formulation introduces no hidden weight.  On consecutive finite
blocks, divergence of `sum_k H^a_k` is exactly divergence of the raw `a`
hazard series, and divergence of `sum_k C^(-a)_k` is exactly divergence of the
raw `a`-deleted charge series.  Infinitely many alternating packet types with
one fixed positive quota on their respective occurrences suffice; the two
quotas need not occur in the same row.

## Exact source correspondence

The displayed finite-window mass in
`QuittingReprojectionDiffuseDeletedWindowPacket.deletedMassLower`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionDiffuseClockBridge.lean`)
is

```text
sum_t live(t) * quittingRootOpponentAbsorptionMass(root_t, owner).
```

Since every `live(t)` lies in `[0,1]`, a positive lower bound on that quantity
is indeed a lower bound on the unweighted block charge
`sum_t c_(t,-owner)`.  In the concentrated arm,
`QuittingReprojectionDiffuseWindowPacket.exists_concentrated_or_diffuseDeleted`
retains a fixed positive survival-weighted opponent atom on original profile
windows; it gives the same raw deleted-charge implication.  In the diffuse
arm, `deletedMassLower` gives it directly, while `clock_sum` and `clock_mesh`
describe the normalized clock rather than adding a different weight.

Two limitations are binding and correctly printed in the revised note.

1. The displayed owner of these deleted windows is naturally the
   vanishing-debt observer.  Proposition 3's divergent raw hazard belongs to
   the distinct atom mover.  Divergence of `c_(-observer)` may be caused
   entirely by that same mover, so these crossed facts can still describe
   only one persistent label.
2. Proposition 3 selects a high-hazard source or replacement stopping law,
   whereas the diffuse packet retains its own actual profile windows.  The
   checked interfaces neither identify those laws nor retain a fixed fraction
   of the selected mover hazard after source reprojection and concatenation.

Accordingly the source claim is an exact interface match only after one
supplies same-window, same-label alignment:

```text
divergent p_a and divergent c_(-a) on one reached chronology.
```

Proposition 4 then recovers the second label automatically.  It does not
itself produce that aligned chronology, the other forcing/debt fields, or a
uniform-equilibrium payoff.  No change to the existing Props1--2 export is
warranted by this still-internal strengthening.
