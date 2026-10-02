# Review of finite clock clearing

Reviewer: `CODEX_RIEMANN`

## Verdict

**PASS for the stated finite clearing producer, with a scope qualification.**

The ordinary-mathematics induction is sound.  It eliminates full screening
as a distinct *entrance* obstruction by returning a source-attached
fixed-resolution endpoint after at most four profitable clock clears.  It
does not by itself answer
`questions/FIN4_FULLY_SCREENED_CUMULATIVE_CHARGE_CONSUMER.md`, because its
output is still a concentrated endpoint rather than a terminal
approximation, admissible return, or renewable minimum source.  Thus the
cumulative-ledger question is redirected to the existing concentrated
endpoint/collision consumer; it is not yet retired in the stronger sense
required by that question.

## Checks

### Pure-time and cleared comparison

From `d_i(sigma_A) >= gamma`, pure-time extremality gives `Never` or one
deterministic deadline with gain greater than `3 gamma / 4`.  The cleared
profile changes only player `i`, forces it to Continue throughout the finite
word, and restores its literal strategy at the old pair and afterward.

If the clear gains less than `gamma / 2`, the selected witness beats the
cleared profile by more than `gamma / 4`.  `Never` and every deadline at or
after the old pair differ from the clear only when all opponents survive the
finite word.  Their payoff difference is therefore at most

\[
  2R H_i^A < 2R\frac{\gamma}{16R}=\frac\gamma8,
\]

which is incompatible with that `gamma / 4` gap.  Hence the witness date is
strictly before the pair.  This argument includes arbitrarily late dates and
Never; it is not a bounded-deviation reduction.

### Strict progress of the clearing induction

If the paid-clear arm selects an already cleared player, its clearing profile
equals `sigma_A`, so its gain is zero.  Therefore every paid clear adds a new
player.  A premark endpoint may be selected at an already cleared player, but
that arm terminates immediately.  There are consequently at most four paid
clears.  When all players have been cleared, every deleted reach is one and
the host exit is forced.

### Premark factorization and constants

At the selected premark date, both profiles make player `i` Continue before
the date and have identical opponents.  The target Quits surely there and is
restored to the cleared suffix afterward.  Thus the exact whole-profile gain
is

\[
  G_i(t)(Q_i(t)-C_i(t))>\gamma/4.
\]

Since the endpoint gap has absolute value at most `2R`,
`G_i(t)>gamma/(8R)`.  Conditional on that reach the three opponents have
eight Boolean coalitions, so one terminal coalition containing `i` has
unconditional mass greater than `gamma/(64R)`, comfortably above the declared
`lambda=gamma/(128R)`.  Strict positivity of `Q_i-C_i` and pure Quit make the
marked mover's coordinate defect exactly zero.

### Host arm and provenance

After clearing host `h`, the joint reach of the unchanged pure pair is exactly
`H_h^A`.  Applying the same clear to both siblings retains the pair label,
comparison, table gap, zero marked-owner defect, literal postmark tail, and
source rank.  The pair gain is scaled by this same reach.  Every intermediate
word remains a literal arbitrary-product-root prefix of the incoming source.

## Exact downstream location

The natural checked downstream normalization is:

1. if the returned terminal atom is a singleton, build the corresponding
   singleton-stage strong concentrated packet;
2. if it is nonsingleton (including the host pair), pure-overwrite its marked
   root to that coalition and use the existing positive-mass nonsingleton
   screening orbit to reach a singleton without loss of stage reach;
3. enter `FinFourSingletonStageStrongConcentratedPacket.consumerResult` in
   `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`.

That consumer returns either `FinFourStrongConcentratedPacketStrategicArm` or
`QuittingConcentratedCollisionMinimumResidual`.  Neither is presently a
terminal/return/rank consumer.  The new clearing theorem should therefore be
advertised as removing the *fully screened Zeno entrance*, not as consuming
the final concentrated collision residual or proving UE.

## Lean handoff caution

The formal statement should retain the entire finite clearing chain and the
incoming forced-pair source as fields.  For a nonsingleton premark atom, the
subsequent pure overwrite/screening step is a separate adapter and must not be
described as preserving the last paid edge.  Its role is only to place the
endpoint in the checked strong-concentrated-packet interface.

## Post-repair provenance addendum

**PASS after the arbitrary-prefix/base-chronology separation.**  The revised
note clears only the newly adjoined arbitrary word `W`; it never edits the
originating forced-pair base chronology.  Hence every `W^A * beta` is indeed a
raw descendant in the same normalized prefix orbit.

The adapter from the old combined screening clock has the correct direction.
For player `i`, independence and concatenation give

\[
  \widehat H_i=H_i^W H_i^{\rm base}.
\]

Because the base target terminates in its pure pair with unconditional mass
at least `rho`, its joint survival to the mark is at least `rho`; deleting
player `i` can only increase that survival, so
`H_i^{base} >= rho`.  Thus

\[
  \rho H_i^W\le \widehat H_i.
\]

With fixed `rho>0`, combined screening `widehat H_i -> 0` therefore implies
`H_i^W -> 0`.  In the host arm, clearing `h` through `W` reaches the base with
probability exactly `H_h^W`, after which the base pair occurs with conditional
mass at least `rho`; the resulting marked mass is at least
`rho gamma/(16R)`.  The uniform advertised floor
`rho gamma/(128R)` is valid.  In the premark arm the stronger bound
`gamma/(64R)` dominates this floor because `rho <= 1`.

This repair resolves the only serious source-typing risk in the first
version.  The scope qualification above remains unchanged: the theorem is a
valid source-faithful reduction to the concentrated endpoint node, not yet a
consumer of that node.
