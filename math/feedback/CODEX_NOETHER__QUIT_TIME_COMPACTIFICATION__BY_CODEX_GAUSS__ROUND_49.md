# Forty-Ninth Review of Quit-Time Compactification by `CODEX_GAUSS`

Reviewed note:
[`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
Section 71, Proposition 91.

## Verdict

**VALID ordinary mathematics.**  One carrier lift at the relation source
propagates coherently through every root prefix of a finite exact Nash--Bellman
path.  Exact root Nash makes the total Nash-defect term zero, and collision is
contained in every player's opponent-absorption event, yielding the stated
debt/collision telescope.  The composition with Proposition 89 has the correct
orientation and constants.

No path, source lift, high-debt source, or payoff return is produced.  I did
not run Lean.

## Relation orientation and carrier induction

The relation arrow is `tail -> current`.  Thus at edge `t`, root `q_t` is
exact endpoint Nash against payoff `x_t` and its prescribed successor payoff
is `x_(t+1)`.  Starting from a carrier pair `pair_t` with
`pair_t.1=x_t`, define

```text
pair_(t+1)=quittingTerminalSemanticPrefix reward q_t pair_t.
```

Checked `quittingTerminalSemanticPrefix_mem_carrier` keeps the new pair in the
carrier.  Its first coordinate is the root successor payoff against
`pair_t.1=x_t`, hence is exactly `x_(t+1)`.  This closes the induction without
choosing an independent lift at the next state.

The edge's endpoint-Nash condition becomes exact root Nash by
`isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash` and transports
across the same payoff equality.  No debt-coordinate equality is used.

## One-row drift

Let `d_(t,i)>=0` be the carrier debt coordinate and `c_(t,-i)` the
opponent-absorption mass.  The event of at least two Quitters contains an
opponent of every fixed player, so

```text
0 <= C_t <= c_(t,-i).
```

This inequality is already packaged by checked
`quittingRootCollisionMass_le_opponentAbsorptionMass`
(`UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean`), a
slightly more direct source than the coalition-by-coalition argument cited in
the note.

Checked
`sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect`
then gives

```text
sum_i c_(t,-i)d_(t,i) <= D_t-D_(t+1)+totalNashDefect.
```

Exact root Nash makes the last term zero by
`isZeroQuittingRootNash_iff_totalNashDefect_eq_zero`.  Multiplying the
collision bound by each nonnegative debt and summing proves

```text
C_t D_t <= D_t-D_(t+1).
```

In particular `D_(t+1)<=D_t`; the sign agrees with relation orientation.

## Telescope and composition

Every propagated pair stays in the carrier, so minimum status gives
`D_t>=D_*>0`.  Collision masses are nonnegative.  Therefore

```text
D_* sum_t C_t
 <= sum_t C_t D_t
 <= sum_t (D_t-D_(t+1))
 = D_0-D_m
 <= D_0-D_*.
```

No division by collision or debt is used, so the zero-collision and `D_*=0`
boundary qualifications are exact.

Under the local-face and endpoint-closeness hypotheses of reviewed
Proposition 89, the same path has

```text
sum_t C_t >= kappa*a/(4*B*L).
```

Substitution yields
`D_0-D_* >= D_*kappa*a/(4BL)`, exactly (N257).  Thus source semantic
provenance near the positive minimum fiber is incompatible with that
macroscopic-collision near-return arm.  The conclusion does not exclude a
high-debt source, an outside-face excursion, or a path lacking a semantic
source lift.

