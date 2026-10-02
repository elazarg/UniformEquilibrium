# Source audit of `PAID_CUP_1.md`

Reviewer: `GATE_SOURCE`

## Verdict

**PASS as an ordinary-mathematics strengthening of the paired unique-cap
branch, with one unformalized cross-law calculation.**  The active-zero-debt
lifting lemma and its qualitative debt-descent/solo-gate consequence are
correct.  Applied after the checked double-unique-cap alternative, they refine
that final branch to prescribed-payoff root games.  They do not consume the
branch or supply a renewable regenerated source, and the note states that
limitation honestly.

Equation (9) is also correct, but the required repaired-law transport is not a
field of the current chain and has no named theorem in the inspected sources.
It must be proved from the two literal stationary roots before it can be used
in Lean.

## Exact source correspondence

For the original singleton source,
`FinFourSingletonBaseSameLawResetProducer` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseSameLawResetProducer.lean`
supplies exactly:

- `free_solved`, giving zero unrestricted debt on every free coordinate;
- `owner_gap`, giving positive owner debt;
- `positiveDebtSupport_eq`, identifying the positive-debt support with the
  singleton owner;
- `paid_row`, `target_joint`, `reset_incidence`, and `dispatch`.

For the literal repair,
`FinFourSingletonBaseResetRepairPaidChain` and
`QuittingSingletonBaseStationaryHandoff` in
`SingletonBaseResetRepairPaidChain.lean` and
`LargeBaseStationarySemanticHandoff.lean` supply:

- `repairedProfile_eq_ownerAlwaysContinueUpdate`;
- `repaired_owner_payoff_eq_source_cap`;
- `repaired_owner_cap_eq_payoff`;
- `outside_debt` and `paid_row` for one free player distinct from the owner.

Thus the identities

```text
b_source(owner) = u_repaired(owner) = b_repaired(owner)
```

and zero repaired-owner debt are genuine.  The latter is already exposed as
`repairedOwner_debt_eq_zero` in
`Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean`.

The cap hypothesis in the intended final arm is exactly
`HasUniqueAllContinueAtCap` on both actual sources, returned by
`sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique`.
It concerns roots against the two unrestricted cap vectors, not against the
prescribed payoff vectors.

## Root-game calculation

For a semantic pair `p = (u,b)` with coordinate debts `d_i = b_i-u_i`, the
displayed identity

```text
Delta_i(b,x) = Delta_i(u,x) - s_i(x) d_i
```

has the correct sign: replacing `u_i` by `b_i` raises the Continue endpoint by
the opponents' all-Continue probability times `d_i`.

If every player with positive Quit probability has zero debt, the support
conditions for a root exact against `u` therefore remain valid against `b`.
For a pure-Continue player the endpoint difference can only decrease.  Hence
double cap uniqueness implies that every non-all-Continue exact root against
the corresponding prescribed payoff activates a positive-debt player.

The subsequent coordinate estimate is the existing generic theorem
`quittingTerminalSemanticDebt_prefix_le` from
`TerminalSemanticEqualityStratum.lean`: for a root exact against `pair.1`,
each prefixed debt is at most opponent survival times the old debt.  Therefore
a second positive debtor, or a second active quitter when the debtor is
unique, makes total debt strictly decrease.  Equality can survive only on the
unique-debtor solo face.  Root existence then gives the three-way alternative
in (7), and applying it successively to the source and repaired pairs gives
(8).

This is an actual semantic-prefix debt descent because both input pairs are
attained.  It is not a paid/reset regeneration: the prefix need not retain the
reset incidence, fixed-law dispatch, or paid-row provenance required by the
maximal one-step regeneration theorem.  The note correctly does not claim
that stronger conclusion.

## Law transport and equation (9)

Let `c` be the one-stage probability that every free player Continues.  The
source root has the singleton owner Quit surely, so its law is the one-stage
free-player product law:

```text
nu_source({owner}) = c,
nu_source(Q union {owner}) = w(Q)       for nonempty Q.
```

The repaired owner always Continues and the free root is repeated
stationarily.  `free_absorption_lower` and positivity of the terminal gap give
`1-c > 0`, so repaired absorption is almost sure and

```text
nu_repaired(Q) = w(Q)/(1-c).
```

This proves the claimed transport

```text
nu_source(Q union {owner}) = (1-c) nu_repaired(Q).
```

Combining it with
`b_source(owner)=u_repaired(owner)=u_source(owner)+d_source(owner)` yields
equation (9) exactly.

However, `SingletonBaseResetRepairPaidChain.lean` explicitly retains no
repaired-law alignment, and no named law-transport declaration was found.
Formalization therefore needs a new stationary outcome-law lemma (including
the `1-c>0` proof); equation (9) cannot currently be obtained by projecting a
stored chain field.

## Novelty and overlap

- `quittingTerminalSemantic_minimum_stratum_alternative` already gives the
  all-Continue/unique-debtor solo-face alternative **at a global minimum**.
  It does not cover these off-minimum attained pairs.
- `quittingTerminalSemanticDebt_prefix_le` and
  `quittingTerminalSemanticDebtSum_prefix_le_one_sub_opponentAbsorption_mul`
  already contain the debt-contraction algebra.
- `capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt` and
  `isZeroQuittingRootNash_at_prescribed_of_capNash_of_killedDebt` in
  `PairBasePaidResetEndpointSeam.lean` treat the opposite conversion direction
  (cap root to prescribed-payoff root).  They do not duplicate the
  active-zero-debt lifting lemma here.
- No existing declaration found in the inspected tree packages the paired
  prescribed-payoff alternative (8) or the cross-law identity (9).

The genuinely new formalizable packet is therefore small and precise:
active-zero-debt payoff-to-cap root lifting, the off-minimum
strict-descent/solo-gate corollary, its double-port adapter, and the stationary
cross-law identity.  None is yet a terminal consumer for the paired unique-cap
question.
