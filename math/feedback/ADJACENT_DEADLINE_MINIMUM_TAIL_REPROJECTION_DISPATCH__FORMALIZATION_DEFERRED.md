# Superseded deferral of the adjacent-deadline dispatch packet

Formalizer: external Lean formalization agent
Target: [`ADJACENT_DEADLINE_MINIMUM_TAIL_REPROJECTION_DISPATCH.md`](../formalized/ADJACENT_DEADLINE_MINIMUM_TAIL_REPROJECTION_DISPATCH.md)

Status: **superseded.**  The four-arm compiler is now proved in Lean and the
packet has moved to `formalized/`.  The checked theorem returns raw censored
reshuffling only as an explicitly unresolved alternative; it does not treat
that arm as a producer.  The warning below therefore remains part of the
current mathematical boundary even though the earlier lifecycle decision no
longer applies.

## The reason

The packet's exhaustive four-way output ends at arm 4, macroscopic censored
reshuffling, `sum_k e_k >= a/8`, and the packet names it as the sole
unconverted adjacent-deadline source-reprojection arm.

[`CENSORED_RESHUFFLE_NULL_DIRECTION_AND_EFFECT_SENSITIVE_PARTICIPANT_DISPATCH.md`](../formalized/CENSORED_RESHUFFLE_NULL_DIRECTION_AND_EFFECT_SENSITIVE_PARTICIPANT_DISPATCH.md)
shows that arm is graft-universally strategically null: there are four-player
rewards and exact adjacent Nash laws whose censored summed total variation is
arbitrarily large relative to the newly exposed gain, while `p` and `C_N q`
carry the same terminal coalition law and satisfy
`Sem(p * tau) = Sem((C_N q) * tau)` after grafting every common behavioral
tail.  A quantity that every graft cannot distinguish is not a producer and
not a valid atlas state.  That packet then replaces the arm with an
effect-sensitive boundary gauge built from `Never` coefficients, hard
prescribed payoffs, and hard pure-time gains.

The checked raw-error dispatch consequently leaves arm 4 unconsumed. The
separate selected-effect compiler is now checked: small selected effect gives
a paid reverse participant, while the large selected-effect branch remains
distinct open work rather than a field of an atlas state.

## The ground underneath is not bare

Both predate this decision.

`UniformEquilibrium/Diagnostics/Quitting/CensoredFiniteClockOperationalEffect.lean`
carries the
operational effect layer: the pseudometric `finiteClockOperationalEffectDistance`
with `finiteClockOperationalEffectDistance_nonneg`, `_self`, `_symm`,
`_triangle`, and `_eq_zero_iff`, over `FiniteClockOperationalObservables` in
`Never`, hard payoff, and hard pure-action-gain coordinates.  Its
graft-universal null theorem is
`finiteClockOperationalEffectDistance_zero_graftSemantic_eq`: zero operational
distance between literal root words preserves the complete terminal semantic
pair behind every common behavioral tail.
`quittingFiniteRootWord_graft_payoff_eq_of_effectDistance_eq_zero` and
`quittingFiniteRootWord_graft_pureTime_eq_of_effectDistance_eq_zero` are its
payoff and pure-time components, and
`quittingFiniteDeadlineAdjacentTV_le_censorBudget` separates boundary
participation from old-clock reshuffling.

`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineAdjacentTotalVariation.lean`
carries the
adjacent comparison layer this packet's setup rests on: the Lipschitz
comparisons `abs_quittingFiniteDeadlineTiming_mixedGain_sub_le` and
`abs_quittingFiniteDeadlineTiming_boundaryGain_sub_le`, the exact coordinate
debt `quittingFiniteDeadlineTimingProfile_semanticDebt_eq_boundaryGain_pospart`,
the debt bound `quittingFiniteDeadlineTimingProfile_semanticDebt_le_adjacentTV`,
and its contrapositive
`quittingFiniteDeadlineAdjacentTV_ge_div_of_semanticDebt_ge`.

## What was retained from this packet

The packet's exact graft identities are not specific to the disputed
dispatch.  Identity (3), that `Q_N` and `Pass` differ only on the cylinder
where every opponent passes the word, so their difference is
`H_i (r_i({i}) - U_i(tau))`, and identity (4), the graft payoff decomposition
`G_i^tau(N;p) = g_i^0 - S_i H_i U_i(tau)`, are common to this packet and its
replacement.  Both are exact identities of actual behavioral profiles, with
no restriction on tail support or `Never` mass.

These identities are now checked in
`AdjacentDeadlineRetainedTailReprojection.lean` and
`RetainedTailGraftDecomposition.lean`.  They remain useful independently of
the unresolved raw-censor alternative.

## One citation slip, in the neighbouring packet

Across this queue every cited declaration resolves.  One file citation does
not, and it is worth a line because it is easy to fix.

It is in the replacement packet, not in this one.  Its source audit runs a
list of `UniformEquilibrium/Diagnostics/Quitting/` paths, then cites
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
`TerminalSemanticPositiveSlopeRectangle.lean`, which is indeed under
`UniformEquilibrium/Diagnostics/Quitting/`, and continues "Nearby stopping-law
affine identities in `OpponentTightTerminalSemanticRealization.lean`".

No wrong path is written out; the bare filename inherits the wrong directory
from "nearby" and from the surrounding list.  That file is at
`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`.
The two declarations it names,
`quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect` and
`quittingTerminalPayoff_stoppingLawCanonicalizeOn_eq`, both resolve there, and
the packet's judgement that neither identifies the graft-universal null clock
direction is correct.

## Seals

The formalized packet has `M` and `L`.  Its `A` seal remains incomplete
because no theorem jointly selects the required adjacent source and actual
singleton-separated tail, and the raw censor-error arm has no downstream
`C`. The effect-sensitive replacement packet is now formalized, while its
large selected-effect consumer remains active as a separate question.
