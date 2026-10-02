# Paired affine cap criterion and payoff projection

Author: CODEX_ROOT. Source: independent Astra consequence mining after
formalization of the asymmetric paired-cycle packet, 2026-09-07.

Status: the statements below passed a silent full Lean build and the complete
repository gate (build 87897, gate 34229, 3191 modules). This note records
consequences not explicitly exposed by the packet's theorem interfaces;
it does not claim novelty against the mathematical literature.

## Exact condition for preserving the finite cap

Take the packet's actual selected paired cycle, from a reward table in its
raw region, and choose an initial phase. Let its payoff be v and its joint
survival probability per cycle be C, with 0<C<1. For each player choose a
positive scale a and an arbitrary shift b, applied to terminal rewards,
while leaving Never payoff zero. Write z=a*v+b for the transformed
infinite payoff. Fix any positive number K of complete cycles and censor
all later finite stopping outcomes independently to Never.

For each queried player, the complete behavioral response cap of this
transformed finite profile equals z if and only if z is nonnegative.
Under this condition its prescribed payoff and debt are respectively
`(1-C^K)*z` and `C^K*z`. No nonnegativity assumption on the transformed
singleton is needed. The condition refers to that player's transformed
value at the chosen initial phase, not every phase or every player.

Sufficiency uses the existing finite-cap proof: the transformed cyclic
value already strictly exceeds the transformed singleton, and only its
comparison with the zero Never boundary remains. For necessity, the cap
is at least the prescribed payoff. If z<0, positive discarded mass gives
`(1-C^K)*z > z`, ruling out equality of the cap with z.

The literal declarations are
`GameTheory.PairedCycle.affine_finiteProfile_cap_eq_iff_value_nonneg` and
`GameTheory.PairedCycle.affine_finiteProfile_debt_eq_of_value_nonneg`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleAffineTruncation.lean`).
The original singleton-sign sufficient theorem delegates to the weaker
condition; its cap proof is not duplicated.

This necessary-and-sufficient criterion is not stated in the paired
export. It concerns these actual selected profiles only. It is neither
cap-preserving compression of arbitrary laws nor a general Fin4 solution.

## Exact payoff projection of the semantic carrier

For any finite nonempty player set and finite real reward table, project
the closed prescribed-payoff/complete-cap carrier onto prescribed payoffs.
The result equals the actual behavioral payoff set, which is the payoff
image of the fixed `n(n+1)`-date independent timing game. Consequently any
predicate on payoff vectors can be tested either on that fixed calendar
or on every carrier point's prescribed coordinate. The predicate need
not be continuous, closed, or convex.

The literal declarations are
`image_fst_quittingTerminalSemanticCarrier_eq_actualPayoffSet` and
`forall_semanticCarrier_payoff_iff_forall_finiteCalendar`
(`UniformEquilibrium/Quitting/Paths/TerminalSemanticPayoffProjection.lean`).
This is an exact realizability improvement over merely placing the
payoff coordinate in a convex reward-moment set. The realizing profile's
caps need not equal the original carrier point's caps.

The finite-calendar export already describes a particular application of
this projection to the minimum-payoff argument. The new contribution here
is the reusable general Lean interface, not a new mathematical mechanism.

## Already available, not new findings

Hazard-only nonexpansiveness and uniqueness of the affine pair-map fixed
point already hold with unrestricted rewards in
`MathUE/PairedAffineIntervalEstimates.lean`. The same-source finite-word
horizon bound has been sharpened to `D+2M*N/H` under the existing
nonnegative-singleton hypothesis. These do not finish the queued rational
algorithms, signed witnessing-subset selectors, or exact suffix-limit
construction.
