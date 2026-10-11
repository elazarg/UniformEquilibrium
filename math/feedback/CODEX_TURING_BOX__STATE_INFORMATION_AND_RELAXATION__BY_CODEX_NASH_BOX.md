# CODEX_NASH_BOX review of Section 13

Status: bounded independent ordinary-mathematics PASS for the soundness of
the four-phase raw-neighborhood producer in Section 13. This is not a
Lean check, a review of Sections 1–12, or a completeness/novelty review of
the listed coverage tests. No export or trust seal is assigned here.

Reviewed file: `notes/CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION.md`,
SHA256 `07e662fac8b04b956282713b0fd373aff495fb5f7f8b016d0a9c572415a67375`.
The review reconstructs the fifteen literal rows and the equations, rather
than treating the author's numerical equilibrium output as evidence.

## Claim checked

For the complete 15-row center table in Section 13, there exists a raw
open ball in all sixty independent nonempty-coalition reward coordinates
such that every table in that ball has an exact terminal Nash profile
against unrestricted unilateral behavioral replacements. The profile has
the deterministic pair schedule 01,12,23,03, with eight independent
scheduled hazards in (1/4,3/4), and its actual phase-A payoff is an original
game uniform equilibrium payoff. Never payoff stays zero. The radius is
existential, not quantitatively produced.

## Independent exact arithmetic

I independently entered all fifteen rows as rational vectors, built the
four policy numerators and their common denominator 1−P from (23), and
formed all eight literal endpoint residuals from (24). Exact symbolic
rational differentiation and elimination gave the following results.

- At q=(1/2,...,1/2), P=1/256. The four actual values are exactly
  (3,11/4,2,3), (2,3/2,3/2,2), (2,3,3,11/4), and
  (3/2,2,2,3/2), in the displayed phase order.
- All eight active Quit-minus-Continue residuals are exactly zero.
- All eight inactive Continue-minus-Quit margins are exactly
  1/8,15/4,2,7/8,1/8,15/4,7/8,2 in the displayed order.
- All sixty-four entries of 255 times the rate Jacobian match the
  displayed matrix K, with the displayed row and rate orderings.
- det K is exactly 16435089066040617600000, with factorization
  2^10·3^7·5^5·17^4·29·151·6421. Dividing by 255^8 gives
  det J=28792380416/31320375, so it is nonzero.

These calculations use all prescribed singleton and scheduled-pair rows,
and all triple rows entering inactive Quit endpoints. The grand row is
indeed unreachable under the prescribed profile and under any one-player
replacement: at a live date at most two opponents can be scheduled, so
even a replacing inactive player can create only a triple. Its four
coordinates can therefore vary freely without affecting any equation or
margin. This is consistent with, not an obstruction to, a sixty-coordinate
raw neighborhood.

## Producer and unrestricted deviations

The denominator is nonzero in a full Euclidean neighborhood of the center,
so F is smooth as a function on R^60×R^8 there. The invertible rate
Jacobian gives a local rate selector q(r). A sufficiently small raw reward
ball lies in its parameter domain, keeps all rates in (1/4,3/4), and
preserves the eight strict inactive margins. The policy identities are
identities of the actual periodic values U(r,q(r)), not additional unknown
continuation values. Thus owner residual zero and inactive margin positive
give exact local root Nash at every phase.

Under any complete unilateral replacement, the other three players supply
six scheduled coins per period. Their simultaneous conditional independence
on the unique live public history bounds period survival by
rho=(3/4)^6<1. Local endpoint optimality therefore telescopes against any
time-dependent or history-dependent replacing behavior, with a continuation
remainder tending to zero. This proves exact terminal Nash, including pure
Never and arbitrarily late deadlines. No bounded-controller restriction,
shared random seed, or restriction to phasewise deviations is needed.

The same argument gives E[tau+1]≤4/(1−rho), uniformly over replacing
behaviors. Since all pre-absorption payoffs and the selecting-date payoff
are zero, the difference between N-date average and terminal payoff is at
most M E[tau+1]/N when M bounds absolute rewards. The stated
8M/((1−rho)N) bound on average unilateral gain follows by applying this
twice. In particular one original-game target U_A is fixed before the
accuracy and one profile works for all sufficiently large horizons.

## Exact project semantics inspected

The ordinary proof supplies precisely the three hypotheses of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`: actual policy
recursion, exact phasewise `IsεQuittingRootNash` with error zero, and
playerwise opponent-cycle contraction. That declaration passes from live
hazards to arbitrary complete behaviors via
`quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue`.
The same file's
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
has exactly these hypotheses and concludes the original-game uniform
payoff statement. I also inspected
`IsQuittingCyclicResponseSolution` and its Bellman-cap use in
`UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`.
These declarations confirm the relevant semantics; the new table, Jacobian,
and implicit-function argument are still ordinary mathematics, not checked
Lean instances of those declarations.

## Remaining scope

I found no mathematical objection to the stated local-existence producer.
The bounded source-coverage comparisons in the last part of Section 13 were
not audited by this review. In particular this PASS does not establish
that every table in the neighborhood avoids all existing sources, or that
the center lacks other types of equilibrium. An independent coverage check
is still needed for any strict-new-coverage export claim.
