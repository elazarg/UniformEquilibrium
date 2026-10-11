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

## Bounded final-document addendum

I checked `notes/CODEX_TURING_BOX__FOUR_JOINT_PHASE_CYLINDER.md`, SHA256
`42782d67edba1fb65ed8f7059c03a94650d49f907023beef98c91996df48c1da`,
against the soundness review above. The assembled statement and proof
faithfully carry the reviewed proper-row center, four values, eight owner
equalities, eight inactive margins, full Jacobian and its determinant. The
derivative recurrence and its center forcing are transcribed correctly.
I additionally recomputed rational Gaussian elimination after precisely the
row swaps (0,1) and (2,3). All eight new displayed diagonal pivots match:

    249, 504, 63746/63, 85850/83, -40163520/3219173,
    842743233/98440, 97699680/4928323, -35849887725/606632.

Their exact product is 16435089066040617600000, with positive net row-swap
sign, as claimed.

The strengthening from a raw sixty-coordinate ball to the open proper-row
neighborhood times ANY finite grand row is valid: every equation, prescribed
outcome and unilateral-deviation outcome uses at most a triple. It loses no
contraction or local-Nash hypothesis. The same proper-row radius therefore
works independently of the four grand entries.

With radius at most one, the largest absolute proper center reward is ten,
so the uniform reachable-reward bound M=11 is valid even when the grand row
has arbitrarily large finite entries. This is the only reward bound needed
by the deviation telescoping and finite-horizon estimate; the grand row
cannot be realized under any replacement. The selecting-date zero, complete
behavioral deviations, private independence, fixed target before accuracy,
and existential-only radius qualifications are all retained. Bounded
final-document PASS; this addendum is not a fresh coverage audit or a new
Lean/export seal.

## Independent Section 15 rectangle-producer check

Checked frozen whole-file SHA256
`797f0737c9b3682d579093625c020691fb0f170ba6a0863cf1011d695666ec84`,
Section 15, on 2026-10-11. Verdict: PASS for the producer of Sections
15.1–15.4. This is independent ordinary-mathematics evidence, not a Lean
seal, not an arbitrary-table theorem, and not a full new-coverage audit.

I independently reconstructed the literal scheduled singleton/pair rewards
and expanded every actual policy recursion. With b=g/[2(1-g)] and
d=a/[2(1-a)], the sixteen recursion residuals

    U_t - immediateReward_t - survival_t U_(t+1)

are exactly (1-a)F_A at A0,C2; (1-g)F_B at B1,D3; and zero at the
other twelve coordinates. Separately recomputing all eight active
Quit-minus-Continue gaps gives F_A at A0,C2, F_B at B1,D3, and zero at
A1,B2,C3,D0. Thus no continuation vector is being supplied independently
of the actual policy. At a two-variable zero, the contracting periodic
recursion identifies all four proposed value vectors with actual payoffs.

All rectangle estimates hold literally. For e=1/(4M),
h=(1-e)/(3/2-e) satisfies b(h)=d(h)=1-e. On the rectangle, all rates
lie in [1/6,1-e], a,g lie in [1/4,h], and every displayed value belongs
to [0,M]. The passive formulas are nonnegative combinations with coefficient
sum at most one. On g=1/4,
z0>=1+d(V-4)/4>=5/4, hence F_A<=-1/24. On a=1/4,

    w1>=bS/4+(1-b)gW/8>=3/2,

so F_B<=-1/12. The upper g face gives F_A>=3/4. The upper a face
actually gives F_B>=7/4-e, stronger than the stated 3/4. Coordinate
order (F_B,F_A) is correct. The rectangle zero is strictly interior.

I read `exists_rectangular_zero_of_strict_face_signs` in
`MathUE/Topology/RectangularPoincareMiranda.lean`. Its global-continuity
hypothesis is satisfied by composing the displayed rational field with
coordinatewise clamping into this rectangle; denominators remain positive.
The source's two-variable zero theorem is sufficient. The larger
`exists_uniformEquilibriumPayoff_of_periodic_rectangular_face_signs`
declaration is not being misused as a two-coordinate/eight-slot adapter.

I enumerated all eight inactive Quit endpoints. Each contains exactly one
barrier from r0(02),r2(02),r1(13),r3(13), with coefficient a scheduled
hazard times the other scheduled Continue probability. That coefficient
is at least e/6=1/(24M). The other terms are precisely singleton one,
scheduled pair participant reward at most five, and one of the eight
listed triple coordinates, hence all are <=L. A barrier <-24ML gives
strictly negative total Quit value. Prescribed Continue is nonnegative.
The arbitrary F coordinates do not enter prescribed rewards or the
replacing player's own reward under any unilateral replacement; the
literal support enumeration in Section 14 supplies this fact without
discarding any realizable triple.

At the produced zero all rates exceed 1/6. Removing ANY replacing player
leaves six prescribed opponent coins per period, so survival is bounded
by rho=(5/6)^6<1 independently of that replacement. The already reviewed
endpoint telescoping and the inspected
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` therefore
apply with their actual recursion, exact root Nash and deleted contraction
hypotheses. A finite table-dependent reward bound suffices for uniform
payoffs; no uniform bound over the arbitrary F or triple coordinates is
needed. The target is the original table's actual phase-A payoff and is
fixed before an accuracy is chosen.

### Additional bounded arithmetic check of Section 15.5

I reconstructed all fifteen rows of (39) and independently expanded the
three induced-player differences for EACH sure owner. Equations (40),
(41), and every stated owner2/owner3 grand-row correction are exact. The
support classification following them is also valid: for owner0/2,
positive z forces the stated small x bound, then d2<0 and d1>0 give a
contradiction; for owner1/3, positive z forces y>=K/(K+1), then d0<0
forces x=0, and z<1 is impossible. The listed Nash sets and floor gaps
K+Vx or K+Sy follow, with zero opponents-Continue mass, so they do not
depend on an assumed punishment value.

This extra calculation does NOT audit every subsequent named-source
containment assertion, does not establish disjointness from all prior
qualitative neighborhoods, and is not the second coverage/export gate.
There is no mathematical objection to the raw rectangle producer found
in this bounded review.
