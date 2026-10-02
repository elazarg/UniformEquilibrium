# Three-cycle passive inheritance: source and class review

Reviewer: CODEX_FROBENIUS.

Scope: independent source and matrix-class review of
[`THREE_CYCLES.md`](../gpt/THREE_CYCLES.md) and
[`THREE_CYCLE_PASSIVE_INHERITANCE.md`](../gpt/THREE_CYCLE_PASSIVE_INHERITANCE.md).
Both packets were read completely. The matrix and inheritance arguments below
pass this review. There is one substantive attribution correction: the explicit
three-player rates and coarse values already exist in the Lean sources.
The complete strategic proof is examined separately in
[`THREE_CYCLE_PASSIVE_INHERITANCE__BY_CODEX_CAUCHY.md`](THREE_CYCLE_PASSIVE_INHERITANCE__BY_CODEX_CAUCHY.md).
No Lean compilation or literature-wide priority audit was performed.

## Claim being checked

For a finite quitting game, let `s_i = r_i({i})` and
`Gamma_ij = r_i({j}) - s_i`. The live and Never payoffs are zero. Behavioral
randomization is independent and private; a deviation replaces one player's
complete behavioral strategy. For a three-player subset `S`, the packet claims
that

    T = Gamma_SS invertible,
    T^(-1) >= 0,
    Gamma_kS T^(-1) >= 0 for every k outside S

produce a fixed ordinary uniform-equilibrium payoff, with all singleton levels,
outside singleton columns, and nonsingleton rewards unrestricted. This is a
source-data sufficient class and an actual strategy producer. It is neither
arbitrary child-equilibrium extension nor completeness of singleton cycles.

## 1. Existing mathematics that needs explicit credit

The packet's Section 3 is exactly the right-oriented three-player construction
already in `UniformEquilibrium/Quitting/Classification/ThreePlayer/CyclicCompiler.lean`.
In its notation,

    (rightP, rightQ, rightR, rightS, rightT, rightU)
      = (b_0, a_0, b_1, a_1, b_2, a_2).

`RightSingletonCycle` imposes the same six strict signs and the same product
inequality. After substitution,

    q_0 = rightAlpha,
    q_1 = rightBeta,
    q_2 = rightGamma,
    s_S + z^phase = rightCoarse phase.

For example, both expressions for `q_0` reduce to

    (a_0 a_1 a_2 - b_0 b_1 b_2) /
      (a_0 a_1 a_2 + a_0 a_1 b_2 + b_0 a_1 b_2).

The other two equalities follow by the corresponding substitutions; independent
symbolic simplification returned zero for all three differences.
`right_balance_one`, `right_balance_two`, and `right_balance_three` prove the
same indifference identities. `right_coarse_arc`, `right_coarse_active`,
`right_coarse_floor`, and `right_coarse_contracts` provide the corresponding
certificate fields. `rightSingletonCycle_isUniformEquilibriumPayoff` consumes
them for arbitrary signed three-player reward tables.

Consequently the phrase “the new calculation ... and its explicit rates” needs
revision. The rates and active coarse cycle are existing mathematics; their
inverse-matrix characterization and ambient passive-row adapter are the added
content identified by this review.

`BalancedSingletonCycleCertificate` and
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`) already
accept an arbitrary finite player set and an arbitrary phase-owner map. They
do not require every player to own a phase. Their fields are precisely the
arc recursion, active-owner equality, all-player singleton floor, and
deleted-opponent divergence used here. Their collision bound permits arbitrary
nonsingleton rewards. The packet correctly credits this consumer and must not
describe its use as a new strategy-class theorem.

There is a closer existing special-case lift than the packet's source list
currently records: `FinFourIntegralTournamentBalancedSingleton.certificate`,
`outsiderTail`, `outsiderTail_recurrence`, `outsiderTail_pos`, and
`target_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`).
They already construct a three-phase ambient certificate by calculating the
fourth player's continuation values. Their source requires the literal full
matrix `tournamentSkewMatrix t A` for an integral tournament and `t > 1`.
They are not the general row-cone adapter in this packet.

## 2. Actual added adapter, and an immediate reusable statement

The strict inverse characterization is correct. If a zero-diagonal invertible
three-by-three matrix has strictly positive inverse, the off-diagonal equations
in both matrix products force opposite signs in each row and column. The
positive entries form one of the two three-cycles. The diagonal inverse entry
then fixes the positive determinant sign, yielding exactly
`a_0 a_1 a_2 > b_0 b_1 b_2`. Conversely the displayed cofactors are positive.
This makes the existing three-player cycle directly accessible from an inverse
test.

The passive-row operation has a useful general form requiring no new research
branch. Let `S` be a nonempty finite subset of the ambient players. Suppose the
induced game on `S` has a supplied balanced singleton certificate with owners
`o(p)`, hazards `q_p < 1`, and surpluses

    z^p = u^p - s_S >= 0.

Suppose, for each outside player `k`, there is a row `w_k >= 0` such that

    Gamma_kS = w_k Gamma_SS.

Then the same owners and hazards admit an ambient balanced singleton certificate,
by retaining the active-player values and assigning

    u_k^p = s_k + w_k z^p.

Proof: the normalized child arc equation is

    z^p = q_p Gamma_SS e_(o(p)) + (1-q_p) z^(p+1).

Multiplying by `w_k` gives the actual outside reward recursion, while
`w_k z^p >= 0` gives its singleton floor. Active-owner equalities are inherited.
Deleted-opponent divergence for child players is inherited as well. For an
outside player every child owner is an opponent, and the child certificate
already supplies a positive-hazard phase. Therefore every field of the ambient
certificate is supplied, and the existing consumer gives its fixed uniform
payoff. No normalization of `w_k` to sum one is needed: this calculation uses
singleton-relative surpluses, not a strategic translation of Never.

This general inheritance lemma needs neither invertibility nor a three-player
core. It is a supplied-certificate adapter until combined with a producer such
as `RightSingletonCycle`; the packet's strict raw-table theorem supplies exactly
that combination. For its particular three-cycle, each coarse surplus is a
positive multiple of a different coordinate vector. Therefore

    all three passive phase floors hold  iff  w_k >= 0.

The row-cone condition is thus exact for these phase floors on this constructed
cycle, not merely an unexplained stronger sufficient bound. It is not necessary
for arbitrary ambient equilibrium, or for other cycles.

The weak-inverse approximation is separately credited to
`CODEX_NOETHER_SUPPORT__NONNEGATIVE_INVERSE_APPROXIMATION_ON_ZERO_DIAGONAL_TABLES.md`.
Keeping `w_k` fixed while perturbing `Gamma_kS` to `w_k T_eta` is valid and is
the appropriate additional adapter. All rows converge in the finite table;
the fact that some coefficients of `w_k` can be large does not obstruct
convergence. This review finds no extra sign condition on `s` or collision
rewards hidden in that passage.

## 3. Exact example and degree-one scope

For the displayed four-by-four `Gamma`, independent exact arithmetic confirms
`det Gamma = 3`, the full mixed-sign inverse, `det T = 7`, the displayed
positive inverse of `T`, and `Gamma_3S T^(-1) = (8,2,11)/7`.
The phase values and fixed target `s + (0,1,0,2/7)` follow from the already
identified coarse construction with hazards `1/2`.

All eleven support rows in the packet's LCP table were independently reproduced.
The only positive-support candidate with nonnegative outside slack is `012`,
with `h = (1,1,1,0)` and outside slack `2`. Empty support fails at right-hand
side `-1`; singleton support fails because the corresponding diagonal is zero.
Thus these omitted supports do not conceal additional roots.

The R0 proof is complete. A nonzero homogeneous complementary vector with
support of size at least two would give a kernel vector of its nonsingular
principal submatrix. A singleton support would require its full column to be
nonnegative, contradicted by the displayed negative column entry. At the sole
inhomogeneous root, strict complementarity makes the min-map derivative have
determinant `det T = 7`, so its local index is `+1`. The degree convention and
additivity are those of Section 2 of
`INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md`; no new degree
theorem is asserted here. This certifies `kappa(Gamma) = +1`.

The open-family claim is also valid. All relevant principal determinants,
negative-column witnesses, support-candidate failure witnesses, positive active
coordinates, and positive inactive slack persist under a small zero-diagonal
perturbation. So do strict inverse and multiplier positivity. The change of
coordinates between singleton rewards and `(s, Gamma)` is invertible on the
zero-diagonal slice. The sufficient set therefore contains a nonempty open
set in full reward-table space, with arbitrary nonsingleton coordinates.
This is a raw matrix degree-one region. It does not mean every completion has
all the additional strategic fields of the repository's hard-residual object.

## 4. Bounded separations and overlaps

- The full inverse-positive Fin4 packet assumes `det Gamma < 0` and
  `Gamma^(-1) >= 0`; this example fails both. Its strict three-player principal
  inverse is a different input from that full-matrix theorem.
- The `03` principal is `[0,-2;-1,0]`. At right-hand side `(-1,-1)` its slack
  is strictly negative for every nonnegative vector. Homogeneous nonnegative
  feasibility forces both coordinates to zero. By
  `isProjectiveQMatrix_iff_standard_or_homogeneous` and
  `IsProjectiveQBarMatrix` (`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`),
  this disproves full ambient projective Q-bar. It does not disprove the
  stronger reward-dependent theorem on the punishment-normal principal matrix.
- The negative graph is exactly `0->1, 0->3, 1->2, 2->0, 3->0`. A cycle
  visiting `3` must use `0` immediately before and after it, precluding a
  Hamiltonian cycle. Thus `SignedFourCycleSingletonData` and all its
  relabelings fail their required negative-successor condition
  (`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`).
- `QuittingCyclicSingletonOpenSignData`
  (`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`)
  requires a circulant normalized singleton matrix on the entire player set
  and schedules every player. Its first-negative requirement would also give
  a negative Hamiltonian cycle here. The displayed active triple itself is an
  existing open-sign example with `gamma=(0,-1,2)`; the ambient passive lift is
  the added step. Generic nonsymmetric inverse-positive triples are already
  covered by `RightSingletonCycle` on their child game.
- The literal integral-tournament lift fails because the `03` pair has both
  entries negative, whereas its paired off-diagonal entries are `t` and `-1`.
  Its singleton family is therefore not the displayed family.
- Product-low is a condition on collision rewards, not just singleton data.
  The cylinder includes completions that fail it: assign `r_i(I)=s_i+1` for
  every player. At the pure all-Quit product root every active player's Quit
  premium is `1`, contradicting `HasProductLowQuittingPremium`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`).
  Take `s_i=1` if a comparison respecting the nonnegative-singleton hypothesis
  of `exists_uniformEquilibriumPayoff_of_productLowPremium` is wanted
  (`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`).
  Other completions can satisfy product-low. No disjointness from its whole
  class, nor from all cyclic constructions, follows.

## 5. Review outcome and outstanding editorial correction

The claimed degree-one example and its neighborhood pass. The general
passive-row inheritance is sound and has an immediate existing consumer.
The strict theorem supplies a new ambient raw-table adapter relative to the
bounded source neighborhood inspected. The active three-player rates and
coarse cycle, their general mesh compiler, and the weak-inverse density
argument are existing dependencies and should be credited accordingly.

No mathematical objection remains within this review's source/matrix/lift
scope. The remaining correction is to add the exact three-player producer and
tournament lift to the packet's correspondence section and narrow the novelty
wording. This review covers the source, matrix, and lift arguments, not every
strategic estimate.

The bounded lookup used `docs/FRONTIER.md` and `docs/TOOLKIT.md`. In addition to
the declarations cited above, source checks included
`quittingSingletonMatrix` (`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`),
`QuittingAnchoredCyclicPatienceSystem`
(`UniformEquilibrium/Quitting/Cycles/AnchoredCyclicPatience.lean`), and
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` together with its
punishment-normal-principal variant
(`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`).
The Solan scope transcription `Literature/future/Solan1999.lean` was read only
as a scope check, not as evidence for an unexamined paper-priority claim.

The raw matrix-class comparison and the unrestricted-strategy theorem have
different proof obligations; neither should substitute for the other.
