# Weighted forward packets: bounded actual-source attempt

Identity: CODEX_FRECHET_CYCLE. Status: stopped at an exact source-class
obstruction, which is an immediate corollary of an existing checked theorem.
No new theorem packet, arbitrary-table producer, export, or Lean work.

The attempted finite construction and its failure are recorded below.
The original producer remains unrestricted in its choice of initial absolute
payoff annotation. In particular, the source anchoring tested here is NOT
claimed necessary for that producer.

## 1. Target and one actual-data construction

Fix a four-player quitting table |r_i(S)|≤M, all-Never payoff zero, and
independent private stopping laws. Under the contrary assumption of no
uniform-equilibrium payoff, seek one fixed finite B and, for every ε>0
and Q≥0, finite roots q_t and absolute values y_t∈[−B,B]⁴ satisfying

    ‖y_(t+1)−F(q_t,y_t)‖∞≤ε a(q_t),
    Reg_i(q_t,y_t)≤ε a(q_t),
    y_t(i)≥P_i−ε,                       Σ_t a(q_t)≥Q.

Here F is the actual affine root payoff map, a is joint absorption,
and Reg_i=max(Q_i,C_i)−F_i is ordinary mixed-root regret. All values,
including the first one, are absolute payoffs; no normalization quotient
or algebraic loop is being counted as executable time. The reviewed
equivalence in `CODEX_HILBERT__ABSORPTION_WEIGHTED_FORWARD_PACKET_REPAIR.md`
converts this target into the original exact-forward support-error target.

The first attempted actual construction was finite backward induction
with each row's admissible Quit probabilities restricted to [λ,1],
λ>0. At each actual continuation choose a Nash equilibrium of that
finite compact root game and prepend it. Reversal of the construction
order gives an actual finite stopping-law profile. It has exact Bellman
matching, invariant reward box, and charge at least λ per added row.
This uses finite root-game existence, not an unrestricted approximate
equilibrium or the desired producer. However, removing the action
restriction gives only an O(λ) root-regret bound, not automatically
o(1) times that row's absorption. Its punishment-floor control is also
a separate requirement in general.

The pre-existing `CODEX_HILBERT__DIRECT_COMPACT_CLOCK_FLOOR_REMOVAL.md`
already blocks a source-free vanishing-floor removal inference at the
whole-law level. I therefore did not develop another parameter family
or claim that the preceding construction solves a new selection problem.

One minimal finite-row computation confirms the same ratio issue in
the canonical VANISH table at R=2,h=1. Starting from the actual exact
one-row payoff (1,0,0,0), put x=λ/(1−λ) and prepend
q=(λ,x,x,x), for sufficiently small λ. The three nonpivots are indifferent
and the pivot is at its lower Quit bound, so these are constrained Nash
rows against each resulting continuation. Put

    c=(1−λ)(1−x)³,        a=1−c,
    u*=2−λ/a.

The actual pivot annotations obey u_(n+1)=c u_n+2a−λ, u_0=1, and hence

    Reg_0(q,(u_n,0,0,0))/a
      = [λ(u*−1)/(a(1−λ))] · (1−c^(n+1)).

If λ→0 while nλ→∞, this ratio tends to 3/16, not zero. The nonpivot
regrets vanish and the annotations stay in the reward box with exact
punishment floors. Thus the issue is genuinely error per charge, not
mere inconsistency of annotations. This solved-table computation is only
a guardrail for source-free conversion; it is not a contrary-case
counterexample. No additional tremble calculations are pursued.

## 2. Targeted correction at a contrary-case near-minimum source

To retain the genuine global contrary-case data, I next allowed an
arbitrary targeted root correction, not an all-player uniform floor.
The tested class starts from an actual near-minimum payoff, permitting
a uniformly small change of that first annotation, and thereafter uses
any product roots and weighted Bellman errors allowed by the target.

The named existing theorem

    exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`
provides a compact payoff projection K of the complete GLOBAL SUM-debt
minimum fiber, an open neighborhood N of K, and c₀>0 such that

    Σ_i Reg_i(q,y) ≥ c₀ a(q)           for EVERY y∈N and EVERY root q.

This is ordinary mixed-root defect, not unweighted support defect.
The theorem is about a continuation value, not the head of an incoming
prescribed row. Its telescope requires no-UE data; I do not identify
a positive finite-menu optimizer with an unrestricted global minimizer.

Immediate weighted-interface corollary: if 0<ε<c₀/4 and y_0∈N, EVERY
finite packet satisfying just the two weighted error conditions has

    q_t=all-Continue,        y_t=y_0,        Σ_t a(q_t)=0.

Indeed Σ_i Reg_i≤4εa combined with the lower bound forces a=0 in the
first row. A product root has a=0 exactly when every player Continues.
Then F(q,y)=y, and the permitted Bellman defect is εa=0, so the next
annotation is identical. Induction repeats the argument. No assumption
about future annotations staying in N is needed: the first step prevents
any exit. The proof covers one-player, pair, and fully simultaneous
corrections, adaptive root choices, and both tiny and large root hazards.

Compactness makes the actual-source statement uniform. There exist
η>0 and r>0 such that every carrier pair z with
D(z)<D*+η, and every y with ‖y−U(z)‖∞<r, lie in N. To see this, first
choose a positive-radius thickening of K contained in N, then use
compactness of the semantic carrier and continuity of SUM debt to put
the payoff projection of a sufficiently thin near-minimum collar inside
half that thickening. Otherwise a convergent countersequence would have
a minimum-fiber limit outside the prescribed neighborhood.

Consequently every actual near-minimum source, including finite-law
realizing approximants, is covered. A source can remain actual without
its limiting carrier point being attained. No assumption that a limiting
minimum pair is itself an actual behavioral profile is used.

This is not a new isolation theorem. It is the direct substitution of
the reviewed weighted-error requirement into existing production
isolation. In particular, no choice of which coordinates to correct
can make the error/charge ratio vanish while the initial annotation
remains in this uniform near-minimum tube.

## 3. What this does and does not rule out

The attempted local actual-source construction cannot begin a positively
charged packet at sufficiently small weighted tolerance. Padding by
all-Continue rows cannot change this: such rows permit zero Bellman error,
so they provide no free motion out of the basin. This is why replacing
an ordinary additive error by error per absorption is consequential.

The unrestricted target in Section 1 nevertheless permits a first
annotation outside N. A genuinely nonlocal modification of an actual
law may first leave the near-minimum region. Likewise, an incoming
prescribed row at a near-minimum HEAD can have an off-minimum
continuation and need not satisfy Nash comparisons. The reviewed
uniformly reached entrance result preserves exactly that distinction;
the present corollary does not consume or invalidate its last row.

No proof that such a nonlocal starting point supplies unbounded charge
was obtained. Conversely, the tube obstruction is not a barrier against
all possible producers and does not settle the contrary case.

## 4. Source record and stopping point

The route was chosen from `docs/TOOLKIT.md`'s strict-minimum isolation
and finite exact-capacity entries. In addition to the declaration used
above, I inspected these exact source surfaces under their imports:

- `quittingRootCoordinateNashDefect` and `quittingRootTotalNashDefect` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`, confirming the
  ordinary-regret convention;
- `quarterGap_mul_absorptionMass_le_totalNashDefect_of_smallAbsorption`
  and `exists_open_linearAbsorptionDefect_of_compact_strictAllContinue`
  in `UniformEquilibrium/Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`;
- `quittingAnchoredPath_backward_rigidity_of_unique_allContinue` in
  `UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`;
- `finFour_quittingFullBoxExactPredecessor_hasFiniteBudget_of_no_uniformPayoff`
  in `UniformEquilibrium/Diagnostics/Quitting/FinFourFullBoxExactPredecessorCapacity.lean`.
  Its box is the canonical reward box; no arbitrary larger-box telescope
  is silently attributed to it.

The neighboring conference notes consulted were the direct compact-clock
floor-removal test, the regular-clock normalized no-go, and
`CODEX_SPINOZA__MINIMUM_SOURCE_EXACT_BLOCK_NORMALIZED_SEAM_FLOOR.md`.
Their existing obstructions were not counted as new findings. No literature
theorem, normalization-to-absolute adapter, or open producer was assumed.

The bounded attempt is complete. The exact next mathematical permission
is a nonlocal actual-law move or a freely chosen starting annotation
outside the minimum-fiber tube. Choosing one that also creates the
required arbitrarily large weighted charge remains open and is not
relabelled here as a theorem or a supplied-input producer.
