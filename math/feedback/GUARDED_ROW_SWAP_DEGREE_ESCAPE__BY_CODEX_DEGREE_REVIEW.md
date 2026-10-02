# Guarded row-swap: independent second mathematical review

## Verdict

PASS for the guarded-degree theorem, strict raw inverse-positive class,
weak-inverse uniform-payoff corollary, and exact finite certificates in
`gpt/GUARDED_ROW_SWAP_DEGREE_ESCAPE.md`. No mathematical repair is needed.
The theorem is ordinary mathematics, not new checked Lean. Full-ceiling
guards are stronger than necessary for some direct constructions; their
role and value must not be oversold during consolidation.

## Independent checks

### Immediate strengthening: matrix-free weak oriented guards

For signed Fin4 qualitative UE, all matrix assumptions can be removed and
only one orientation of weak guards is needed. Precisely, for an ordered
pair (a,b), assume the twelve weak lower comparisons for recipient a and
the four weak full-partner joining comparisons for recipient b. Equivalently,
the actual polynomial conditions Δₐ(qᵦ=0,z)≥0 for z≠0 and
Δᵦ(qₐ=1,z)≤0 for all z suffice. The lower minimum includes every T⊆J,
including the empty set and J itself.

Fix a sure, b Never; a finite mixed Nash among outsiders supplies their
original residual signs because their deleted clocks include sure a. If
outsiders are active, all deleted clocks contract and the weak guards
complete exact stationary equilibrium. If no outsider is active, their
Nash inequalities and b's upper guard give rₖ({a,k})≤rₖ({a}) for every
k≠a. Nonnegative sₐ then gives an exact sure-solo stationary equilibrium.
For a negative sₐ, argue by contradiction from no original UE.

The exact tracked declaration
`finFour_punishment_le_singleton_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`
gives original punishment value μₐ≤sₐ under precisely that contrary
hypothesis. The tracked
`isUniformEquilibriumPayoff_soloReward_of_instantPunishment` in
`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean` consumes
μₐ≤sₐ and all the displayed no-join inequalities, giving the fixed vector
r({a}) as UE and a contradiction. Both exact statements and the latter's
IR/no-join definitions were independently read; `quittingPunishmentValue`
in `Quitting/Stationary/MinMax.lean` is the infimum over independent
opponent behavioral profiles of the complete unilateral cap.

Thus sixteen weak raw comparisons yield unconditional signed Fin4 UE.
No punishment or favorable root is an input. In the sole-owner negative
branch this conclusion is not exact stationary equilibrium; absent the
contrary hypothesis it need not identify the fixed UE target as r({a}).
The original degree theorem remains valuable for its stronger interior,
at-least-three-active exact stationary output. The half-ceiling theorem
remains a distinct class not consumed by this sure-owner argument.

PASS for this bounded strengthening, independently of the other review.

### Original proof and finite certificates

The complete manuscript and complete supplied
`gpt/CHECK_GUARDED_ROW_SWAP.py` were read. The latter uses exact SymPy
arithmetic, performs no file writes, and passed when executed. Its matrix,
root, full-cap, partition, four child-LP, pure-toggle, and neighborhood
calculations match the displayed table.

The map uses row permutation PΓ, not ΓP or a payoff relabeling. When an
outsider is active, the crossed lower and upper guards force both selected
hazards into (0,1), so both original residuals vanish. At outsider zero the
single-partner residual divided by its hazard is an affine strictly negative
bracket. Thus every nonzero modified fixed point satisfies the original
individual endpoint conditions and has at least three positive hazards.

Global degree +1 and local degree κ(PΓ) use an expanded real domain and
retain the lower clip. The R0 homogeneous margin dominates the quadratic
remainder. Nonzero-root singularities, continua, and original strategy faces
do not affect annular existence. Positive inverse establishes R0 before
computing κ(PΓ)=−1 from the unique LCP(PΓ,−1) solution. Total degree +2
is not an equilibrium count or the index under the unswapped Nash map.

Complete behavioral caps are exactly max(Qᵢ,Hᵢ/(1−αᵢ)) because all deleted
opponent clocks contract. This is valid for signed rewards. The geometric
first-opponent bound is uniform over every replacement law. Tail censoring
also retains the full response class. For its finite-horizon bound, a late
positive-singleton response has no enhanced solo payoff; a negative-singleton
late response is bounded instead using Never. This one-sided argument is
necessary and is correctly retained. It does not claim two-sided uniform
convergence of every finite-opponent terminal response value.

The weak-inverse perturbation changes only off-own singletons, preserves
the finitely many strict raw guards for sufficiently small perturbations,
and makes the inverse strictly positive by the second-order support argument.
Original-game regret tends to zero by the 2δ reward estimate. Selecting a
payoff subsequence, then a profile, then its horizon threshold gives one
fixed UE target, without limiting-strategy or limiting-cap claims.

For the necessary-condition calculation, strict external singleton signs,
positive reciprocal entries, and Γ being R0 do imply PΓ is R0. If outsiders
are absent, the two crossed diagonal slack entries force both pair weights
to vanish. Otherwise both pair weights are positive, both pair slacks zero,
and swapping those zero slacks returns a homogeneous Γ solution. However,
the original manuscript's assertion that no-UE implies full Γ degree +1
uses an earlier mathematical theorem; a standalone packet must either give
that dependency properly or state this matrix restriction with its explicit
matrix premises. It is not proved by a bare standard-Q hypothesis.

## Boundary and increment

The table with only r₀({0,1})=2 nonzero gives an unguarded false crossed
fixed point (0,1,0,0), while player 0 can gain two. Thus guards are essential.
All four residuals of the main fixture at the all-half vector are distinct,
which simultaneously excludes every nondiscrete response-invariant partition.
Its full degree is +1. The robust neighborhood is full sixty-dimensional,
not an exact response-row equality locus; raw inequalities still constrain
its collision entries.

There is a separate simpler construction under the unit-ceiling guards:
fix one selected player sure and the partner Never, and take a finite Nash
equilibrium of the remaining players against the sure anchor. The lower
and upper guards justify the pair's endpoints. If the sure owner has
nonnegative singleton, even the no-outsider case satisfies its Never bound.
This does not invalidate the stronger interior, at-least-three-active
stationary producer. It means the full-ceiling nonnegative-singleton UE
conclusion alone should not be advertised as a novel degree-only entrance.
The half-ceiling companion avoids this shortcut and supplies a genuinely
different raw class; its pure-partner joining gains are positive.

## Source inventory and assembly condition

The narrow tracked-source inventory and Gowda Section 2 convention are
recorded in the companion crossed review. In particular
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` and
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` consume the
actual original-game root produced here. They do not produce that root.

One common-ceiling guarded theorem h ∈ (0,1] can contain both strict proofs.
Keep distinct the half-ceiling weak coefficient conditions and this note's
weak inverse with strict full-ceiling raw guards. The exact examples,
behavioral cap proof, signed finite-law argument, and literal approximation
must be included rather than delegated to temporary files. No unresolved
mathematical objection remains within that scope.
