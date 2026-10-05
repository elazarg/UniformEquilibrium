# Final signed-cycle surface confirmation

Reviewer: CODEX_HILBERT. Verdict: PASS for the final assembled mathematical
surface and its scope. This is the requested bounded assembly-integrity
check, not a new third whole-core gate or a claim of Lean implementation.

Reviewed file:
`formalized/HETEROGENEOUS_SIGNED_SINGLETON_FOUR_CYCLE_PRODUCER.md`, 614 lines.
Exact SHA-256:

    b6ef2d02ffcfe4f6c1cdfb71cff09d59dea09c2e4bca418970d4e712dfbfdc84

I read the entire final draft before any other review report. I focused on
the assembled statement, probability and UE definitions, actual certificate
handoff, unrestricted fine-mesh proof, elementary horizon bound, finite
early-absorption quantifiers, and exact collision boundary. No mathematical
repair is requested.

## 1. Raw hypotheses and fixed-target conclusion

The source is a real Fin4 reward table with arbitrary own levels and all
44 nonsingleton coordinates free. The strict signed tests select the SMALL
simple eigenvalue and explicitly check all four reconstructed coordinates.
No positive-singleton, punishment-normality, supplied continuation, or
unproved existence condition has been added to the theorem's telescope.

The normalized masses sum to 1−A, have positive sequential survival
denominators, and produce four hazards strictly between zero and one.
The rotated absorption weights used in the owner identity sum to 1−A:
their numerator is (1−A)t_(i+1). Thus the cyclic wrap is consistent also
at i=3. The two remaining passive phase floors are obtained from the stated
positive b and h, independently of the opposite comparison's sign.

The payoff v⁰ is fixed by the table before the error. For each error, one
fine profile works at all sufficiently large horizons; the statement does
not replace uniform equilibrium by unrelated finite-horizon equilibria.

## 2. Behavioral and horizon additions

At every fine date, forced Continue followed by restoration has EXACTLY the
prescribed value, for owners as well as passive players. Consequently a
pure response at a chosen date incurs only that date's endpoint gain, not
a sum of mesh errors over its preceding Continue decisions. The payoff
transport uses deleted-opponent reach, which is at most one.

Literal Never is checked separately. The three remaining owners provide
strict deleted-period contraction β_j<1, uniformly over the entire
deviator's behavior. Restoration after K periods differs from Never by at
most 2Mβ_j^K. This also works with negative own levels and negative values.
Pure-time mixture extremality then covers every complete behavioral
replacement, including unbounded/randomized dates.

The horizon estimate is valid: with period length 4L and β=max_jβ_j<1,
survival at each period boundary is at most β^K under every unilateral
replacement. Summing survival in blocks bounds the expected absorption
date plus one by 4L/(1−β)+1. The stated average/terminal error bound
2M(4L/(1−β)+1)/n is conservative and uniform in the deviation. Choosing
terminal error below ε/2 and each average/terminal error below ε/4 proves
the displayed uniform Nash inequality and payoff proximity simultaneously.

## 3. Finite actual laws and exact quantifier order

The marginal censor event at T=4LK has probability c_i^K; the four censored
clocks remain independent. Product coupling therefore controls prescribed
payoffs, and opponent-only coupling controls every unilateral response,
uniformly over all omitted dates and Never. Taking the supremum costs no
deadline factor and yields E_r(p)≤η_L+4MΣ_i c_i^K.

The order is exactly: given e,H,ρ,N₀, choose L, then K, then the censored
law and N=max(T+H,N₀). The law has no finite atom at or after T; hence
R_p(N−H)=A^K<ρ. Full error is proved BEFORE menu enlargement. This is not
an invalid padding of a finite-menu-only Nash law. No zero deleted-survival
inference is made from prescribed absorption.

## 4. Source interface and collision regression

I inspected `BalancedSingletonCycleCertificate`,
`BalancedSingletonCycleCertificate.toWithBounds`, and
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
The constructed owner, hazard, coarse, initial, probability bounds, arc,
owner equality, all-player floors, and opponent divergence supply exactly
its fields. The derived collision cap comes from the actual finite table;
it is not an assumption that nonsingleton rewards equal singleton rewards.

I also read `Game.IsUniformEquilibriumPayoff` in
`GameTheory/GameTheory/Stochastic/Uniform.lean` and
`isUniformEquilibriumPayoff_of_finitePlayerPhaseNashCertificate` in
`UniformEquilibrium/Quitting/Cycles/CyclicKofNPlayerPhaseHazards.lean`.
The latter supplied exact-root interface is not silently substituted for
the mesh argument.

The collision regression is exact. At Γ†, s=1 and r₀({0,1})=3, pivot0
can overwrite its phase-zero Quit by Continue and then Quit at phase1.
No opponent quits during phase0, so deleted reach into phase1 is one.
Its payoff is (1/2)·1+(1/2)·3=2 rather than v⁰₀=1. At the first fine
subdate of phase1 the Continue value remains1 and Quit gives1+2θ₁.
Thus the coarse cycle is not falsely advertised as exact Nash.

The handoff keeps the raw reconstruction separate from the existing semantic
compiler. The comparison scope properly concedes the old circulant fixture
and does not claim every nonsingleton completion was previously unsolved.
The heterogeneous row obstruction can be expressed invariantly as the ratio
of the larger to the smaller negative magnitude; this is unaffected by
column permutation and positive row scaling. The stated neighborhood claim
uses that invariant property, not a fixed ordering of its negative columns.

## 5. Final assessment

The final additions preserve the reviewed mathematical conclusion and
agency. They produce a raw-data sufficient class, actual independent
behavioral profiles, one fixed uniform payoff, and the stated finite-clock
source; they do not settle arbitrary Fin4 or assume a favorable selector.
No unsupported exact-coarse-Nash, rationality, chronology, or positive-gap
claim appears in the assembled surface. ROOT alone decides promotion.

Final administrative hash confirmed:
`8dabb5e019ed9542f76058b1ae34919791c510117226e1cdae3cf0de5b1d9e33`.
The author batched the final PASS header and replacement of an obsolete
question pointer by the same standalone early-absorption conclusion.
Neither changes the theorem being confirmed; no new mathematical assertion
was introduced by this update.
