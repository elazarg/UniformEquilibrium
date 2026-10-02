# Independent check of the robust final-window reach theorem

Reviewer: CODEX_SKEPTIC.

## Verdict and scope

PASS for Section 12 of
`notes/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md`, using its
Sections 5, 10, and 11 as ordinary mathematical source producers. I first
derived and saved the proof independently in
`notes/CODEX_SKEPTIC__ROBUST_APPROXIMATE_FINAL_WINDOW_REACH.md`, then read
Section 12 to compare it. No mathematical objection or missing packet field
was found. No Lean build, export review, or review of Section 13 is claimed.

## Claim checked

For every fixed Fin4 quitting reward table without a uniform-equilibrium
payoff, there exist H≥1, e_*>0, and ρ>0 such that every finite timing
ε-Nash profile, 0≤ε≤e_*, at every deadline N≥H satisfies

    R(N−H)≥ρ.

The source is an ordinary ex ante approximate Nash profile on the finite
date-or-Never menu. The conclusion concerns its actual joint reach and
literal conditional suffix, not a newly selected profile, a compact limit,
or an assumption Nε→0. The conclusion does not cap the omitted late-date
deviation and does not prove uniform-equilibrium existence.

## Exact valid steps

1. The inspected
   `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`
   (`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`)
   quantifies over every positive support tolerance and every nonnegative
   charge target in one fixed compact carrier. Its contrapositive therefore
   supplies one forbidden tolerance λ and charge T. It does not require
   bounded capacity for approximate roots as an extra premise.

2. Choose the reach level and finite-error threshold after λ,T and the
   Section 5/11 thresholds, before choosing N or a source. At a first
   crossing K of ρ, all earlier source tails have error at most ε/ρ and
   remaining deadline at least H. This licenses the Continue floor η there,
   without assuming the conclusion R(N−H)≥ρ.

3. The crossing endpoint has R(K)≥ρη⁴. Section 12 correctly includes
   e_*≤ρη⁴e_τ and remaining deadline at least H_τ. Therefore its payoff
   floor applies to v(K), as well as all earlier displayed values. This
   endpoint becomes the starting value of the reversed packet and cannot
   be omitted. Using ε/ρ at K would have been a gap; the actual text does
   not do so.

4. Root absorption α_t obeys q_i(t)≤α_t. Together with
   −log(1−q_i(t))≤q_i(t)/η, this gives
   −logR(K)≤(4/η)Σα_t. The chosen
   ρ=exp(−4(T+2)/η) makes the source charge exceed T+2. My independently
   saved proof instead bounded joint Continue directly below by η⁴,
   obtaining a weaker but sufficient charge factor. Both proofs are valid.

5. Section 10's pruning deletes total hazard at most
   μ≤4ε/(ρδ), uniformly in prefix length. With δ=λ/4 and the stated
   thresholds, new support error is at most λ/2, and the new actual payoff
   floor is at least χ−λ. Absorption charge drops by at most μ≤1. Thus
   the forbidden requested charge survives. No Kε or Nε estimate is used.

6. Pruning retains the original suffix from K. Recomputing actual suffix
   values gives exact chronological Bellman equations and the same fixed
   reward cube. Reversal v'(K−s), q'(K−1−s) gives exactly the policy and
   support orientation required by `QuittingFiniteForwardPacket` in the
   cited file. Every value including both endpoints has its floor. The
   resulting packet contradicts the chosen λ,T prohibition.

7. For N<H, the final min(N,H) dates comprise the whole source, whose entry
   reach is one. Thus the short-deadline wording is also correct.

## Source and boundary audit

In addition to the packet record and its final consumer, I read
`IsQuittingRootSupportApproxNash`
(`UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`),
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
(`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`),
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`),
and
`IsCanonicalExactQuittingNashBellmanSpine.punishmentValue_le_of_all_normal_and_summable`
(`UniformEquilibrium/Quitting/Bellman/Finite/SummableExactNashBellmanPunishmentFloor.lean`).
The approximate pruning and punishment-floor producers are not attributed
to these checked consumers as if the adapters themselves were in Lean.

An exact root-data regression with η=1/2 has successive reaches
1,1/8,1/128 and first-crossing threshold ρ=1/8. Its crossing reach is
exactly ρη⁴. This confirms that the strengthened endpoint denominator is
real, not a cosmetic slack choice; the regression makes no Nash claim.

The theorem supplies the actual positive reach field for all sufficiently
accurate finite timing Nash profiles. The finite final window can still
carry positive unrestricted omitted-date debt. No return, punishment repair,
or terminal approximate-equilibrium consumer follows from this review.
