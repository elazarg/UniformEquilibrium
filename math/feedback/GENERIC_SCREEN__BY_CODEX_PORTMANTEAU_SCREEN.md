# Strategic and compactness review of GENERIC_SCREEN

Reviewer: CODEX_PORTMANTEAU_SCREEN.

Verdict: pass within the assigned scope. The strict product-base source,
MAXimum-debt dependencies, zero-Never argument, singleton-mass collar,
varying-table compactness, common-calendar attachment, harmonic inequality,
and strict one-third bound are mathematically sound as stated. The algebraic
screened-root exclusion is a supplied premise in this review and is checked
independently elsewhere. No fresh Lean compilation or axiom audit was run.

Reviewed: [the updated short manuscript](../gpt/GENERIC_SCREEN.md), and
Sections 1–2, 6–8, and 10–11 of
[the full proof](../gpt/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md),
with the other sections read for context. Detailed proofs and the bounded
source inventory are in
[the reviewer's notebook](../notes/CODEX_PORTMANTEAU_SCREEN__MINIMUM_SINGLETON_COLLAR.md).

## 1. The crucial exact source is sufficient

`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
in `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`
has exactly the needed premises: joint-carrier membership, zero Never,
zero singleton coordinates, at least two players, and s_i<B_i for every
player. Its conclusion gives one unpadded root-then-Never profile with two
distinct sure quitters and exactly the same complete semantic pair and
outcome law. No ancestry, cap attainment, or finite-calendar hypothesis
appears. Its additional stationary-repetition conclusion is unused.

The underlying proof in
`exists_twoSureProductRootThenNever_realizing_semantics_of_strictSingletonMargin`
(`UniformEquilibrium/Diagnostics/Quitting/ProductRootLimitCapSandwich.lean`)
uses M_i≤B_i≤max(s_i,M_i); strictness forces B_i=M_i. The semantic cap's
definition is the supremum over every unilateral `BehaviorStrategy`, as
specified by `quittingContinuationBestResponseValue`
(`UniformEquilibrium/Quitting/Root/FirstBranch.lean`). Thus the conclusion
preserves the full-cap pair as well as its law.

`minimumTerminalSemantic_exploitabilitySingletonMargin`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`)
and `minimumTerminalSemantic_maximumDebt_allPlayersTie`
(`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`)
concern the same positive global MAXimum-debt minimum. The manuscript does
not substitute a minimum of total debt. The unit reward bound required by
the tie declaration is present.

## 2. Zero singleton laws and the collar

For an actual independent profile, with marginal Never probabilities a_i,
joint Never probability p, and singleton-i mass u_i,

    u_i≥(1−a_i)∏_{j≠i}a_j≥p(1−a_i).

Thus a jointly convergent zero-singleton law with positive Never mass has
Never mass one. The retained reward moment gives U=0; the MAX moat and
d_i≤m give U_i≥s_i. All s_i≤0 would make all Never zero-debt, contradicting
m>0. This correctly establishes the missing Never-zero hypothesis before
applying the product-base source.

Compactness of the minimizing joint-law set then gives a positive minimum
of total singleton mass. A violating sequence of actual near-minimizers
would converge jointly to a minimum violating that lower bound. The result
therefore covers every sufficiently accurate actual profile, not one
specially chosen sequence.

The varying-table graph proof is also valid: approximate each carrier point
by an actual profile, evaluate the same clock laws at the limiting reward,
and use the uniform reward-distance bounds for both prescribed payoffs and
the supremum over all responses. The law is unchanged. The compact set of
fiber minima with η≥a>0 consequently gives one κ and ε_0 for every table
in that set. No bound uniform as a tends to zero is obtained or needed.

## 3. Calendar attachment passes with the stated ancestry boundary

Sections 4–6 of
[MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md)
use a fixed singleton fiber, its positive maximizing value, the strict pure
sure-coalition floor, complete reward-uniform finite approximation, and the
MAX singleton moat. They do not use the preceding stretch formula or an
old-table/final-table inverse-stretch identity. The generic source provides
their hypotheses, and keeps the four own singletons free for the projected
normal-cone argument.

Every actual inner minimizer in the common-calendar window is uniformly
near η(r_m), and η(r_m) tends to Ω_b>0. The fiber collar therefore applies
before tuple/calendar selection. The silent shift, tester-weight operations,
and final reward-table transport preserve the prescribed outcome law.
Consequently the same selected profiles and final weights retain all the
predecessor's listed activity, stationarity, owner-weight, and total-pressure
conclusions together with Σ_i μ_p({i})≥κ.

The fixed owner obtained along a subsequence has total singleton mass
at least κ/4. This establishes no fixed date, response-law singleton mass,
cap-attaining response, or post-response cap control. The manuscript
explicitly relinquishes the original stretch ancestry, as required.

## 4. Harmonic and one-third bounds pass

On the strict Continue-cap branch, the exact prefix debt is

    d'_i=β_i d_i+q_i(H_i+β_i U_i−Q_i).

At a positive MAX minimum d_i=m, prefixing q_i=tλ_i yields derivative

    λ_i(B_i−s_i)−mΣ_jλ_j.

The Continue branch persists for all coordinates for sufficiently small t
because B_i>s_i. Taking λ_i=1/(B_i−s_i), a sum Σ_i m/(B_i−s_i)>1 would
make every debt decrease, contradicting minimality on the prefix-invariant
semantic carrier. This proves the harmonic inequality, including for
unattained carrier minima. No collision or complete response is omitted.

Let a=max_i s_i. All Never cannot attain a positive minimum, so a>m.
For an owner attaining a, B_i−s_i<1−m; other margins are at most two.
Hence m/(1−m)+3m/2<1, equivalently (3m−1)(m−2)>0 with m<1, and m<1/3.
The compact unit reward cube and continuity of η make its attained worst
value strictly below 1/3 as well. This numerical conclusion remains
strictly weaker than η=0.

## 5. Minor presentation issue and review limits

The final full-proof link in the short manuscript points through the absent
`screened_root_reduction/` subdirectory. The available full proof is the
sibling `GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md`.
This is a link repair, not a mathematical objection. No source file was
edited by this review.

No unresolved objection was found in this assigned part. The complete
assembled review also uses the separate independent algebraic audit.
This review neither exports the packet nor supplies a consumer of its
positive prescribed singleton mass, a counterexample, or a proof of
uniform-equilibrium existence.
