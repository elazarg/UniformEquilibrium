# Independent response review: stationary-response quotient degree escape

## Verdict and scope

PASS for Theorems A and B, the Fin4 counterexample-facing and inverse
consequences, the 33-coordinate paired class, and the exact stationary
example, with the qualifications explicitly stated in the manuscript.
No unresolved mathematical objection was found in that chain.

The reviewed manuscript is
[`STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE.md`](../gpt/STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE.md).
This review independently checks both the strategic argument and the algebra
needed by it; it does not assume another review's conclusion. These are
ordinary mathematical conclusions, not newly Lean-checked theorems.

The precise distinction is important. The raw degree argument produces an
absorbing stationary **Nash–Bellman root**. It produces an exact terminal
behavioral equilibrium at that same root if at least two original hazards
are positive, or if its sole active owner's singleton reward is nonnegative.
A negative sole owner instead requires the stated punishment-normality
condition and a separate approximation argument. For Fin4, the named
same-table no-UE reduction supplies that condition in the contradiction
proof. The manuscript does not silently claim exact stationary equilibrium
in the negative-sole-owner case.

## 1. Raw partition, agency, and degree

The data and probability mode are sufficient: finitely many players,
arbitrary finite real terminal rewards, zero live and Never rewards,
independent private randomization, and complete unilateral behavioral
replacement. Equality of hazards within a block is a restriction on a
profile's numerical parameters, not a common random coin or a coalition
agent.

For each original player, the finite product formulas give

    Δᵢ = (1 − αᵢ)Qᵢ − Hᵢ,
    DΔ(0) = −Γ.

Polynomial equality on the full-dimensional quotient cube extends to the
ambient quotient space. Differentiating the response identity therefore
gives representative-independent row sums and ΓE = EA. There is no claim
that A is the singleton matrix of a smaller quitting game.

For a nonzero stationary profile, a = 1 − ∏ᵢ(1 − qᵢ) is positive,
vᵢ = [qᵢQᵢ + (1 − qᵢ)Hᵢ]/a is the actual repeated-profile terminal payoff,
and direct expansion verifies

    a[Qᵢ − Hᵢ − αᵢvᵢ] = Δᵢ.

Thus clipping the block coordinate according to the common residual
enforces the appropriate one-stage endpoint inequality for **every original
player**. No sum of block members' utilities or joint-deviation test
replaces an individual test.

The degree proof is valid on its stated ambient domains:

- On Ω = (−1,2)ᵏ, every clipped image lies in [0,1]ᵏ. The homotopy to
  the cube center has no displacement zero on ∂Ω and has degree +1.
- Near zero the upper clipping is inactive, while the lower clipping gives
  Z(x) = min(x, Ax + O(‖x‖²)). Omitting the lower clipping would be wrong;
  it is retained here.
- R0 gives a positive minimum of ‖min(x,Ax)‖ on the ambient unit sphere.
  The quadratic remainder is strictly dominated on a sufficiently small
  sphere, proving isolation and local degree κ(A), including boundary
  directions with negative coordinates.
- Excision leaves degree 1 − κ(A) away from zero. Proper-support and
  saturated roots remain inside Ω. No nonzero root is required to be
  isolated, and a total degree of +2 is not asserted to count two roots.

The LCP conventions agree with the coordinatewise minimum map, its
strict-complementarity index sign det A_SS, and right-hand-side independence
for R0 matrices in Gowda, *Applications of Degree Theory to Linear
Complementarity Problems*, Section 2, printed pages 869–870
([author-hosted paper](https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf)).
Integer, not merely mod-2, degree is needed.

## 2. Complete responses and the same-profile uniform conclusion

Exact one-stage Nash and the Bellman identity give both endpoint bounds
Qᵢ ≤ vᵢ and Hᵢ + αᵢvᵢ ≤ vᵢ. When αᵢ < 1, a deterministic deadline t has
terminal value

    Hᵢ(1 − αᵢᵗ)/(1 − αᵢ) + αᵢᵗQᵢ,

and Never has value Hᵢ/(1 − αᵢ). Every complete behavioral replacement is
represented by an independent first-Quit law along the unique live history;
conditioning on that law averages these values. Consequently its full cap
is max(Qᵢ,Hᵢ/(1 − αᵢ)), not merely the best stationary-deviation payoff.
The prescribed payoff attains the cap at an exact root.

With at least two positive original hazards, every player's deleted
opponent clock is geometric. Its first quit bounds the absorption time
under every unilateral replacement. Bounded rewards then give a terminal
versus horizon-H payoff error bounded by a profile-dependent constant/H,
uniformly over all replacements. The corresponding discounted error also
vanishes by the same geometric domination. Hence the same prescribed
stationary profile has the claimed uniform property. No bound uniform over
all roots is needed or claimed.

If αᵢ = 1 at an absorbing root, i is the unique active original player and
must occupy a singleton block. Its actual payoff is sᵢ, while its complete
cap is max(sᵢ,0). For sᵢ ≥ 0, any sole-quitting deviation's evaluated payoff
is at most its terminal cap, even without an opponent absorption bound.
The outsiders retain a contracting opponent clock. This covers the
otherwise exceptional finite-horizon case and justifies Theorem B's first
bullet. In particular, blocks of size at least two permit arbitrary signed
singleton rewards without this exception.

## 3. An explicit boundary falsification attempt

Consider two players with zero Never reward and

    r({0})   = (1, −1),
    r({1})   = (1/2, −1/2),
    r({0,1}) = (−1, 1).

Here Γ = [0,−1/2;−1/2,0] is R0 and κ(Γ) = 0: its homogeneous LCP has
only zero, while LCP(Γ,−1) has no solution. The discrete partition satisfies
the raw response identity. At q* = (0,1/4), the actual payoff is
v = (1/2,−1/2), and the one-stage endpoint Nash equations hold. Player 1
nevertheless gains 1/2 by replacing its strategy with Never.

This does not contradict Theorem A or B. It falsifies the stronger omitted
implication “absorbing stationary Bellman root implies exact terminal Nash.”
It also shows concretely why passing to a strategy limit is unsafe: for
qᵗ = (t,1/4), t > 0, the actual payoff is still exactly v. Player 0's full
cap is 1/2, while player 1's cap is −1/2 + 3t/2. Thus exploitability tends
to zero as t tends to zero, although the limiting profile q* has
exploitability 1/2. The disappearing deleted-opponent clock changes the
Never cap discontinuously.

The negative owner in this example is punishment-normal. Immediate Quit
guarantees player 1 at least −1/2 against every opponent plan; a positive
constant opponent hazard t gives cap −1/2 + 3t/2, so its punishment value
is exactly −1/2. Even normality does not turn the unmodified limiting root
into exact terminal Nash. The manuscript correctly uses normality for a
completion or approximation, not for that false assertion.

## 4. Negative sole-owner completion and the actual UE bridge

Suppose the selected root has unique active owner i, sᵢ < 0, and μᵢ ≤ sᵢ.
Boundedness makes the infimum and suprema finite. For each ε > 0, the
definition of μᵢ supplies an independent opponent plan whose **complete**
i-response cap is at most sᵢ + ε; attaining the infimum is unnecessary.

The finite solo prefix followed by that plan is a legal behavioral profile.
Against an arbitrary i-response, quitting during the prefix gives sᵢ,
whereas surviving it faces the chosen complete cap. These are disjoint
events, giving the stated global cap bound. Against an outsider j-response,
couple the first K independent owner coins with those of the original
infinite solo profile. A discrepancy in the terminal outcome can occur
only if all K owner coins Continue, with probability
ρ = (1 − qᵢ)ᴷ, regardless of j's strategy. Conditional punishment behavior
does not introduce a shared random signal.

It follows, with |r| ≤ M, that

    dᵢ ≤ ε + 2Mρ,
    dⱼ ≤ 4Mρ  for j ≠ i,
    ‖U − v‖∞ ≤ 2Mρ.

Choosing ε tending to zero and K tending to infinity gives actual terminal
approximate Nash profiles with payoffs converging to the one fixed vector
v. No convergence of their strategy laws to an equilibrium is invoked.
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` consumes
exactly these hypotheses and yields UE at v. It does not claim that every
punishment-completed profile is itself an exact stationary equilibrium or
that the unmodified negative-sole-owner root is uniform.

There is no discounted-to-stationary limit in the new proof: its degree
calculation is performed directly at zero discount. Thus no uniform lower
bound on deleted opponent clocks along a discounted root sequence is
silently needed.

## 5. Arbitrary cardinality and the normality qualification

Theorem A is cardinal-free. Theorem B's stated sign or normality assumptions
on singleton-block players are valid sufficient conditions for the direct
strategic completion. Only a selected negative sole owner can need the
normality hypothesis, but imposing it on every singleton-block player
ensures it without an additional root-selection claim.

This is a valid weaker scope, not a proof that normality is logically
necessary for arbitrary-cardinality UE under the raw quotient hypotheses.
The review supplies no counterexample to an appropriately stronger UE
theorem with that hypothesis removed. Conversely, the manuscript contains
no argument licensing its unconditional removal.

The earlier signed full-matrix degree/discount repair in
[`CODEX_LERAY_CARDINAL__STATIONARY_REPAIR_AND_INDEX_ESCAPE.md`](../notes/CODEX_LERAY_CARDINAL__STATIONARY_REPAIR_AND_INDEX_ESCAPE.md)
does not automatically transfer to every response-invariant quotient.
Writing λ for a positive discount rate, the stationary discounted response
polynomial has the form

    Δᵢ^λ = Δᵢ + λ αᵢQᵢ.

In the manuscript's centered paired class, on equal paired hazards,
α₁ = α₀ and Q₁ − Q₀ = s₁ − s₀. Therefore

    Δ₁^λ − Δ₀^λ = λ α₀(s₁ − s₀),

which need not vanish. Zero-discount response invariance alone is not a
discounted block-invariance theorem. This explains why importing the older
signed repair is not an unstated substitute for the new completion proof.
The raw partition/quotient criterion, rather than the direct clipped-map
degree calculation by itself, is the substantive increment relative to
that earlier review.

For Fin4 there is no normality input in the final criterion. On the literal
same bounded reward table, the named no-UE theorem supplies
`all_punishmentNormal`; no table change, positivity normalization, or
conditional auxiliary source is required. Finiteness supplies a reward
bound. The resulting contradiction is sound.

## 6. Homogeneous lift, paired class, and exact fixture

The lift Ex of a nonzero homogeneous complementary A-vector is nonzero,
nonnegative and complementary for Γ because ΓE = EA. Normalizing by its
positive coordinate sum gives the full simplex witness expected by the
tracked homogeneous-normal consumer. Its support-normality premise is
available under no Fin4 UE. This proves quotient R0 in the
counterexample-facing statement.

For an invertible nonnegative A⁻¹, every inverse row has a positive entry.
Thus any solution of LCP(A,−1) satisfies
x = A⁻¹(1 + w) ≥ A⁻¹1 > 0, forcing w = 0. Its local index is sign det A.
The proof first obtains R0 from the counterexample assumption; it does
not falsely infer R0 from uniqueness at this single right-hand side.
Strict inverse positivity separately excludes any nonzero homogeneous
complementary solution.

Independent exact symbolic recomputation from the displayed fifteen reward
vectors verified:

- the full paired residual identity at (x,x,y,z), ΓE = EA, determinants
  45 and −15, and both displayed inverse matrices;
- the active residuals F, F, −xf, the full inactive residual polynomial,
  and the active three-by-three Jacobian determinant −2A₀B₀C₀;
- all displayed stationary payoff formulas and all fifteen membership
  toggle gains;
- the rational root brackets, strict monotonicity bounds, and inactive
  residual upper bound −8269/15625 < −1/2.

The inverse-function argument therefore supplies an open neighborhood in
all sixty reward coordinates: the three active coordinates remain interior,
the fourth remains inactive with a strict endpoint inequality, and every
deleted clock continues to contract. It does not require symmetry of nearby
tables and does not claim an explicit neighborhood radius.

The 33 free nonsingleton coordinates are counted correctly: recipient 0 has
eleven, recipients 2 and 3 have twenty-two, and the centered relation
determines recipient 1's eleven. The four singleton levels remain arbitrary.
The canonical recipient shifts leave Γ and every stationary Δ unchanged;
the exhibited contracting root therefore has the claimed shifted actual
payoff and complete caps. This is not a general strategic affine-equivalence
claim with Never's reward held fixed.

The explicit bounded gate checks in Section 7.3 also agree with the table.
In particular, the F-row weighted coefficients for deletion 0 are
(0,0,−14/9) with lower bound 1; the indicated J rows for deletions 2 and 3
are respectively (0,−2,0) and (0,−2,−1), both with lower bound 3.
Nonnegative weights are impossible in each case, and deletion 1 follows
by the table's transposition symmetry. All reciprocal singleton entries
have the same strict sign, so there is no escort edge. Every three-player
principal inverse has a negative entry. The cross two-player principal
has no nonzero homogeneous witness and fails standard Q, for example at
the negative all-ones right-hand side.

The prose comparison to an unnamed “attached paired one-parameter collision
family” is not needed by any proof above. This review does not identify
that attachment uniquely or certify a broad overlap/priority claim from
that phrase. The explicit class, fixture, and bounded coefficient
comparisons stand without it.

## 7. Exact tracked source interfaces inspected

All following repository source paths are tracked. Declarations were
checked under their actual imports, not inferred from conference summaries.

- `normalizedSoloMatrix_eq_soloReward_sub` in
  `UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`
  identifies Γ in the correct recipient-row, quitter-column orientation.
  `normalizedSoloMatrix` and
  `normalizedSoloMatrix_eq_projectiveLCPMatrix` in
  `UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`
  provide the normalization dictionary.
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  and the `all_punishmentNormal` field of
  `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
  have the asserted signed, bounded, same-table Fin4 hypotheses.
- `exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal` in
  `UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`
  consumes a normalized full homogeneous witness and normality only on
  its positive support. It handles the possible simplex vertex explicitly.
- `IsQuittingStationaryBoundaryAdmissible`,
  `quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_endpointNash`,
  and `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` in
  `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`
  retain exactly the exceptional max(0,sᵢ) boundary condition.
- `quittingBestReplyValue` and `quittingPunishmentValue` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean` quantify over full
  behavioral strategies and opponent plans. `IsQuittingNormalPlayer` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean` means
  precisely μᵢ ≤ sᵢ, including negative singleton rewards.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  is the actual terminal-profile, fixed-target UE bridge used here.
- `IsQuittingSingletonEscortEdge` and
  `BalancedSingletonCycleCertificate.exists_escortCycle` in
  `UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`
  justify the arbitrary-period no-balanced-singleton-certificate check,
  including removal of zero-hazard phases.

No core repair is requested. The strongest verified survivor is the raw
response-invariant quotient producer with exactly the manuscript's complete
strategic consequences, including its signed Fin4 criterion and its stated
cardinal-free sign/normality scope. Removing that scope restriction would
require a separate argument, not a change of wording.
