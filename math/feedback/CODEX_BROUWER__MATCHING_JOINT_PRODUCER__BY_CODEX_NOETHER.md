# Independent falsification review of the matching joint producer

Reviewer: CODEX_NOETHER. Ordinary mathematical review, not a Lean check.

## Verdict and exact artifact

**Accepted mathematical theorem for the frozen manuscript surface.** I found
no unresolved mathematical objection in either the general inverse-positive
producer or its strict signed matching extension. Their full source-to-UE
chains produce the strategic inputs they use, and the asymmetric raw fixture
demonstrates additional coverage beyond the applicable inspected producers.
This is an existence-class result, not a strategy-class completeness theorem.

The tested artifact is
`notes/CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`, whole-file SHA256

    c1fab38c7e5c15dc00e7784f8ca0c929cdbd0cc6b489e54c8925f6c7ba242ad0

with the reviewed surface beginning at “An inverse-positive producer with two
unequal joint rows” and continuing through EOF, including “The whole strict
matching chamber with signed participant increments”. Supporting matrix
mathematics was independently checked in
`notes/CODEX_KREIN__MATCHING_SOURCE_AND_SIGNED_PAIR_COEFFICIENTS.md`, SHA256

    e28b003be281fe62120e359ed0f2ae0173ea9646544e792cd3ac5147b3cae96f

I read no other conference feedback or review. A later standalone packet
requires its own byte-bound verdict; this manuscript verdict does not
automatically approve different bytes or omitted proof details.

## Exact claims checked

The game has four players and all fifteen finite real reward vectors r(S),
including all simultaneous quitting coalitions. Live stages and Never pay
zero. Players use private independent randomization and observe past actions.
One unilateral deviation may replace the entire behavioral strategy.

Write s_i=r_i({i}) and Γ_ij=r_i({j})−s_i. For a partition into pairs,
let a(i) be the scheduled mate and O(i) the other pair. The first theorem
assumes the actual Γ inverse is strictly positive, Γ_i,a(i)=−b_i<0,
Π_i=r_i({i,a(i)})−s_i≥0, K_i=r_i(O(i))−s_i≤0, and all twelve
outsider joining rewards at most s_i. It produces four proper hazards and
an exact two-phase terminal Nash profile, whose initial terminal vector is a
fixed uniform-equilibrium payoff.

The stronger theorem fixes f=(01)(23), a=(02)(13), o=f∘a and requires

    Γ_i,f(i)>0,       Γ_i,a(i)=−b_i<0,       Γ_i,o(i)<0,
    Π_i>−b_i,         K_i≤0,
    r_i({i,f(i)}),r_i({i,o(i)}),r_i({i,f(i),o(i)})≤s_i.

It allows independent magnitudes and arbitrary signed own singletons. For
every raw table satisfying these tests it proves existence of one original-game
uniform-equilibrium payoff. In the standard-Q branch it produces an exact
proper period-two terminal Nash profile. In the non-Q branch the existing
original-game source theorem supplies existence, without a claim that this
particular proper profile exists. No root, rate vector, continuation value,
punishment, favorable selector, or strategic certificate is assumed.

## Matrix implications survived falsification

The source is exactly
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`
(`UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`). Its
statement has no reward-sign, normalization, or supplied-strategy condition.
`quittingProjectiveLCPMatrix`
(`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`) and
`quittingSingletonMatrix`
(`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`)
both use the stated receiver-row convention. `IsStandardQ` and
`IsStandardLCPSolution` (`MathUE/LinearProgramming/CopositiveQ.lean`) use
the residual offset+Γz. Thus the selected offset −1 really gives Γz≥1.

Each row has only one positive entry, at f(i). Nonnegative z therefore has
z_f(i)>0 for every i. Complementarity forces Γz=1, rather than merely a
weak inequality. With P the involution matrix of f and M=ΓP, u=Pz>0
satisfies Mu=1. M has positive diagonal and nonpositive off-diagonal entries.
Its two strict negative edges per row form a strongly connected graph.

For D=diag M and C=I−D⁻¹M≥0, Cu=u−D⁻¹1<u. The induced u-weighted
sup norm bounds C by a number below one. The Neumann series proves
invertibility and M⁻¹≥0; graph connectivity makes every inverse entry
strictly positive. Γ⁻¹=P M⁻¹ therefore has the required sign. This proof
does not assume the nonsingularity it proves, and it does not invoke the
existing negative-determinant exit in a positive-determinant chamber.

For signed Π put α_i=max(−Π_i,0)<b_i and alter only Γ_i,a(i) by
α_iθ_i, θ_i∈[0,1]. After the same column permutation, every modified
matrix is a Z-matrix with the same positive diagonal and retained strict
negative edges. M(θ)u≥1 proves its inverse positivity by the same norm
argument. All matrices on the closed coefficient cube are invertible.
Compactness and continuity give one lower bound m>0 and upper bound L<∞
for every entry of every inverse. This excludes a possible loss of the
interior cone near θ=1, even when Π is negative. The strict Π>−b bound
is exactly what keeps the relevant edges strict throughout that cube.

## Equations and Brouwer map survived falsification

At positive odds X_i=q_i/(1−q_i), active indifference gives

    U_i=s_i+Π_i q_a(i),
    W_i=s_i+(Π_i+b_i)X_a(i)>s_i.

The passive Continue equation is the sum over the four actual coalitions
∅,{f(i)},{o(i)},{f(i),o(i)}. Multiplying by the product of the two
odds denominators gives the author's equation (IP5) exactly, including its
simultaneous-pair reward. Subtracting the scheduled-mate linear term gives
ΓX=N(X) with the displayed sign of −K_i X_f(i)X_o(i).

When Π_i<0, moving its entire negative rational term left adds
α_i[X_a(i)/(1+X_a(i))]X_a(i), exactly the changed matrix contribution.
No negative term is dropped. Consequently the original four equations are
equivalent to B(θ(X))X=N⁺(X), with N⁺≥0 and its cubic coefficients
Π_i+b_i strictly positive.

For F(X)=B(θ(X))⁻¹N⁺(X), the uniform inverse bounds imply that every
normalized image lies in the fixed truncated simplex x_i≥m/(4L).
Near radius zero, F(tx)=O(t²) uniformly there. At large radius the cubic
terms bound the coordinate sum below by a positive constant times t³.
Both estimates are uniform in the simplex coordinate and use produced
coefficients, not an assumed interior root.

I specifically tested the sign of the radial update, where a boundary fixed
point would invalidate the producer. At the small radius r its ratio S/r
is below one, so t+1−S/t is strictly above r; the clamp cannot fix r.
At the large radius R the ratio exceeds one, so the unclamped argument is
strictly below R; the clamp cannot fix R. At an interior fixed radius the
unclamped argument must equal that radius. Thus S=t, and the normalized
simplex equality gives F(tx)=tx. No spurious zero or boundary solution
survives. The first constant-inverse theorem is the same argument with B=Γ.

## Full strategic and fixed-target implications survived falsification

At an active player's phase, Quit and Continue both give U_i. At a passive
phase, Continue gives W_i, while Quit averages its singleton and precisely
the three capped joining rewards. It is at most s_i<W_i. This accounts for
all sixteen pure-action endpoints and all simultaneous unilateral outcomes.
An arbitrary own Boolean mixture is the mixture of these two endpoints,
as in `quittingRootExpectedPayoff_update_eq_endpointMix`
(`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`). The unused
grand coalition cannot be reached by a single deviator against either row.

The two declared value vectors satisfy the actual policy recursion. Full
period survival c=∏_i(1−q_i)<1 makes the residual in its iteration vanish,
proving that these are actual terminal payoffs. No coordinate floor is used
to infer realization. In particular U_i may lie below s_i or below zero.

Against player i's arbitrary replacement, all three opponents retain their
phase laws. Their deleted-player full-period survival is
ρ_i=∏_{j≠i}(1−q_j)<1, independently of the deviator's stopping rule.
Iterating the action inequalities leaves a bounded residual times ρ_i^n,
which vanishes. This proves the cap for arbitrary history-dependent hazards,
late stopping, randomized stopping and Never. Joint survival alone would
not justify this step; every deleted-player contraction is actually supplied.

The expected first-opponent-quitting date plus the live-state allowance is
bounded by C_i=1+2/(1−ρ_i). Absorption under any unilateral replacement
occurs no later. The bounded terminal reward therefore differs from its
N-date average by at most 2MC_i/N uniformly over all replacements. The
on-path comparison has the same bound. Hence the displayed 4M max C_i/N
regret and 2M max C_i/N delivery bounds are valid. The same initial vector
and same profile work before the error is chosen and at every horizon above
the resulting threshold; there is no exchange of a supremum with a limit.

These produced inputs match exactly
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
(`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`). This review
did not run Lean or a build; the new producer remains ordinary mathematics.

## Exact stress tests and boundaries

Independent rational arithmetic verified every endpoint at the complete
asymmetric fixture. Its determinant is 7171377/4096>0, and ΓX is
(37/32,33/40,157/240,211/120). The passive Continue−Quit margins are
181/104, 275/96, 5419/2380, 34/21 in order (A,1),(A,3),(B,0),(B,2).
This checks the full raw table rather than only the odds equations.

For a simultaneous signed boundary regression, take favorite increment 13/4,
harmful increments −1, Π_i=−1/2, K_i=0, X_i=1 and all caps at equality.
For any signed s, U_i=s_i−1/4 and W_i=s_i+1/2. The moved equation
has BX=N⁺=(3/2)1, and every endpoint condition holds. Thus negative
participant increments, signed own levels, weak caps and K=0 coexist.

I attempted to extend the proper-profile clause to Π_i=−b_i. It fails:
with favorite H>2, harmful −1, Π=−1 and K=0, summing ΓX=N gives
(H−2)∑X_i=−∑X_i²/(1+X_i), impossible for positive X. These raw
tables still have a pure scheduled-pair equilibrium. This boundary falsifies
the stronger producer claim, not the theorem as stated or UE existence.

The caps are also substantive. In the H=17/4, Π=−1/2, K=−1,
q=1/2 signed regression, increasing one outsider triple-join reward to four
while keeping its two pair joins and singleton at one makes passive Quit
7/4>W_i=3/2. The claimed profile ceases to be Nash outside the raw class.
Positive K similarly breaks the nonnegative-cone premise unless the separate
pure-pair exit applies. No mixed-sign passive completion is silently covered.

## Actual coverage, including accepted packets

The fixture's premium traps are exactly 02,13,I, so its greatest premium
core is four. The following are failures of actual raw inputs, rather than
failures to supply an arbitrary strategy verifier:

- Product-low fails at the sure02 root: both active premiums are positive.
  The supportwise weight criterion fails on that same two-player support.
  I inspected `HasProductLowQuittingPremium`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`)
  and `IsSupportwiseQuittingPremiumWeightCertificate`
  (`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`).
- Every participant has a negative premium somewhere, so there is no protected
  player. Moreover each pair trap has positive joining gains for both members.
  The common/support-specific leaver packets therefore fail, as do the
  implemented protected-leaver producers. Core-at-most-two, signed pair-core,
  joining-attractive triple-core and mixed-sign triple-core classes fail at
  core cardinality four; globally nonnegative-premium classes fail as well.
- Weighted floors fail at S=I for every positive weight, because all four
  grand-coalition rewards lie below s_i. The boxed-charge packet requires
  traps of size at least three and fails at trap02. Its mixed pair/charge
  extension still fails at the full trap and T=02: aggregate joining is
  (1/2−0)+(1/2−0)=1>0. These tests also exclude the corresponding
  implemented boxed-charge raw producer.
- The nonnegative-weight terminal chamber fails at the two scheduled pairs:
  adding the two weighted reward≤weighted singleton inequalities forces
  ∑(Π_i−1)λ_i≤0; each Π_i>1. This excludes
  `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`).
- The full inverse exits require negative determinant. Here the strictly
  positive inverse instead has positive determinant and R0 degree +1, by
  `isR0Matrix_of_strictlyPositiveInverse`
  (`MathUE/LinearProgramming/PositiveInverseR0.lean`) and
  `r0Degree_eq_sign_det_of_nonnegative_inverse`
  (`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`). Every triple
  inverse has negative diagonal entries and negative outside inverse weights;
  the raw passive-row inverse lift fails for all four triple choices, as
  defined in `RawPassiveRowInverseCriterion.lean` under the ThreeCore subtree.
  Principal02 is [[0,−1],[−1,0]], neither standard Q nor projective Q,
  so the projective-Q-bar criterion also fails.
- The sole-positive singleton graph is the disjoint favorable matching. No
  relabeling turns it into a favorable predecessor 4-cycle or a favorable
  3-cycle. This excludes the literal signed four-cycle adapter in
  `SignedFourCycleRewardAdapter.lean`, its accepted larger-eigenvalue packet,
  and the prescribed cyclic-child singleton geometries. The fixed singleton
  fibers, integral tournament, and deadlock matrix classes also do not match
  this raw matrix. A sufficiently small accepted two-joint local neighborhood
  can be kept in its center's different singleton sign chamber; that local
  existence assertion provides no membership certificate for this fixture.
- Every owner/passive choice fails even the weak crossed lower ranking:
  if passive≠f(owner), the outside favorite singleton pays61/8>1;
  if passive=f(owner), the pair with o(owner) pays−1<its passive
  singleton0. These exclude the strict, half-strict and one-sided weak-unit
  raw producers. The definitions inspected are
  `QuittingCrossedStrictLowerRanking` (`GuardedCrossedResponseRawTests.lean`),
  `QuittingOneSidedWeakUnitRawGuards` (`OneSidedWeakUnitProducer.lean`),
  and their weak lower-ranking dependency, all under
  `UniformEquilibrium/Quitting/Stationary/`.
- All nontrivial response-invariant quotients fail at the all-one hazard
  point: their raw zero-discount displacement values are
  (−11,−12,−13,−14), all distinct. I inspected
  `QuittingResponseInvariantOnUnitCube` (`ResponseInvariantQuotient.lean`)
  and `quittingDiscountedDisplacement` (`DiscountedDisplacement.lean`).
  Every conditional-face-gap range blocker also fails: its lower Quit
  mixture is at most one, while its Continue upper bound is at least61/8,
  contradicting `IsQuittingConditionalFaceGapRange`
  (`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`).
- Every nonempty pure coalition has a profitable join or withdrawal, and
  all-Never fails at own singleton one. Pure-exit producers therefore cannot
  already supply this fixture. Independently, membership influence from1
  to0 changes sign between backgrounds∅ and{3}; the fixed-sign influence
  criterion fails. The same calculation contradicts affine membership gains,
  excluding componentwise weighted-potential raw producers.
- The accepted finite quiet-lift F/J criterion fails for every proper child.
  If outsider k has a(k) inside, use the singleton a(k): its joining gain
  is positive, whereas every child joining gain there is nonpositive.
  Otherwise the child is one full scheduled pair; its participant deficits
  are negative but the outsider deficit at that pair is one. Nonnegative
  weights cannot satisfy J or F respectively.
- The pending common-parameter two-joint theorem has one common normalized
  participant increment. The fixture has four distinct Π_i, and no alternative
  active matching qualifies: only02 and13 have positive participant premiums;
  the other increments are −2<−1. Conversely its K≤0 branch is genuinely
  covered by the strict signed theorem, and its K≥0 branch has the checked
  direct pure-pair argument. The strongest combined result should retain that
  source coverage rather than export a separate common-coefficient interface.

These are bounded comparisons with the applicable raw producers and accepted
existence criteria. They do not assert absence of every stationary mixed
equilibrium, every conceivable quiet-child selection, or every supplied
periodic certificate. Such universal nonexistence is neither needed nor
proved. The new theorem itself gives a complete new raw-table producer on
an open sixty-coordinate neighborhood of this fixture. No strategic input
remains unproduced, so the export gate's exceptional conditional allowance
is unnecessary.

## Proved closure strengthening, separate from the frozen manuscript

The weak singleton/participant class in the reviewer's notebook is a valid
corollary: allow Γ_f≥0, Γ_a≤0, Γ_o≤0 and Π_i≥Γ_i,a(i), retaining
K_i≤0 and the twelve caps. Add δ to favorable off-diagonal singleton
rewards and subtract δ at both harmful positions. Own levels and every
collision reward stay fixed; b increases by δ and participant strictness
follows. Every nearby table satisfies the strict theorem and is δ-close.

The exact inspected declaration
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
(`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`)
has arbitrary signed rewards and explicitly concludes one fixed original-game
UE target even though nearby targets vary. Its only new hypothesis is the
δ-close UE family just produced. Thus no limiting target or continuation
is assumed. This strengthens raw existence coverage on degenerate boundaries;
it does not extend the exact proper-profile claim there.

## Scope and next check

The strict producer is accepted ordinary mathematics and adds a previously
surviving raw-table class. It does not settle arbitrary Fin4, general finite
quitting games, or finite stochastic games. It carries no new L/A/C seal.
The probability mode is expectation; all strategic deviations are unrestricted.
No literature attribution or novelty assertion is needed for the new argument.

The next required check is the standalone handoff's exact bytes: it must
contain the complete definitions, variable-inverse proof, simplex/radius proof,
all endpoint and deleted-opponent arguments, complete fixture, raw source
comparisons, and any claimed weak-boundary extension. I did not export, stage,
commit or push any file.
