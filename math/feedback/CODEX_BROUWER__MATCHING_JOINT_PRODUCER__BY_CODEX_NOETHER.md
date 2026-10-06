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

I read no other conference feedback or review. The separate standalone
verdict at the end binds the completed handoff, including its changed fixture
and stronger weak-boundary statement, to a different exact hash.

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

I did not export, stage, commit or push any file.

## Separate final standalone verdict

**Accepted for mathematical export review, with no unresolved objection.**
The separately tested artifact is the complete 647-line file
`notes/CODEX_BROUWER__MATCHING_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md`, SHA256

    c47039fd1d48eb76e05ee5105021f39485de6003b62dd46c4aef75ddb1f40653

I read the entire standalone file and rechecked the differences from the
accepted manuscript. It fully includes the variable-inverse matrix proof,
the positive-odds Brouwer producer, all strategic and horizon arguments, the
weak-sign/weak-participant closure proof, the independent general inverse
criterion, and the pure-pair arm. There are no deferred conference lemmas or
unproduced strategic witnesses. The named existing semantic and source
dependencies are tracked Lean files, and I verified their hypotheses by
bounded source inspection without compiling or changing Lean.

This artifact uses a different full coverage fixture: Π_A=145/32 and
Π_B=99/14, with equal premiums within each pair but unequal premiums between
pairs. Independent exact arithmetic confirms all sixteen endpoints at
q_A=1/5 and q_B=1/6. The active endpoints are 61/32 and61/28;
passive Continue values are183/70 and305/128. Passive Quit is17/50
or31/72, with positive margins398/175 and2249/1152. The singleton
matrix, traps, grand-coalition tests, pure exits, rank/ratio obstructions and
matrix signs used in the earlier audit are unchanged. Both new premiums
exceed four, so the displayed larger-trap singleton charge inequality also
fails exactly. The universal proper-child counterprofiles are actual exact
terminal Nash profiles, with zero joint Never and an explicitly profitable
omitted player; they exclude universal child-debt certificates without
asserting that every possible selected child lift is unsafe.

I separately checked the new proper-three stationary exclusion. For a support
containing scheduled mates i,k and i's favorite j, player k's zero Never
value gives

    D(x)=(Π+9)x−Π,
    a=(1−2x)/D(x),       (Π+1)/(Π+11)<x<1/2.

Its two premiums satisfy 0<Π<9, proving D(x)>0 and the stated proper-rate
range. Player i has Quit value D(x)(a−c), whereas Never pays
(61/8)x(1−c)/(x+c−xc). Since a<1 and Π+61/8>9, the Quit value
is strictly below D(x)(1−c)<(61/8)x(1−c), itself no greater than
Never. This is an exact contradiction for all four proper-three supports.
It therefore excludes every relabeling of the proper-three local stationary
branch named in the packet, without claiming to exclude full-support
stationary equilibria.

The new affine-transport quotient exclusion is also valid. The all-sure
displacement scales by the player's positive affine scale, while the zero
derivative is the negatively scaled singleton row. Equal response rows in a
block force equal scales there because each original row sum is H−2>0.
Their distinct all-sure displacements then still differ. The visible affine
period-three cylinder has visible own/favorable/harmful center levels1,4,0
and radius1/50000000; its gap ratio is strictly below four, whereas the
fixture's ratio is53/8. The positive affine scales and shifts cannot change
that ratio. I checked the named cylinder source, its center table and its
invisible-coordinate definition directly.

The completed packet passes the substantive export boundary: it strictly
eliminates the stated weak matching raw class from the surviving UE
counterexamples and exhibits an open interior fixture outside the compared
actual producers and accepted existence criteria. This is not another
conditional interface. The weak and non-Q branches assert UE existence with
one fixed target, while exact proper period-two production is confined to
the strict construction branches. The boundary falsifier correctly prevents
inflating that stronger profile claim. New content remains ordinary
mathematics and earns no L/A/C assertion from this review.

## Separate arbitrary-passive extension verdict

**Accepted, with no unresolved mathematical objection.** The independently
tested artifact is the entire 310-line file
`notes/CODEX_BROUWER__MATCHING_JOINT_PHASE_ARBITRARY_PASSIVE_REWARDS.md`, SHA256

    c97c1320ef98c0d68fb866ba532effbe1d2c666f99b328ba3d08b4a3fcb5c6c6

The exact new claim removes every K_i sign restriction from the matching
raw-table existence theorem, retaining strict singleton signs, Π_i>−b_i
and the twelve outsider caps. Arbitrary own singletons and every unused
terminal reward remain signed. Its strict Q branch produces four proper
rates and exact period-two terminal Nash against unrestricted behavioral
deviations, with one fixed uniform target. Its weak Γ-sign/Π-boundary
closure asserts UE existence only. It does not settle arbitrary Fin4.

I independently derived its load-bearing scaled-point bound before reading
these frozen bytes, then read the entire artifact and checked the differences
from the accepted K≤0 proof. Moving K_i⁺X_fX_o into the favorite coefficient
of B(X), alongside the negative Π part in its harmful coefficient, exactly
recovers the original passive equation. After the favorite permutation the
new term is a positive diagonal increase. The original u>0 satisfies
B(X)Pu≥1. Scaling by the actual variable diagonal, rather than the old
diagonal, yields the required Neumann contraction and strictly positive
inverse on every finite cube. No global-in-X inverse lower bound is asserted.

For each positive scaled fixed point F(X)=ηX with0<η≤1, the two strict
negative coefficients imply

    c_i X_a(i)X_f(i)(1+X_o(i))
      ≤N⁺_i(X)<η(h_i+K_i⁺X_o(i))X_f(i),
    c_i X_a(i)<max(h_i,K_i⁺).

Thus its raw-data radius R=1+∑max(h_i,K_i⁺)/c_i is selected BEFORE
the cube inverse bounds and cone κ. The inverse compactness bounds, normalized
simplex self-map and O(t²) compression are then valid. At an outer fixed
direction, the radial clamp could fix R only if η≤1, contradicting the
strict scaled-point bound. At the inner boundary compression gives the
opposite strict radial movement. Every Brouwer fixed point is therefore
interior and solves the genuine four equations. This specifically closes
the potential circular radius/cone and spurious-boundary objections; uniform
cubic expansion at infinity is neither used nor needed.

The original action-endpoint, absorption and arbitrary-deviation proofs
depend on c_i>0 and the caps, not on K sign, so remain unchanged. Full Never,
history-dependent randomization and arbitrarily late stopping are controlled
by the three-opponent geometric survival factor. The same phase-A value and
profile give terminal-to-average error2MC/N and regret4MC/N at all large
horizons. The exact declarations
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`
(`UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`) and
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
(`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`)
were rechecked at their source signatures. The first has no sign or strategic
premise; the second gives ONE fixed original-table UE target even when nearby
targets vary. The singleton perturbations preserve caps and arbitrary K.
No boundary proper-profile compactness is assumed.

I recomputed the mixed-K fixture exactly: its determinant is33583397/20480,
inverse strictly positive, and all sixteen endpoints give the displayed
values. Passive Quit is17/50 or31/72 with margins398/175 and2249/1152.
Triple determinants are257/20 or53/4 and every inverse diagonal is negative.
The affine quotient test remains valid because equality of scaled response
row sums and all-sure responses would force equal ratios; the four ratios
−440/169,−96/37,−104/37,−112/37 are distinct. The proper-three proof
uses favorite terminal level289/40 or61/8 and Π+F_i>9, still giving
the stated contradiction. No full-support stationary exclusion follows.

This is a genuine additional raw class: the sole-positive matching fixes f,
and only scheduled02/13 satisfies the participant comparison. Its K₀=1
persists under small raw perturbations, so no relabeling places it in the
previous all-K≤0 producer. Neither scheduled pair has both outside K≥0,
so neither pure-pair arm supplies it. Unequal premiums prevent a common-
premium reduction. Its pure and proper-child profitable-deviation witnesses,
weighted-floor/upper-bound failures, principal-matrix signs, crossed weak-
ranking and conditional-range obstructions remain exact. These are comparisons
against the raw hypotheses already source-audited above, not against arbitrary
supplied certificates or a claim that every conceivable stationary or selected
quiet-child strategy fails.

The final combined export must carry its full named-source comparisons and
receive a separate assembly/hash check. The current proof itself is accepted
ordinary mathematics and strictly supersedes the passive-sign restriction.
I did not read any counterpart review, export, change Lean, build, stage,
commit or push. The math-unicode skill affected only terminal-readable notation.

## Final consolidated artifact verdict

**Accepted for mathematical export, with no unresolved objection.** This
verdict is independently bound to the complete 723-line frozen artifact
`exports/CROSSED_MATCHING_UNIFORM_EQUILIBRIUM.md`, SHA256

    4757f61a3e57ea6f328d1642136d52d4db2b012a160cda487e1ff167050e4a2c

I read the full consolidated artifact and checked its assembly against the
two separately accepted complete proofs above. The matching existence
theorem retains arbitrary signed K, strict proper production in its Q branch,
and weak-boundary UE closure with one fixed target. The separate general
inverse-positive criterion still requires Π≥0 and K≤0 and uses a constant
inverse with uniform cubic expansion. The radius-first scaled-eigenpoint
proof is used only where proved; no arbitrary-K assertion was imported into
the general-inverse branch. The pure-pair arm and proper-profile boundary
falsifier also retain their correct scopes.

The complete mixed-K table, moved-system values
(167/200,193/160,7/8,193/160), all sixteen action endpoints, affine quotient
ratios, proper-three exclusion and literal crossed/range guard obstructions
are consistent with the exact checks above. All twenty cited Lean files
are tracked. The named source statements' hypotheses and the raw-data
comparisons are preserved, not replaced by generic supplied-certificate
interfaces. Full behavioral deviations, Never, signed payoff realization,
one fixed target and all-large-horizon quantifiers remain explicit.

The result strictly narrows the surviving UE counterexample class, including
an open mixed-passive region beyond the prior K≤0 and pure-pair arms. It
does not assert full-support stationary nonexistence, arbitrary strategy-class
completeness, a solution of unrestricted Fin4, or a new Lean seal. This is
the final mathematical acceptance of these exact consolidated bytes.
