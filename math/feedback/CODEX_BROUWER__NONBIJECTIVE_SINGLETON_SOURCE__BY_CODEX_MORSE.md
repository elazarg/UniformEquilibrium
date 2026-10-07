# Independent bounded check of the complementary-odds degree producer

Reviewer: CODEX_MORSE.

Scoped verdict: **PASS** on the root-production mechanism and its actual-
game adapter in the final section “Global nonlinear degree supplies the
missing nonzero root” of
`../notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`, whole-note SHA256
`e11cbd808d6c55b858dbf1a65d00a24a073472d6353ca3195b8f56e0357bca7e`.
I reconstructed the degree argument and challenged its signed and boundary
cases independently, without another review. This is ordinary mathematics,
not a Lean build. No full new-coverage fixture audit or export-artifact
verdict is included in this bounded check.

## Raw hypothesis and strategic scope

For one partition into two pairs, the assumptions are exactly

    c_i=r_i({i,a(i)})−r_i({a(i)})>0,
    r_i({i}∪T)≤s_i for every nonempty T in the opposite pair.

There is no sign restriction on own levels, Π_i, K_i, or the singleton
matrix. The construction under full R₀ and nonzero R₀ degree supplies
a nonzero complementary odds vector, possibly on a face, and from it an
exact original-game period-two terminal Nash profile. Bare Fin4 no-UE
supplies R₀ and degree one, so the contradiction proves raw UE existence.
Neither an inverse cone nor a chosen favorable component is an input.

## The global feasible-set bound

Let E={X≥0:ΓX≥N(X)}. In a proposed unbounded sequence normalize by
t=ΣX and take a nonzero limit u. Choose u_j>0 and i=a(j). The identity

    N_i=c_iX_j(X_k+X_l)+(c_iX_j−K_i)X_kX_l
          +Π_iX_j²/(1+X_j)

is exact. Since X_j tends to infinity, the second coefficient is eventually
nonnegative, whatever the sign of K_i. The last term has absolute value
O(t), whatever the sign of Π_i. Thus u_k>0 or u_l>0 would give a
positive order-t² lower bound incompatible with ΓX=O(t). The normalized
support is contained in the scheduled pair {i,j}.

The next limit uses the actual zero diagonal Γ_ii=0. Dropping the first
two nonnegative terms gives Γ_ij u_j≥Π_i u_j, whereas
Γ_ij=Π_i−c_i<Π_i and u_j>0. This is a contradiction even if both
coordinates of the limiting pair are positive. No positivity of N, of
the inverse, or of every original coordinate of the sequence was used.
The closed feasible set E is therefore compact.

## Total degree and the local origin

For H_λ(x)=min(x,Γx−N(x⁺)−λ1), a zero necessarily has x≥0,
nonnegative residual and complementarity. It therefore belongs to E for
every λ≥0. Since ΓX−N(X) is bounded on E, a sufficiently large finite
Λ leaves H_Λ with no zeros. A ball containing E in its interior gives
one common zero-free boundary for λ∈[0,Λ]. Hence the total degree of
H₀ in that ball is zero. This does not incorrectly extrapolate a local
degree or assume properness of the whole ambient map.

Under R₀ the positively homogeneous minimum map h(x)=min(x,Γx) has
only the zero root. Its norm has a positive minimum on the unit sphere,
so ‖h(x)‖≥a‖x‖. Meanwhile N(x⁺)=O(‖x‖²). The uniform perturbation
bound for coordinatewise minimum makes
min(x,Γx−θN(x⁺)), 0≤θ≤1, nonzero on a sufficiently small sphere.
Consequently the origin has the nonzero homogeneous R₀ degree. Excision
against the total degree zero forces another root outside that small ball.
No differentiability, regular-root census or isolated nonlinear root
assumption is present.

I inspected `r0Degree` and
`localDegree_lcpMinBoxProblem_zero_eq_r0Degree` in
`MathUE/LinearProgramming/R0Degree.lean`. The source uses the homogeneous
minimum-complementarity map and its positively oriented scalar chart;
the sign and radius identification needed here is the literal one.
Only nonvanishing is needed for the contradiction.

## Singleton supports and actual inactive values

If only X_j>0, all N_l vanish except possibly at i=a(j). Feasibility
forces Γ_lj≥0 outside that mate row. The remaining inequality is

    Γ_ij≥Π_iX_j/(1+X_j).

For Π_i<0 it is impossible because Γ_ij=Π_i−c_i<Π_i, while the
right side exceeds Π_i. For Π_i≥0 it forces Γ_ij≥0 too. Thus any
feasible singleton support would give a nonzero homogeneous LCP solution,
contradicting R₀. The produced root has at least two positive coordinates.

The template endpoint identities are correct with arbitrary Π,K:
active Continue equals U_i and passive Continue equals W_i+e_i/D_i.
For X_i=0, solving the actual two-phase recursion gives

    W_i^act−W_i=(e_i/D_i)/(1−(1−q_a)/D_i),
    U_i^act−U_i=(1−q_a)(W_i^act−W_i).

The denominator is positive because there is a positive opponent hazard.
Both corrections are nonnegative. Active forced Quit equals U_i, while
passive forced Quit is at most s_i≤W_i. Thus the correct actual values,
not the potentially incorrect template values, give every inactive
player's incentives. Positive coordinates have e_i=0 and retain the
original active equalities. All deleted-opponent cycles contract, giving
the unrestricted behavioral and fixed-target horizon conclusion by the
usual finite-iteration remainder argument.

An exact adversarial point combines all three delicate features. Use the
two-cycle-plus-leaves Γ displayed earlier in the note, schedule 01/23,
and take

    s=(1,1,1,1), Π=(2,2,−1/4,−1/4), K=(7,7,0,0),
    X=(1,1,0,0).

Then c=(1,1,1/4,1/4), e=(0,0,1/2,1/2), and U=W=(2,2,1,1).
The actual two inactive values are instead 7/6 at both phases. Their
correction is (1/8)/(3/4)=1/6. All cross-pair participant and relevant
triple rewards can equal their caps 1, so this is compatible with a
complete original table. The example tests negative Π, positive K,
boundary support and nonzero inactive correction at once. It is not
offered as new-coverage evidence.

## Literal source and weak boundary

`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`
does supply full R₀ and degree one from the original no-UE hypothesis,
without singleton-sign or auxiliary-equilibrium assumptions. Its named
R₀ dependency in
`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`
matches the stated matrix. Therefore the actual profile closes the
strict raw Fin4 argument, not only a conditional root interface.

The weak c_i≥0 extension also checks as UE-only reward closure: adding
δ to the four scheduled participant entries changes neither singletons
nor any opposite-pair joining cap. It makes every c_i strict. Applying
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
then returns an original-game fixed target. An exact periodic profile at
the weak boundary is not obtained from that argument and is not claimed.

I found no failed implication in this mechanism. The proposed modified
coverage table still requires its own complete source/child audit, exactly
as the author states; this scoped PASS does not certify that separate
unfinished task or authorize an export.

The author confirmed that whole-note hash
`80edfc39db0bd72f1c2ead9bea17552d89d4357c6e81bffeb6913a209076d44b`
changes only introductory/current-status text from the reviewed hash. I
reread the final degree section at those bytes; it is unchanged, so the
same scoped mathematical PASS applies. Later appended examples or coverage
claims are not included automatically in this mechanism verdict.

## Final standalone assembly, source calibration and coverage

Final-artifact verdict: **PASS**, with no unresolved mathematical objection,
on the complete 640-line artifact
`../exports/TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md`, SHA256
`9260c76df59721bd09dc94b9a72cb4bff5c1205f3b4456f8eb07b71320c068e9`.
I read all its sections and checked its substantive assembly additions
without reading another review. This verdict now includes the complete
fixture and the named raw-source comparisons; it is not inferred from
the earlier root-mechanism-only verdict. No Lean build was performed.

The statement preserves exactly four weak scheduled-pair joining
comparisons and twelve opposite-pair own-singleton caps. It adds no
singleton-sign, inverse, favorable-graph, chosen-root or strategic
premise. Under strict comparisons the original no-UE source supplies
R₀ and degree1, the nonlinear degree argument produces a nonzero root,
and the support and inactive-value arguments produce actual strategies.
The weak result is explicitly UE-only reward closure. Thus the final
three-partition counterexample restriction is an unconditional original-
table restriction, not a rephrased supplied-certificate interface.

### One-chart degree calibration and strategic completion

The new calibrated version uses one chart [−2R,2R]⁴ throughout.
The central region and its closure lie strictly inside that chart, so
the named ambient-map adapter identifies their cube solutions with
zeros of H_λ, including boundary points of the central region. Compact
E confines all λ-homotopy roots there. At the large offset the selected
region has no solution and hence degree zero. The small-region
θ-homotopy is isolating by the same uniform O(‖x‖²) estimate as before.
For the homogeneous field, solution-set excision compares this small
region to the central one; scalar-radius invariance then identifies
its degree with the literal `r0Degree`. This requires neither an
unimplemented arbitrary-chart comparison nor a whole-cube degree-one
assertion on the selected region.

I checked the actual statements in `MathUE/LinearProgramming/R0Degree.lean`,
`MathUE/Topology/BoxComplementarityAmbientMapAdapter.lean` and
`MathUE/Topology/BoxComplementaritySolutionExcision.lean`, including
`localDegree_lcpMinBoxProblem_zero_eq_r0Degree`,
`isSolution_ofAmbientMap_iff_of_coordinateInterior`, and
`BoxComplementarityProblem.localDegree_eq_of_solutionsIn_eq`.
The original no-UE source and arbitrary-close-reward consumer retain
their already reviewed hypotheses. This is static source validation,
not a new kernel-check claim.

All actual inactive corrections are retained in the artifact. The
signed stress target (−2,3,−5/6,25/6) is correct. The direct horizon
argument is also complete: opponent survival is bounded by ρ^m per
period, so every unilateral law has expected live duration at most
C=2/(1−ρ). The pathwise error bound gives MC/N delivery and 2MC/N
deviation gain relative to the one fixed ACTUAL phase-A target.
The initial-zero convention and negative rewards are both respected.

### Exact fixture and all five withdrawal operations

I independently recomputed the modified table's c=(2,1,1,1) and all
twelve strict caps. Hence its admitted raw set really contains a full
coordinate neighborhood, not just a thin stratum. Its inverse, principal
minors and complete offset−1 root census remain those of the displayed
R₀/degree1 matrix. The signed-column criterion fails on every partition:
its unique column signs require σ₂=−1, conflicting with c₂>0 on03/12
and with K₂=−1 on each other schedule.

All thirteen tabulated J witnesses were recalculated from the complete
table. The fourteenth child's two elementary rows are inconsistent.
In the withdrawal-strengthened test for child012, the literal F/J
definitions give precisely

    1≤λ₁/2−(D+4)λ₂,
    1≤−3λ₀+λ₂,
    −K₃≤−K₀λ₀−4λ₁.

At12 the participant withdrawals are exactly 4−5=−1 and0−1=−1.
The singleton withdrawal floors are at most1 for patient and both
security variants and at most0 for deadline/cancellation. Consequently
every dropped withdrawal term has the correct nonpositive sign; the
future terms are absent precisely for the three specified kinds.
The resulting negative upper bound contradicts −K₃>0 for arbitrary
nonnegative advance and withdrawal weights. I checked the definitions
and bounds in `WithdrawalFutureJoinRaw.lean`, `PatientWithdrawalRaw.lean`,
`DeadlineWithdrawalRaw.lean` and `DeadlineWithdrawalSecurityLP.lean` under
`UniformEquilibrium/Quitting/Classification/QuietExtension/`.

The child12 both-quit witness has actual payoff(5,1), not the old
modified singleton value; its two withdrawal comparisons are strict.
The separately supplied stationary child123 law has exact zero child
debt, zero Never, and omitted gain5210405575/136773399. The packet
correctly does NOT assert a universal zero-debt-profile witness for012;
it excludes that child's five raw certificates by the finite-row proof.
This preserves the distinction between raw certificate failure and
arbitrary safe-child selection.

The premium traps are exactly03 andI. The forced-Quit weight test
forces λ=0; the separate actual-row floor test also fails. The larger-
trap intermediate sums are88 and90, and product-low fails at the
displayed03 root. The response-partition, phase-floor, cyclic-child,
guard, conditional-range and influence comparisons retain exact failure
witnesses. I also checked the changed sure1 branch, the corrected ≤
bound in sure0, and the full sure2/sure3 boundary enumeration. The
reported sure0 gap recomputes to
−724795040468913623231/692156460057385664250.

No all-proper stationary exclusion is claimed or needed. The complete
strict raw class, its neighborhood, and the finite weak counterexample
restriction provide genuine additional counterexample-class narrowing
beyond the named accepted raw tests, including the signed-column cone.
All mathematical inputs needed by the packet are inline or named
repository declarations; there is no dependency on another conference
note, review, unaccepted CCE theorem, or unproduced strategic witness.

## Independent fixed-temperature representation check

Scoped verdict: **PASS** on RC1–RC10 and the proposition in “Retaining
tied atoms and the entire tester set,” in the author notebook at whole-file
SHA256 `810da591fdc5387491fb7133ebfa4301b8c7dff333fbb9db45fc1f510e013982`
(1873 lines). This is a separate ordinary-mathematical review of a supporting
global-minimum representation, not an export gate, an original-clock
attainment theorem, or a UE result. No counterpart review was read.

### Coarsening and strong convergence

The source bound uses the actual common active-cell push-forward, retaining
Never and transporting every response in both directions. I inspected
`quantileClockSupport`, `quantileClockScaledRadius`,
`hasEscapeAwareQuantileClockCompressionAtBound` and
`hasEscapeAwareQuantileClockCompressionAtRewardBound` in
`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`, and
`finiteClockActiveQuotient`, `finiteClockActiveCompressedLaw` and
`exists_finiteClockActiveCellIndex_eq` in
`MathUE/Probability/QuantileClock.lean`. For an arbitrary supplied absolute
reward bound M, the precise applicable wrapper is the `AtBound` theorem;
the `AtRewardBound` specialization uses the canonical game-specific bound.
Both give the stated 12M/j coordinate error for Fin4 with the appropriate M.
The 96M/j sum-debt bound and at most 8j+2 quantile cells follow.

The entropy chain rule is exact, including zero masses. Its reconstructed
law has the same common marginal and the same quotient masses. Thus global
near-minimality, not finite-calendar Nash or common support alone, yields
τΣ_i KL(p_i‖p̂_i)≤96M/j+η. Pinsker and Cauchy–Schwarz give RC5 with
the stated constants. The common-quantile coordinates identify this norm
with L¹ exactly. Bounded K-step functions form a compact L¹ family even
when endpoints coincide. Choosing j first and then the sequence tail
proves total boundedness of the actual likelihoods. Uniform continuity
of x log x on [0,4] proves entropy convergence. No positive lower bound
on the Never mass or likelihood ratios is needed for RC1–RC8.

### Tied intervals and both complete-cap inequalities

I checked the potentially delicate endpoint cases directly. An open
component (a,b) of the limiting endpoint complement is approached by one
whole original atom, not by several atoms of unrecorded relative order.
Otherwise an intermediate endpoint would persist inside (a,b), contradicting
Hausdorff convergence. Its limiting density is constant, and the only
available test in its interior is its midpoint. The midpoint itself is
retained because the corresponding original date is a legal response.

The assertion that E outside T has zero Lebesgue measure is also valid.
Inside a component of the complement of T, two distinct limiting endpoints
would force an original atom midpoint between nearby approximating
endpoints. That midpoint would contradict the positive distance from T.
Thus there is at most one endpoint in each such component. This justifies
the collapse map almost everywhere without adding any unavailable cut.

For prescribed outcomes, away from the countable component endpoints,
Never boundary and pairwise equal draws, the first-coalition partition
stabilizes. Two draws lie either in one persistent atom or have a limiting
endpoint strictly between them. Strong convergence of the product densities
then permits bounded convergence for each coalition indicator.

For a moving pure response x_n→x, there are two genuinely different cases.
At a persistent atom midpoint, x_n is eventually that exact atom's midpoint,
so the tie is retained. At x∈E, the limiting prescribed law has no mass at
x itself; a nonvanishing adjacent atom stays on its correct side because
its midpoint remains separated from x. All other atom masses crossing the
cut tend to zero. This proves convergence for every moving available
response, including the last finite response c_n→c. Never remains a
different isolated response, so signed singleton rewards cause no problem.

Consequently a subsequence of finite maximizers gives limsup b_i(pⁿ)≤b_i(q).
Conversely each limiting test is approximated by actual tests via Hausdorff
convergence, giving b_i(q)≤liminf b_i(pⁿ). The same argument proves
continuity of the limiting pure-response payoff on T; a positive atom's
midpoint is isolated, while non-atomic cuts have continuous payoff.
Thus the stated limiting maximum is attained, and neither cap inequality
assumes an unrecorded response location.

### Exact stress tests and scope

The tester-set bookkeeping is essential. In a two-player table with own
singleton payoff 1, passive singleton payoff 0 and pair payoff −10, let
both laws assign mass 1/2 to each of adjacent dates 0 and 1. The available
quantile tests are {1/4,3/4,1} and Never, and the complete cap is 0.
An artificially inserted cut at 1/2 would instead earn 1/2. Inserting an
empty initial date would also add the test 0 and raise the cap to 1.
These are different calendars with identical likelihood densities and
atom lengths. The proposed T distinguishes all three correctly.

At the opposite boundary, if all laws are Never, T={0} records a genuine
finite response while Never remains separate. With own singleton −1, the
two values are −1 and 0; collapsing those tests would be false. The proof
does not collapse them. Vanishing atom lengths likewise contribute no
unrecorded positive tie probability because all likelihoods are bounded by 4.

There is no unresolved mathematical objection to the stated representation
and attainment of the numerical value m_τ. This verdict does not justify
arbitrary variations on the limiting calendar, multiplicity of collapsing
empty dates, realization on ℕ, τ→0 passage, or a zero-debt conclusion.
Those missing consumers remain exactly as the author states. No Lean
compilation or kernel verification was performed in this review.
