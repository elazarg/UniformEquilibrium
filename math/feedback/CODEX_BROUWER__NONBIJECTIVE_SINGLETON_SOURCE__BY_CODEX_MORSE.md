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

## Independent RC11–RC12 finite-mixture transport check

Scoped verdict: **PASS** on the added “Finite atomic replacements with the
mandatory late test retained,” at whole-note SHA256
`32537b4b13d54e44add2df540cb036addf94a1582af821374b2669602e894407`.
This check concerns the finite transport and the new response tests only;
it does not repeat the preceding representation review or claim a descent.

The simultaneous input is arbitrary finite ν_i on T together with Never,
and arbitrary separate weights λ_i∈[0,1]. No cap optimizer, Nash law,
common mixture weight or public signal is supplied. The target laws are
the independent mixtures (1−λ_i)q_i+λ_iν_i. The enlarged tester set
includes a distinct empty c⁺ beyond c=max T, even if some λ_i=1 removes
all of that player's original support. This is the correct finite-clock
completion; it is not permissible to replace that last finite test by Never.

The zero-mass consolidation is legitimate. For each of the finitely many
inserted zero-mass locations one can first choose disjoint neighborhoods
whose limiting prescribed masses tend to zero, then choose the approximating
index so that those neighborhoods dominate the Hausdorff errors. The
preimage of each neighborhood is a consecutive block of actual response
dates. Replacing that whole block by one date is an order quotient of the
natural calendar, not a player-specific rearrangement. At c the block ends
at the first empty date after the last occupied one; a further empty date
is retained. If there is no finite occupied date, the same construction
starts with date 0. No nonvanishing original atom is moved across an
inserted location or silently split.

This preparation is necessary: mapping an inserted atom to one arbitrary
date in an uncollapsed zero-mass cluster could leave extra before/after
tests even when its limiting point is isolated in T. After consolidation,
an upper-bound test sequence approaching an interior insertion point can
remain strictly before it only if T has points approaching from below;
otherwise all sufficiently nearby original dates were in the one collapsed
block. The analogous right-side statement holds. In an accumulating case,
the limiting one-sided payoff is a limit of actual T-tests, so is bounded
by their supremum even when no test attains that value. At c every after
test has exactly the c⁺ value. Coincident tests and Never are kept literally.
This proves the upper full-cap bound. Each fixed old test away from the
finite insertion set, each inserted tie, c⁺ and Never is separately
approximated, proving the lower bound. Taking a supremum only after these
pointwise lower bounds avoids a false limiting-maximizer assertion.

The entropy argument also includes unequal λ_i. On the unchanged component
the density vector is ((1−λ_i)r_iⁿ)_i. At positive atoms the post-insertion
mass vector converges. At a formerly zero-mass location continuity of the
finite-vector entropy, together with 0≤H(y)≤(Σ_i y_i)log4, controls the
vanishing base contribution. The same finite-vector argument applies to
Never. Thus this is entropy convergence, not only lower semicontinuity.

An exact late-test stress uses two players with own singleton 1, passive
singleton 1 and pair payoff −2. From all Never, put mass 1/2 at the new
finite c and retain mass 1/2 at Never for each player. The pure-c payoff
is −1/2 and the Never payoff is 1/2, but quitting strictly after c earns
1. Consequently the cap on {c,Never} is 1/2 while the actual cap is 1.
The added c⁺ restores exactly the missing response. This is a test of the
transport, not a positive-minimum example.

No unresolved mathematical objection remains to RC11–RC12. The conclusion
is a legal simultaneous finite-atomic variational inequality at a represented
regularized minimum. It neither produces a negative direction nor permits
arbitrary changes of the marked calendar. In particular it does not yet
consume a positive unregularized global debt minimum or prove UE.

## Narrow overlap/value check of the supported-unique-cap exclusion

This is an overlap check, NOT another independent proof review or export
verdict. The claim checked is the final unregularized section: a supplied
marked positive GLOBAL minimum cannot have, for every owner, a unique
complete maximizing clock carrying positive prescribed own mass. Finite
retained clocks and the separately labelled Never are both allowed.

The earlier finite same-tail selector in this notebook already obtains an
EXISTENTIALLY reselected first-row minimum maximizing the sum of squared
rates. If any mixed rate survives, a responsive cap tie obstructs it;
otherwise that reselected row is a pure collision. It does not exclude
the original represented minimum. It also does not test arbitrary later
supported response clocks by signed whole-law changes. Thus the new
exclusion is a genuinely stronger POINTWISE restriction on every supplied
marked minimum, although the tied-cap conclusion adds little in the
already reselected fully mixed first-row branch.

The nearest inspected generic declaration is
`Math.IsCoordinateAffine.exists_vertex_minimum` in
`MathUE/Analysis/CoordinateAffineBoxMinimum.lean`, under its actual import
`MathUE.Analysis.LowerBoxBoundarySmoothDrift`. It moves a global box
minimum of a coordinate-affine function to a vertex. The single-coordinate
interpolation and endpoint-decrease lemmas in the same file are the
elementary algebra used by the earlier selector. This existing generic
tool does not establish a complete-cap stable neighborhood, transport
signed mixtures on the old realizing calendars, or supply the endpoint
identity for the fixed-response polynomial. Those are the substantive
quitting adapters here; the multiaffine polynomial fact is not itself
new research.

A narrow search of `Diagnostics/Quitting/StoppingLaw`, nearby diagnostic
minimum/regret files, and `MathUE/Optimization` found the minimum-response
chord and fixed-witness/supremum-switch layers, but no existing declaration
with this supported-unique-complete-cap adapter. In particular the
one-law minimum chord is not a simultaneous open box, and the coordinate
box theorem does not make a distant selected-response endpoint actual
Nash. The proposed proof correctly uses that endpoint only algebraically.
No Lean build or unrestricted whole-conjecture review was performed.

## Second independent falsification review of the final cap-atom artifact

Verdict: **PASS**, with no unresolved mathematical objection to
`exports/POSITIVE_MINIMUM_CAP_ATOM_EXCLUSION.md`, SHA256
`29e55dee03a1cb70f9a470f5a3a9f646a1f3029c1108a5d5c384fe6c16471300`.
I read all 511 lines of that complete artifact, independently checked its
unrestricted-clock producer and final exclusion, and attempted to break
the isolated-cap gap, signed original-chart transport, last finite
tester, and distant polynomial endpoint. This is ordinary mathematical
review, not a Lean compilation or kernel seal. The preceding overlap
check was not a proof review; this entry is the full second review.

### Exact claim reviewed

For arbitrary bounded signed rewards on any NONEMPTY finite player
set, let delta be the infimum of SUM debt over all independent complete
natural-date/Never stopping laws, with full unrestricted behavioral caps.
Assume delta>0. From ANY specified finite-law minimizing sequence, the
artifact extracts its own original-witness marked calendar and attains
the same debt numerically there. EVERY marked minimum produced by that
construction has some owner with either at least two distinct complete
maximizing test points, or a unique maximizing point carrying ZERO own
point mass. The alternative also holds after retaining the separate
empty finite test c-plus. It does not claim arbitrary marked laws are
attainable, a positive gap exists, or the surviving branch is consumed.

### Falsifying the marked producer

The finite-law infimum reduction uniformly couples all unilateral
responses while censoring only small late FINITE mass to Never. Thus
it neither relies on opponent tightness nor drops late tests. The old
mixture-quantile densities are bounded by n and keep independent raw
coordinates; the chart is not a common random signal. Their weak-star
limits retain the marginal mass, nonnegativity and upper bound.

The endpoint and finite-test Hausdorff limits serve different purposes
and are both needed. A component (a,b) of the endpoint complement is
the limit of one entire OLD atom interval. Only its midpoint can be
an interior finite test. The limiting densities are constant there,
so every positive prescribed finite atom is exactly such a midpoint.
Endpoint points not in the test set form at most a countable set:
two endpoint points strictly inside one test-complement component
would force an old atom midpoint between them. They are therefore
Lebesgue-null. The final cut c is not an interval midpoint and has
zero own mass. Never remains a separate isolated label, even if c=1.

I tried the two unstable-kernel cases explicitly. Distinct raw
coordinates either share one retained atom interval, where the old
tie is eventually exact, or have a limiting endpoint strictly between
them, where the old order is eventually exact. Equal raw coordinates
and retained endpoints are null. If a moving response approaches a
retained midpoint, no EMPTY old response cut can enter that retained
open interval: the old response is eventually precisely its original
atom date. At every other limiting finite test the collapsed law has
no point atom, so the moving-order exceptional set is null. These
facts establish the stated L1 kernel convergence, including the last
finite cut c. Product weak-star convergence is valid here because
rectangle tests factor and the product densities have one uniform
bound; it is not asserted for arbitrary correlated weak limits.

The fixed-kernel/moving-kernel split consequently proves payoffs and
ALL caps converge. Taking an actual old maximizing sequence gives
the cap upper bound; approximating each fixed limiting test gives
the lower bound. Taking maxima before these two arguments would be
invalid, but the artifact does not do that. No earlier empty finite
test is invented before a first original date-zero atom.

### The two uses of positive own mass

Positive finite own mass implies positive mixture mass and hence a
retained midpoint isolated in T. Never is isolated by construction.
Thus deletion of the unique maximizing point leaves a COMPACT
complement on which the continuous response value has strictly smaller
maximum. The uniform FULL-response gap is valid. A unique zero-mass
accumulation maximizer would not have that gap; the theorem excludes
that attempted generalization explicitly. The complement is nonempty:
the separate last finite point c and Never already give two test labels.

Positive mass also makes signed reweighting legal. For fixed lambda
near zero, the target mass at an OLD atom is

    m_i^k + lambda_i(1-m_i^k).

Since m_i^k>=m_i/2 eventually and lambda_i>-m_i/4, this is at least
m_i/4 for negative lambda_i. All remaining masses have positive factor
1-lambda_i. Coordinates already pure at their selected atom simply
do not move. The original Never atom is used as Never, not replaced
by a late finite date. No negative probability or shared mixing flag
appears. Taking a small TWO-SIDED box, rather than only [0,1]^n,
is essential to the interior-minimum argument.

### Original-chart transport and every response

The selected finite atom interval has positive limiting length, and
the original date's own mass converges to m_i>0. The same is true for
the Never interval when selected. The normalized interval indicators
converge strongly in L1; after a fixed signed reset the OLD-chart
densities remain nonnegative and uniformly bounded, although their
old sum need no longer be exactly n. The convergence argument needs
only that bound, not a freshly recomputed mixture chart.

All collapse maps, actual response-date sets, and response kernels
are UNCHANGED. In fact all old positive masses remain positive in
the chosen open box. Consequently the moving-test convergence from
the producer applies to the new bounded densities, with both the
limsup maximizing-test and liminf fixed-test arguments intact.
The extra c-plus is harmless for a proved reason: q_i(c)=0 and no
selected reset targets c, so q_i^lambda(c)=0 throughout the box.
At c and c-plus each finite opponent exit is already strictly earlier;
on all-opponent-Never the deviator alone quits. Their response functions
coincide throughout this variation. Neither is equated with Never.
This remains valid for arbitrary signed singleton rewards and selected
positive Never atoms.

For EACH fixed lambda in the box there is a sequence of genuine
independent finite original-calendar laws with convergent FULL caps
and payoffs. Its debt is >=delta at every index. Passing to the limit
gives the required global lower bound for the represented signed
variation. No realization of an arbitrary annotation or simultaneous
finite profile for all counterfactual lambdas is needed.

### Multiaffine branch and the endpoint overclaim test

Uniform response coupling costs at most 2M times the sum of opponent
TV changes. The chosen box makes twice that error smaller than every
old complement gap, so all complete caps remain at their displayed
unique points there. The actual SUM debt equals ONE fixed-response
polynomial F in that box. Every lambda appears with degree at most
one, including in prescribed payoff, because the laws vary separately
and independently.

The lowest nonzero Taylor part of a nonconstant multiaffine F is a
nonzero combination of distinct nonconstant sign-cube characters.
It has mean zero and cannot vanish on every sign vector, so it has
a strictly negative sign value. A sufficiently small signed step
stays in the legal cap-stable box and makes F strictly smaller.
This argument covers higher-order flatness and zero coordinate
directions; vanishing first derivatives alone are not being used.

At (1,...,1) the displayed law of every owner is precisely its
displayed response clock. Hence EACH summand of the globally defined
fixed-response polynomial vanishes algebraically, including coincident
clocks, Never, and the all-Never tuple. This proves F is nonconstant
when F(0)=delta>0. It does NOT prove that the selected response stays
optimal at that distant point, that actual debt there is zero, or
that the tuple is Nash. The artifact makes exactly this distinction.
The actual contradiction is at the small signed step, transported
to one sufficiently large original finite witness below delta.

The three boundary tests are exact: the participant-one/passive-zero
grand profile has zero debt and unique supported caps; the half-date-zero/
half-Never profile has positive PROFILE debt with a legal local descent;
and the independent uniform compact-clock profile has a unique
zero-point-mass maximizer in its topological support with no uniform
gap. They invalidate the three tempting hypothesis weakenings, not
the reviewed universal theorem.

### Source truth and scope

The named censoring, complete-law/behavioral cap correspondence,
one-law payoff/outcome affinity, and finite-menu uniform target
criterion were re-read under the actual imports in
`Paths/LateFiniteStoppingLawCensor.lean`,
`Paths/StoppingLawOperationalDistance.lean`,
`Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`,
and `Terminal/FiniteMenuFullProfileApproximation.lean`. The existing
mixture declarations really require coefficients in [0,1]; the new
two-sided transport is proved directly and does not cite them as
authorization for negative coefficients.

No counterexample, silent tester identification, lost late response,
illegal negative reset, public correlation, or endpoint cap overclaim
was found. The precise surviving alternative remains multiple complete
test-point maximizers OR a unique zero-own-point-mass maximizer for
at least one owner. Its downstream global consumer remains open.

## Focused independent BG1–BG6 bridge review

Reviewer: CODEX_MORSE. Reviewed the ENTIRE final section
“A random minimum forces a root-to-later active payoff-kernel bridge”
of `../notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`, BG1–BG6.
Exact heading-to-EOF SHA256:
`a74e319a2e70999513399e527ce48769d9ef0013dece01272afb95df122c1afc`.
No CODEX_NOETHER BG verdict or feedback was read. The author's bytes
were not changed. Verdict: PASS as ordinary mathematics, with no
unresolved mathematical objection to the exact source restriction.

This review does not independently certify my own base recipient-scale
DR contribution. That full artifact already has two blind reviews;
here I check the NEW bridge inference and its exact compatibility
with one fresh final table. No export or Lean certification follows.

### Claim and exact compatible-table quantifiers

At a produced positive true global SUM minimum of one bounded,
debt-rigid table with pairwise distinct nonempty-coalition payoffs in
each recipient row, either the prescribed terminal outcome is
deterministic, OR some owner has BOTH the earliest active root τ and
a later response σ>τ maximizing its full cap. The root is finite,
isolated, has positive mixture mass and has no prescribed mass before
it. The two response PAYOFF KERNELS, not just their test labels or
coalition names, differ on a positive-probability set of old opponent
draws. Their expected values remain equal maxima.

The bridging owner can have zero individual debt. This is a producer
of genuine tied source data, not a debt decrease, cap-Nash root or UE
consumer. A random outcome may still have many other plateau aliases.

BG's stated82 table can be combined with the COMPLETE typed93 family
in MORSE Section50 at ONE final table. The correct construction order
is important. Start at the sign-adapted intermediate r^α, before its
recipient-scale selection. Common contraction by c∈(0,1) arbitrarily
close to1 sends Δ and every homogeneous raw label to c times its old
value, preserving all93 gaps, positivity and every nonzero lower-join
and grand-withdrawal sign. It puts every reward strictly inside the
unit cube. Choose a sufficiently small full-table perturbation inside
that cube outside the finitely many within-row equality hyperplanes.
For93 labels the coefficient bound is8, so the combined value/gap
change is at most16β, rather than BG1's82-only14β. Choose β below
the finite gap, positive Δ and all28 sign margins; the dense generic
set meets this open neighborhood. All OLD cohorts E_A,Z_A still give
the EXACT fresh positive branches; do not relabel them after selection.

NOW perform DR on that fixed actual carrier. Positive row scales
preserve within-row inequality and within-row join/withdrawal signs;
their arbitrary smallness preserves all93 gaps and positive Δ.
Coordinate-regular selection makes ALL FINAL unweighted minimizers
debt-rigid. Arbitrary reward perturbation AFTER selecting regular
weights would not preserve rigidity automatically, and is not used.
Apply SA, HR and BG afresh at this ONE table. Same-table normality is
obtained from its positive infimum, not inherited through perturbation.
Thus the combined random-outcome and bridge conclusions do not switch
minimizing families or import an old fixed tester. The author's82
statement is valid; the93 compatibility requires only this explicit
coefficient adjustment and finite-sign preservation, not new strategy
data or another independent producer hypothesis.

### Full cap-box and original-source falsification checks

1. BG2's strict-head argument treats ALL active response sets. Before
   τ, every old-head term is already absorbed, so every upper tester
   has one common positive affine transform. The compact lower set
   has no active point. Actual signed original conditionals use whole
   retained dates/RIGHT endpoints or null boundaries; an isolated
   endpoint is not approached by raw cuts splitting its interval.
   Individual constancy is derived only after the cap-stable actual
   box is made a family of true minima. A sole head gives U_h=s_h,
   contradicted by the checked four-player quadratic prescribed margin.
   Multiple heads collapse original laws to one common pure coalition.
   Thus nondeterminism genuinely excludes all strict pre-active mass.

2. If no owner bridges root to later, every cap containing τ is EXACTLY
   {τ}. Each such cap has the isolated uniform complement gap. Each
   other cap set is compact, excludes τ and is entirely later, so one
   ordered cut separates it from τ even if it accumulates elsewhere.
   For every upper response all reset-containing opponent terms quit
   atτ and supply the SAME constant; the original term has positive
   coefficient. This preserves every upper tie/order. The lower gap
   excludes all other responses locally. There is no hidden unique-
   later-max assumption and no selected branch derivative.

3. Supported resets for all positive root suppliers have literal
   old retained finite dates and bounded two-sided densities. ALL
   original moving test kernels are retained, including empty dates,
   arbitrarily late deadlines, Never and the exact finite c/c⁺
   duplicate. Hence the selected multiaffine sum equals actual D on
   an open signed box. Global minimality makes it constant; common
   debt then makes each selected polynomial constant. No actual far
   endpoint cap or Nash status is inferred.

4. Every root-only-cap supplier has zero individual debt under its
   own supported reset and therefore is originally pure at its
   unique root cap. Every later-cap supplier has positive debt from
   its suboptimal positive root atom. With every OTHER root supplier
   algebraically reset to root, its own late prescribed branch and
   its selected later cap see the SAME passive root coalition. Thus
   d_h=a_h d_h, giving ORIGINAL a_h=1. A redundant a_h=1 is handled
   directly; no zero-mass conditional is defined. A sole supplier is
   excluded by U_h=s_h and the prescribed margin. Therefore no-bridge
   would force the actual original prescribed outcome to be a pure
   root coalition, contradicting the hypothesized random outcome.

The cap box genuinely handles multiple later cap points, including
points with identical kernels. The only contradiction is against
the missing ROOT-to-later bridge, not point multiplicity alone.

### Positive-event PAYOFF-kernel distinction and finite witnesses

For a bridging owner i, its root cap exceeds s_i by the true global
singleton margin. Without any opponent root mass its root response
would equal s_i, so there is positive probability of a nonempty
opponent root coalition S. On that event, with no earlier exit, the
root deviation gives S∪{i} and EVERY later deviation gives S. These
are two nonempty coalitions; row genericity applies to them directly
and gives r_i(S∪{i})≠r_i(S). Finitely many S imply at least one
event has strictly positive probability. Equality of the two caps'
EXPECTED values does not invalidate their pointwise difference.

For original finite witnesses, root atom and through-root masses
converge by retained interval endpoint tests. The exact event with
members S at the retained n_k and all other opponents later has
probability tending to the positive limit. A fixed later compact
test has original σ_k>n_k eventually, since its limiting point is
strictly larger than the isolated τ; Never is literal Never. The
two finite responses give the SAME two different fixed reward
coordinates on that event. No limit-born response or artificial
nonisolated atom supplies the distinction. The change in absorbing
decision date does not alter terminal or uniform asymptotic reward
semantics.

### Minimal exact failures and consumer boundary

The complete participant-indicator table with half root/half Never
laws has random outcomes and root-only caps with D=2, but its TRUE
global infimum0 permits descent. It falsifies replacing the global
positive minimum by positive profile debt. The complete constant-one
table with one sure root owner has random coalitions and tied root/
later response POINTS with different coalition kernels, but payoff
kernels are identically1. Its global gap0 and nongeneric rows make
it a precise countertest to the unconditional payoff-kernel upgrade.

The repeated-root ledger was checked algebraically: simultaneous
root/later cap ties make the row exact Nash against the OLD suffix
CAP vector b, and D=cΣ(b−u). They do not make it Nash against u
or preserve those ties after prefixing the same row again. The named
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`,
`quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`
in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean` require exact
cap-Nash against the executable suffix caps. The same file's
`exists_quittingCapNashRootStack` DOES produce a finite stack over ANY
executable terminal continuation and ANY finite depth, without a
supplied Nash premise. It supplies neither an absorbing stack nor
invariance of a repeatedly used fixed root. BG does not invent a
scaling hypothesis or infer absorption from finite stack existence.

The real increment is exclusion of the ONLY-late-plateau multiplicity
source when outcomes are random. Combining with SA at the compatible
fresh table gives a genuine first-root-versus-later payoff-kernel tie
at EVERY produced minimum. It gives no positive bridge-owner debt,
automatic independent finite-amplitude repair, debt-support rank drop,
distinctness of every cap kernel, or full Fin4 UE. Subject to those
explicit boundaries, the complete BG argument has no unresolved gap.

## Independent SG1–SG5 end-Never graft falsification

Target: the section from `### SG1. Exact global end-graft question and
status` through SG5/EOF in
`../notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`, exact SHA256
`9e7cb53849007feea9c83c3cd0e05199a56adc646851cdfe9415d135df14b07f`.
I read the whole section and reconstructed its actual finite witnesses.
I did not read another SG review. I contributed the earlier NP source;
that source is not self-certified here. SG's appended-tail argument and
its Γ application are BROUWER's distinct inference checked below.

Verdict: PASS as ordinary mathematics, with a genuine additional source
restriction. No unresolved mathematical objection. This is not a UE
consumer or an assertion that the paid root bridger owns the final cap.

### Exact unrestricted graft and both carrier domains

For an original finite approximant with last finite support L, retaining
EVERY old finite atom and putting the tail at L+2 has the stated ledger.
No response through L can see the new opponent draws. The old full
finite cap is represented among these responses and the empty date L+1:
all later old finite responses pay R_i+h_i s_i, and positive s_i makes
old Never smaller than that value. Thus retaining an empty date BEFORE
the tail is sufficient; the proof does not insert extra dates inside
the old supported chronology.

At any later response the all-opponent-old-Never cylinder has probability
h_i and carries the tail response. Its complement is already screened
by the old first finite opponent coalition and supplies exactly R_i.
This is true for literal Never as well as every finite deadline. The cap
is therefore max(B_i,R_i+h_i b_i), not a chosen lower bound. A full
behavioral replacement is covered by affinity in its complete stopping
law. Prescribed rewards change only on the all-player-old-Never cylinder,
giving U_i+νu_i. The owners use independent private branch replacements;
no shared random event or correlation is introduced.

All original U,B,R,n quantities converge in the marked chart, so this
entire pair is in the original full carrier. Finite approximation of an
arbitrary tail is uniform for ALL response caps by the same coupling
estimate; a diagonal realizes any v in K. For K_abs one may choose actual
absorbing tails throughout. If finite witnesses are desired, preserve a
Never-zero owner by moving its finite tail remainder to a finite cutoff,
rather than to Never. The total variation error tends to0 uniformly in
all tests. The graft then has joint Never mass0. Consequently the stronger
absorbing-domain floor really applies to every v in K_abs; it is not a
substitution of a different minimum for the original source.

Subtracting the old true minimum gives exactly

    Σ_i h_i[(b_i−κ_i)⁺−n_i u_i]≥0,
    κ_i=(B_i−R_i)/h_i≥s_i.

At the separated table its value is≥g on K_abs. The signs and factors
match ν=h_i n_i, and the original AllNever tail makes the expression0.

### Checked Γ producer and the sign of the finite tail

I read the complete tracked file
`UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`
under its displayed imports. The exact declaration
`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`
takes ONLY actual Fin4 no-UE and produces a simplex weight with strict
positive image under the actual receiver-row projective matrix. The
actual no-UE premise is supplied by the positive full gap. It does not
require the own-singleton vector e_m or an additional StandardQ witness.

I also read `quittingProjectiveLCPMatrix` and its definition in
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`:
Γ_ij=r_i({j})−s_i, not the transpose or its negative. Therefore the
first-order prescribed tail payoff is

    v_i=Σ_j z_j r_i({j})=s_i+(Γz)_i>0.

The strict sign uses this source's positive own singleton rewards.
For the finite tail with probabilities ρz_j, the singleton weight
error plus nonsingleton probability is bounded by2ρ², so the displayed
2Mρ² remainder is safe. Coupling each opponent with AllNever has total
changed probability≤ρ, uniformly over EVERY test. The old AllNever
full cap is s_i; hence |b_i(ρ)−s_i|≤2Mρ, including Never.

If all κ_i>s_i, one common sufficiently small positive ρ gives both
u_i>0 and b_i<κ_i for every owner. The strict inequalities hold on all
large original approximants. Their ACTUAL grafted caps are unchanged and
their debt tends to δ−νΣ_i u_i<δ. This is an actual contradiction to the
full all-law floor, not a derivative of a fixed cap or a selected tester.

Thus some κ_i=s_i. In the marked producer, V_i(c)=R_i+h_i s_i;
c is the final finite empty tester and has zero mixture/own mass. The
claimed maximizing end wall follows without raw-integer attainment.

### Independent exact full-cap regression

Complete sixty-entry table: own singleton1, every passive coordinate2,
every participant coordinate of a nonsingleton3. Old laws give each owner
mass1/2 at date0 and1/2 at Never. Direct exact independent enumeration
gives U_i=9/4, B_i=11/4, R_i=7/4, h_i=1/8 and κ_i=8.
The singleton Γ has diagonal0 and every off-diagonal entry1, so its
uniform simplex image is3/4>0. Use the one-date tail with quit rate1/4
for every owner: u_i=45/32 and b_i=69/32. Append it at date2 to the
old Never branches, retaining the empty date1. Its laws are exactly

    p_i(0)=1/2, p_i(2)=1/8, p_i(Never)=3/8.

Enumerating EVERY finite-response phase and Never gives
U_i'=1197/512 and B_i'=11/4, exactly the two graft equations. Total
debt falls from2 to211/128. The table itself is solved by pure all-Quit,
so this is not a positive-gap example. It specifically confirms why
positive profile debt cannot replace the true global-minimum premise.

### Exact source value and remaining limitations

NP's paid first-to-later bridge did not locate a maximizing last finite
tester. SG excludes the all-strict κ>s geometry at EVERY produced
positive-Never true minimum, using ONE actual whole-tail competitor. It
is a real additional source restriction, not an alias for point-count
or a conditional price supplied without an underlying profile.

At an end contact, the same positive tail can raise caps. The universal
budget prices this and gives no automatic consumer. The c-active owner
need not be the first-root bridger; not all owners must cap at c; c need
not be an attained raw natural deadline. No joint punishment, minimizing
tail, Nash continuation, renewable paid reset or UE is established. The
review does not add SG to the separately frozen NP standalone artifact.

## Independent strengthened CB1–CB5 review

Reviewed the complete bounded section beginning `## CB:` in
`notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`, SHA256
`e0fef9e1d10c29489c4a22da4914c97c2bfce3de3f2d98a79cfce9558e4eba0b`.
The frozen whole-note hash supplied for that section was
`8b32300a8d8a293bf565114b1731dbb561ae00ddc601394b6d7994ad43d11a3f`.
I read the complete proof and checker, rechecked the source and prefix
declarations below, and ran the bounded checker. This is an independent
ordinary-mathematical review, not a Lean verification or an export seal.

Soundness verdict: PASS. No unresolved mathematical objection.
Source significance: the positive-FIRST-ROOT-supplier localization is a
genuine further restriction relative to the accepted source and the
bounded existing finite-surplus accounting checked here. It consumes
neither source alternative and supplies no quantitative funding or UE
consumer. Export significance remains a separate operational decision.

### Exact statement and the role of the extra premise

Keep the actual SAME-table, least-literal-joint-Never canonical source
and its alternative II: one root/later tied owner i with root rate0,
and at least one different later-only owner. The claim is that SOME
owner k with positive prescribed FIRST root rate has

    γ_k = B_k − V_k(F_k) > 0,

where F_k is its ENTIRE prescribed finite conditional law. This is not
the unconditional finite surplus, which equals m_kγ_k; here m_k>0 for
every positive supplier. It does not assert regret at the zero-rate
bridger or at an arbitrary tail owner. The contradictory hypothesis
γ_k=0 is used ONLY for positive first-root suppliers.

Every first root has at least two positive nonsure suppliers. A positive
supplier cannot be later-only under this hypothesis: its root atom has
a strict positive full-cap loss. A root-only supplier cannot put positive
finite mass after the first root, since its ENTIRE later cap is strictly
below its root cap. These conclusions follow directly from integrating
the nonnegative pure-regret integrand; uniform root-versus-upper gaps
also prove them without any questionable pointwise inference under weak
clock convergence. The bridger i has root rate0. Counting four owners
therefore leaves EXACTLY two positive root-only suppliers ℓ,h, with
rates x₀,y₀∈(0,1), and one remaining zero-rate later-only owner j.
The conditional suffixes of ℓ,h are literal PureNever.

### The first affine path really rules out bridger finite mass

If i has finite mass m_i>0, preserve its ENTIRE old finite conditional
law and replace its whole law by zF_i+(1−z)Never near m_i. No clock is
introduced. Its own cap is independent of its own law. The caps of ℓ,h
stay at their root endpoints by their strict full upper gaps and the
uniform product-TV bound. In the suffix, owner j faces just one possibly
finite opponent, i, so every existing finite reply has value

    s_j + z f_j(t).

For z>0 its complete finite cap is s_j+z sup_t f_j(t), an affine function
even when the supremum is negative. Literal Never pays z r_j({i}); an
existing final empty response exceeds it by (1−z)s_j>0. The source's
strict later-only gap keeps j's root endpoint inactive in a two-sided
neighborhood. ALL four caps and ALL prescribed payoffs are thus affine
on this actual whole-law path.

Global minimality makes total debt constant locally. The augmented
carrier then gives the decisive contradiction without assuming γ_i=0:
increasing z strictly decreases ORIGINAL joint Never,
(1−z)∏_{k≠i}n_k, while retaining total debt δ. Therefore i is PureNever.
The source's final-empty c-active owner with positive finite mass cannot
be ℓ or h (their cap is root-only), nor i. It is j, so j's retained
finite mass satisfies 0<m<1. No finite-optimality premise for j is used.

### Literal moving calendars and the negative-L branch

The realization is legitimate on the original finite approximants.
After root normalization, censor only vanishing unwanted suffix mass
of ℓ,h and i to Never. Uniform product-TV control bounds prescribed
values AND every finite/Never response, independently of its moving
date. Keep the entire conditional finite law F_j and its original
calendar. Its first occupied suffix date, every later finite test, the
original final empty test, and Never all remain in the test set.
Before-root tests, if present before normalization, pay s_k plus a
vanishing error and remain uniformly below the old caps B_k>s_k in
the local parameter neighborhood. They are not silently replaced by
an unavailable pre-first-suffix date.

At each finite index the one-opponent formula is exact. Its bounded
four suprema L_k admit a convergent subsequence; cap errors remain
uniform in m on a compact subinterval of(0,1). Root prefixing is the
literal full-cap map, so every fixed nearby (x,y,m) has a realizing
sequence in the ORIGINAL augmented carrier. This argument needs no
attained raw infinite date and no joint lottery over profiles.

In particular L_i is NOT automatically nonnegative. For a direct
signed regression, let s_i=1, let j's entire finite law stop at the
first available suffix date, and put r_i({j})=0,
r_i({i,j})=−1. The available same-date reply has f_i=−2, all later
finite replies have f_i=−1, hence L_i=−1. The complete suffix cap is
1−m, while Never pays0. Inserting an earlier empty date would falsely
change L_i to0. CB's proof uses the correct L_i=−1. With instead
r_i({j})=1 and r_i({i,j})=0, the same calendar gives L_i=0, confirming
the separate zero branch. Both examples preserve the final empty
reply rather than creating a pre-tail response.

### Independent tie-surface algebra

Write c=(1−x)(1−y),

    W=Q_i−A_i−c s_i,
    U_k=R_k⁰+c m r_k({j}),
    B_j=A_j+c s_j,
    B_i=max(Q_i,A_i+c[s_i+mL_i]).

The other caps are Q_ℓ,Q_h locally. The root polynomials Q,A,R⁰ and
c are multiaffine; W(0,0)=0 because Q_i(0,0)=s_i and A_i(0,0)=0.
These are all coordinates of the same literal semantic pair.

If L_i=0, changing m locally leaves every cap fixed and makes every
payoff affine. Total debt is again constant at its interior minimum,
while c(1−m) strictly falls. This contradicts least ORIGINAL Never.
No division by L_i is made.

If L_i≠0, the exact tie is m=W/(cL_i). Since the original c>0 and
0<m<1, this is feasible on an open rectangle about the actual root.
The complete true debt there is exactly

    P=Q_i+Q_ℓ+Q_h+A_j+c s_j−Σ_k R_k⁰−(S_j/L_i)W,
    S_j=Σ_k r_k({j}).

No sign of L_i or S_j is assumed. P is multiaffine and attains its
global minimum δ at an interior point. Its two first derivatives vanish;
a nonzero xy coefficient would then take both signs on centered
opposite quadrants. Thus P is constant and the entire local rectangle
consists of actual full minima.

The original joint Never on that surface is

    ν=c−W/L_i.

It too is multiaffine and attains its least value ν_min at an interior
point. The same argument makes it constant as a polynomial. Evaluating
THIS POLYNOMIAL IDENTITY at(0,0) gives ν_min=1, whereas the actual root
has x₀,y₀>0 and 0<m₀<1, so ν_min=c₀(1−m₀)<1. This proves the
contradiction using least Never alone. The alternative common-debt
argument is also correct: d_j=s_jν, and its polynomial identity at
(0,0) conflicts with d_j=s_jν_min<s_j. Neither argument declares
(0,0,m(0,0)) a feasible source minimum.

### Named dependencies and bounded prior-overlap check

The actual source dependencies are `LEAST_NEVER_MULTIPLE_BRIDGE_SOURCE.md`,
its complete old-calendar response transport and admissible whole-law
variation, the root normalization, the c-active finite-owner conclusion,
and least LITERAL original Never selection. The exact production prefix
surface is `quittingTerminalSemanticPrefix`,
`quittingTerminalSemanticPair_rootThenContinuation`, and
`quittingTerminalSemanticPrefix_mem_carrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, read under
its displayed imports. Its cap coordinate is the max of root-Quit and
root-Continue using the own suffix cap, not a Nash continuation value.

The accepted packet already gives root/later RESPONSE contacts and a
final-empty c-active owner with positive finite mass. It does NOT put
suboptimal prescribed finite mass at a POSITIVE FIRST-ROOT supplier.
Those are distinct assertions. The bounded finite-surplus discussion
in `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` gives
d_k=γ_k^unconditional+n_k(B_k−R_k), and discusses zero-finite-surplus
chambers and conditional pricing; it explicitly does not exclude that
chamber or consume the source. Its later paid-finite coupled accounting
requires additional bridge/c-active and budget conditions. Neither
already supplies CB's first-root-supplier conclusion. The unrelated
sole-sure saturation sign test in the same note concerns a sure root
and is not this nonsure canonical alternative II.

The embedded exact checker passed all100 actual calendars, including
40 negative-L_i cases and92 nonzero-L_i polynomial cases. This supports
the algebra but is not the proof of carrier realization above.

Final scope: CB excludes precisely the submode in which every positive
first-root supplier has an optimal entire finite conditional. The paid
finite loss must occur either at a later-only owner's prescribed root,
or in a root-only supplier's after-root finite mass. It yields no
uniform numerical γ bound, no joint independent move whose benefit
exceeds induced cap costs, no absorbing strategy, and no UE. Both
canonical source alternatives remain unconsumed. No unresolved soundness
objection remains; a further operational use is still needed before
treating this supporting restriction as an equilibrium mechanism.

## Independent CS1–CS4 review

Reviewed the complete section `## CS:` through its frozen EOF in
`notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`, bounded SHA256
`c046551783bbcba26cd891946ac76d3610be446a4b218096e400bddf83b1e38e`.
The supplied whole-note SHA256 was
`88e35c15ea13011026be1d19ce9d79c991ed3d823d51b090615d66c9028cb446`.
I read the primary source packet and named prefix declarations, derived
the two-mass cap account independently, and ran the complete embedded
exact checker. This review is ordinary mathematics, not a Lean check.

Soundness verdict: PASS. No unresolved mathematical objection.
Significance: a further conditional restriction on the ACTUAL selected
alternative-II source, not a consumer of that alternative. It rules out
one sole-post-root-owner submode. It does not say all paid root suppliers
are root-only, produce another helpful joining sign, quantify funding,
or exclude either complete source alternative. No export recommendation
is inferred from this supporting restriction alone.

### Statement actually checked

Keep the SAME selected reward table, true full minimum δ, common debt
vector at EVERY full minimum, and least ORIGINAL joint-Never augmented
minimum supplied by `LEAST_NEVER_MULTIPLE_BRIDGE_SOURCE.md`. In its
alternative II there is exactly one root/later bridger i with a_i=0,
and at least one later-only owner. Suppose a positive root-only supplier
k has positive finite mass f_k after the retained root. Then some OTHER
owner must also have positive prescribed finite mass after that root.

The contradictory submode fixes every other whole law to
a_h δ_root+(1−a_h)Never and varies only k's independent private law

    a δ_root+f F+(1−a−f)Never,

where F is its ENTIRE existing post-root finite conditional. The original
point satisfies a>0, f>0, 1−a−f>0. No finite-best-reply premise is used;
a later-only owner is allowed positive, suboptimal prescribed root mass.
No common random signal or unsupported replacement clock is introduced.

### All-cap affineness, including signed and nonisolated envelopes

Let C=∏[h≠k](1−a_h) and C_h=∏[ℓ≠h,k](1−a_ℓ). For h≠k every existing
finite suffix response against k's conditional finite mass m=f/(1−a)
has value s_h+m[V_h(t;F)−s_h]. Because m>0, the ENTIRE finite envelope
is s_h+mL_h, with L_h the supremum over the unchanged full finite
calendar. This remains true for L_h<0 and L_h=0; multiplication by a
positive scalar preserves all orderings and all multiple/nonisolated
maximizing families. An empty date before the first F atom is NOT needed
and must not be inserted.

Literal suffix Never pays m r_h({k}). At every finite realizing index
the old final empty test pays this plus (1−m)s_h. Its strictly positive
margin persists locally because both own rewards and k's Never mass
are positive. Thus the all-behavior suffix cap is the finite envelope,
not the maximum with an unaccounted Never branch. Affinity in the
deviator's whole stopping law gives unrestricted behavioral coverage.

Root survival for responder h is (1−a)C_h, so the conditional fraction
cancels EXACTLY:

    T_h=A_h(a)+C_h[(1−a)s_h+f L_h],
    B_h=max(Q_h(a),T_h).

Root Q_h and A_h are affine in a. For own k the opponents are fixed;
the suffix cap is s_k, and root-only strictness gives

    B_k=Q_k,
    G_k=Q_k−A_k−C s_k>0.

The prescribed account is U_h=R_h⁰(a)+C f r_h({k}) for EVERY h,
including k. Indeed surviving finite absorption by k has unconditional
probability C f, regardless of F's internal calendar. In particular
U_k=aQ_k+(1−a)A_k+C f s_k. No quotient remains in these whole-law
coordinates. This is why the two-mass parameterization works even if
some later-only observer has a positive root rate.

All nonbridgers have strict numerical root-versus-ENTIRE-later gaps.
They persist on a small legal box by the uniform response bound. One
affine branch therefore supplies each such full cap. Only i retains a
max of two affine branches. The argument assumes neither isolation of
a late maximizer nor a uniform gap within the late maximizing family.

### The line consists of original global minima

The source's Sections6–7 give uniform prescribed and ALL-response
transport on the original moving calendars. Under the contradictory
submode, unwanted post-root masses of other owners tend to zero and
may be censored to literal Never with vanishing product-TV error.
Normalize their convergent nonsure root masses but retain every old
occupied or empty suffix date. k's positive finite conditional has mass
bounded away from zero and remains an existing conditional at each
finite index. The two-mass changes are legal on one common small box
because its old root, post-root finite and Never masses are all positive.

At each index define L_h from the COMPLETE finite response set. Bounded
coefficients have a common convergent subsequence. All displayed affine
accounts then converge uniformly on the box; maxima of their two
branches converge too. Before-root tests removed in source Section15
pay s_h in the limit, strictly below the original B_h, and stay below
on a sufficiently small box. Never stays separate from the final empty
test. Thus every modified triple (U,B,ν) belongs to the SAME original
augmented carrier, with ν=C(1−a−f). No favorable minimizing suffix or
new pre-first-suffix response has been substituted.

Writing the true total debt locally as max(F_root,F_later) for two
affine functions, choose nonzero z perpendicular to their difference
gradient. Their difference vanishes at the original point, hence it
vanishes EXACTLY along the small two-sided z-line, even when the gradient
is zero. True debt is affine there and bounded below by δ. Its interior
minimum therefore makes it CONSTANT δ, not merely stationary to first
order. Every point on this line is an original full minimum.

If z_a+z_f≠0, one orientation reduces C(1−a−f), contradicting least
ORIGINAL ν. Otherwise z_f=−z_a and z_a≠0. Own cap Q_k is fixed, while
the derivative of U_k is z_aG_k≠0. Its debt changes between genuine
global minima, contradicting their supplied common individual debt
vector. These cases exhaust every nonzero z, with no sign assumption
on any L_h and no exceptional zero-envelope case.

### Exact dependencies, overlap and remaining use

The primary packet's Section5 supplies common individual debt at EVERY
minimum of this SAME final table; Sections6–7 supply old-law and complete
response transport; Sections15–16 supply literal root normalization,
strict nonbridger gaps and a zero-rate sole bridger; Section18 supplies
the augmented carrier and least ORIGINAL joint Never at that table.
The suffix is neither a minimum nor a Nash continuation.

I read `quittingTerminalSemanticPrefix`,
`quittingTerminalSemanticPair_rootThenContinuation`, and
`quittingTerminalSemanticPrefix_mem_carrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` under its
displayed imports. Their cap coordinate is exactly max(root-Quit,
root-Continue with the own suffix cap). They do not provide augmented
Never transport by themselves; the packet and the actual law formula
above supply that separate coordinate. Narrow sole-finite/root-only
searches in that file, `TerminalSemanticEqualityStratum.lean`,
`TerminalSemanticSoloCapThreshold.lean`, and the packet found no existing
statement of this CS exclusion.

The packet's c-active owner with positive ORIGINAL finite mass does not
already force a second post-root finite owner: that owner's finite mass
could be at the first root. Nor does CB already prove CS: CB supplies a
paid positive root supplier, but permits a later-only supplier with its
loss at the root, or a root-only supplier with paid later finite mass.
CS excludes precisely the latter supplier being the SOLE later finite
owner, using a new two-dimensional whole-law minimum line. It is a real
bounded refinement relative to these exact source statements, not a
global audit of all project consequences.

The embedded checker passed 100 exact all-clock sparse-suffix tables,
including 33 negative-L_i cases. It checks the full root/suffix/Never
account, not globality or carrier realization; those were checked by
the proof above. The next operational task remains a simultaneous legal
change of actual laws whose benefit exceeds every induced full-cap
cost. CS supplies neither that move nor a quantitative margin. Both
canonical source alternatives remain open.

## Bounded CT sign and boundary extension check

Reviewed `## CT:` through its frozen EOF, SHA256
`6dbb11d68e853e215cd312d5e511f90cf15527341ad91109cdaed0bde1ea2bf9`.
This is a bounded extension check reusing the complete CS carrier and
all-cap review, not a third transport audit or an export seal.

Verdict: PASS, no unresolved sign or boundary objection. The restriction
now reads: if exactly ONE owner k has positive prescribed finite mass
after the root in the selected source II, then its root rate a_k is0.
To contradict a_k>0, k is a nonbridger because the sole bridger's root
rate is0. Hence G_k=Q_k−A_k−C s_k is NONZERO, not necessarily positive.
Its own full cap max(Q_k,A_k+C s_k) is constant under its private law
changes in BOTH signs. All other affine cap formulas and the max-of-two
total debt from CS remain unchanged. The least-Never-preserving line
has z_f=−z_a and z_a≠0, so its own payoff derivative z_aG_k and its
own debt derivative −z_aG_k are nonzero even for later-only k.
That contradicts common debt just as in CS. Positivity of root mass,
late finite mass and Never mass makes the signed box legal; no such
motion is claimed on the surviving a_k=0 boundary.

The bounded CB corollary also follows. With at most one future finite
owner, every positive root supplier has no future finite mass by CT
(or vacuously when there is none). Its entire finite conditional is
then its root atom. A root-only supplier would have zero finite regret,
so CB's paid positive supplier must instead be later-only. If there is
a unique future owner, its zero root rate makes it distinct from that
paid supplier. This locates a bad-root submode; it does not consume it.
Zero-future and sole-zero-root-future modes remain possible under these
statements, as do both full canonical source alternatives. No funding
bound or UE consumer is supplied.

## Bounded CU zero-root amount extension check

Reviewed `## CU:` through its frozen EOF, SHA256
`0e1fb001a00950a9ed89d50405ead0d4c2ea7ffd6196522a76926fa01296cb65`.
Verdict: PASS, no unresolved boundary or sign objection. This is a short
extension check reusing CS's all-clock original-carrier proof.

If the unsupported sole bridger i alone has positive post-root finite
mass, its finite amount m and Never amount1−m are both positive. Varying
these TWO existing categories is legal on a two-sided interval even
though its fixed root rate is0. No root-rate boundary motion is used.
Its own full cap is constant because its opponents are unchanged and
are all Never in the conditional suffix. EVERY other owner is a
nonbridger and faces just i's old finite conditional F in that suffix;
its ENTIRE finite envelope is s_h+mL_h for any signed L_h, with Never
strictly dominated by the old final empty tester. Strict root/later
numerical gaps fix one affine branch locally. Thus all full caps and
prescribed payoffs are affine in m. Original global minimality makes
an exact interval of full minima, and increasing m strictly lowers
ORIGINAL ν=C(1−m). Least Never contradicts this. Common debt is not
needed. Old calendar transport is the reviewed CS construction; no
pre-first-suffix date, favorable suffix or new response clock is added.

CT plus CU therefore leaves a sole future owner k with root rate0 and
k≠i. In that mode i is literal PureNever. The primary source packet's
Section9 explicitly supplies at least TWO positive first-root suppliers.
Neither i nor k can be one, so the other two labels are exactly those
two nonsure suppliers, with no future finite mass. CB implies at least
one is later-only, since a root-only supplier's entire prescribed finite
law would now be its root best reply. The classification of k remains
ROOT-ONLY OR LATER-ONLY; zero prescribed root mass imposes no strategic
label. Neither this argument nor CT excludes the zero-future mode.
Both full source alternatives and the retained bad-root branch remain
open, with no quantitative coupled-law funding or UE consumer.

## Bounded CW actual geometric-minimum adapter check

Reviewed `## CW: actual sparse minima admit geometric whole-conditional
replacement` through its frozen EOF, SHA256
`49fe9491e3a579c8fef534e724dbbb5d7e75b8d246490deaf17e73f559fc9a11`.
Verdict: PASS, no unresolved source-realization or bridge-retention gap.
This checks the actual sparse-source adapter; generic geometric cap
domination is already supplied by a named source declaration. Neither
full source alternative is consumed and no new generic theorem/export
or numerical funding statement is inferred.

The input is the SAME table and minimum in the reviewed CT/CU one-future
mode: i PureNever, zero-root future owner k≠i with finite mass f∈(0,1),
and the other two owners having positive nonsure prescribed laws whose
finite mass is exclusively at the root. Their caps need not be root-only.
k's strategic cap label remains root-only OR later-only. The
primary packet's original actual realizing sequence may be normalized
and censored exactly as described: only masses whose limits are0 move
to Never, root probabilities converge to their fixed nonsure limits,
and uniform product-TV bounds control prescribed payoffs AND every
behavioral response. Thus the resulting opponents of k really are
date0/Never laws at each sufficiently late finite index, not an abstract
semantic pair standing in for opponent laws.

I read `GeometricPivotCapDomination.lean` in full under its displayed
imports, including `exists_geometric_pivot_payoff_eq_and_caps_le`,
`quittingTerminalPayoff_geometric_pivot_late_response_eq_affine`, and
`quittingTerminalPayoff_geometric_pivot_eq`. With deadline1 these actual
opponent laws satisfy its finite-head premise. k's late-finite mass is
bounded away from0, so the selected first positive late-atom/finite-mass
ratio z_N belongs to(0,1]. The theorem preserves EVERY payoff and k's
literal Never atom, and bounds all full response caps, including all
new geometric dates and signed late limits. The new conditional need
not preserve the old occupied calendar; the actual all-deadline theorem
is what prices that change. It does not create an unpriced empty reply
before its first suffix date1.

For each nonpivot observer, all geometric finite replies interpolate
between coefficients zP_h and Γ_h, so the full finite supremum is
max(zP_h,Γ_h). Never is below the limiting late finite value by the
strict positive amount(1−f)s_h. Own k cap is fixed. These statements
are valid for negative or zero coefficients and for an unattained late
limit. Taking z_N→0 changes the cap formula to max(0,Γ_h), NOT to the
cap of an actual Never conditional. Positive finite mass f persists
at EVERY realizing index. Proper geometric tails can be censored to
a sufficiently late FINITE atom with vanishing TV cap error, keeping
Never exactly fixed; uniform finite words give the same zero-hazard
endpoint, with all-test error O(M/N). Hence the displayed triple belongs
to the ORIGINAL augmented carrier, with ν=C(1−f)=ν_min.

Coordinatewise full-cap domination gives B_geo≤B* and prescribed U_geo=U*.
Original globality gives D_geo≥δ; summing the cap comparison gives
D_geo≤δ. Their equality forces EVERY nonnegative cap decrement to0,
so the full pair and original Never coordinate are unchanged. This
argument needs the true all-law floor and does not mistakenly assign
δ to a suffix or assume common debt to recover coordinate equality.

Crucially, cap equality alone does NOT preserve i's later branch. CW3
repairs that correctly with the universal source theorem. Original
root-only nonbridgers keep their strict numerical gaps because their
root endpoints stay fixed and later envelopes cannot increase. Original
later-only owners keep the same later branch because cap equality and
their strict original gaps force it; k's own gap is wholly independent
of its own law. Thus no other label becomes a root/later bridger.

The resulting finite realizing sequence is at this SAME row-generic
table, realizes an ORIGINAL full minimum, retains positive marginal
Never, and still has prescribed first-root atoms of p,q at literal0.
i's full cap remains its unchanged Q_i there, so that root is the
earliest full maximizing point of every reconstructed marked minimum.
There is no earlier raw finite date; all later response tests have been
priced by the full-cap formula and retained compactification. Primary
packet Sections6–9 explicitly apply to ANY finite-law full-minimum
sequence at this final table, not merely the original selected sequence.
Section10's bridge argument likewise uses only that produced marked
minimum, legal supported-root variations and common debts at EVERY
minimum. It therefore applies to THIS reconstructed sequence. If i's
later branch had fallen strictly below Q_i, it would have no first-root
bridger at all, contradicting that universal conclusion. The same sole
tie and strict nonbridger classification consequently survive. No
two-case property is assumed for an arbitrary unrelated prefix.

Bounded significance: an actual one-future source conditional may now
be chosen from a one-parameter geometric/diffuse family while retaining
the exact original full pair and sparse root geometry. This is useful
source-data compression, not outer-law Nash selection, a paid coupled
move, a full-II consumer, or a UE proof. The distinct positive supplier's
bad-root mass and all induced full-cap costs still require funding.

## Bounded CX coupled actual-source resultant check

Reviewed frozen `## CX: a coupled source-minimum box forces a two-row
resultant` through EOF, SHA256
`d3a3e1a7bf6aad59c83629756c530ffd6bb0fd0233c193beda780c0563534091`.
Verdict: ordinary mathematical PASS for the stated fixed-table necessity
AND compatible FRESH-source exclusion. No unresolved algebra, full-cap,
realization or generic-selection gap found. This is a bounded submode
restriction, not closure of alternative(II), a UE consumer or an export
recommendation. The argument is distinct from the reviewed CW generic
geometric replacement and its source adapter.

Exact scope: at the SAME CW one-future minimum, i is PureNever and the
sole bridger; k has zero root rate and finite amount f₀∈(0,1); p,q are
the two positive nonsure root/Never suppliers. The geometric conditional
has 0<z₀<1. q must be later-only with STRICT first-tail endpoint.
i must have a STRICT first or END tail endpoint, and p must be root-only
or later-only with one strict tail endpoint. k is root-only OR later-only,
with no inferred strategic label from its zero prescribed root rate.
Then the appropriate literal two-row resultant R^e vanishes. At a fresh
source avoiding the 48 nonzero polynomials, this precise configuration
cannot occur.

The coupled chart is genuinely open and independent. With w₀=f₀z₀>0,
its y=w₀(1−a), f=x/(1−a), z=y/x satisfies 0<y<x<1−a at the original
point and on a small two-sided (a,x) box. Thus q is an independent
root/Never law and k an independent proper-geometric/Never law at every
point. Fixing y/(1−a) does not introduce a public correlation signal.
The raw support begins at literal1; no new pre-first-suffix date is used.
I recomputed the prescribed first-coalition masses: {p} has a_p(1−a),
{q} has C_p a, {p,q} has a_p a, and {k} has C_p x. They give exactly
CX.4 for ALL four recipients and literal Never C_p(1−a−x).

The full caps use the SAME actual laws. Reading
`quittingTerminalPayoff_geometric_pivot_late_response_eq_affine`,
`quittingTerminalPayoff_geometric_pivot_eq`, and
`exists_geometric_pivot_payoff_eq_and_caps_le` in
UniformEquilibrium/Quitting/Terminal/GeometricPivotCapDomination.lean,
I independently expanded any finite suffix reply at1+n against k:

    V_h(1+n)=s_h+fΓ_h+f(1−z)^n(zP_h−Γ_h).

Thus its complete finite supremum is s_h+f max(zP_h,Γ_h), INCLUDING
negative and zero endpoint coefficients. Never is f r_h({k}), strictly
below the END supremum by (1−f)s_h>0. Incorporating root passive fields
gives exactly all three nonpivot formulas CX.6; k's own later cap is
A_k+C_p(1−a)s_k and is independent of its own law. All dates0,1+n,
the potentially unattained END, and literal Never are therefore priced.
This is not a check only of a displayed first response.

q's strict first branch gives the constant full cap
A_q^root+C_p(s_q+w₀P_q). Its root and END gaps persist. p's whole
root-only gap suffices even when its INACTIVE tail endpoints tie; if p
is later-only, its assumed strict endpoint selects an affine expression.
k's strict root/later gap follows from its nonbridger status and persists.
i alone retains a full max hinge. Its assumed strict tail endpoint makes
each of its two competing full branches affine. Consequently CX.8 really
is the TRUE D, not a frozen-test lower estimate.

Proper geometric profiles are actual unrestricted behavioral profiles.
Replacing their conditional tail beyond a sufficiently late date by a
FINITE last atom preserves f, all prescribed values and literal Never;
coupling bounds EVERY behavioral response by the vanishing tail-TV error.
On a small closed box z is bounded away from0, so this error can be made
uniform. Each point belongs to the SAME original augmented carrier. The
true minimum floor therefore applies, even though no suffix minimum or
stationary-Nash claim is supplied.

For an actual max of two affine functions at an INTERIOR global minimum,
CX3 correctly produces a two-sided TRUE-minimum line: either both affine
branches coincide identically (then the full box is minimum), or the
kernel of their nonzero difference is a tie line on which the remaining
affine value is minimized internally, hence constant. The first case
contradicts least original Never immediately. In the second, least ν
forces its direction to be (1,−1) up to a nonzero scalar. Only AFTER this
global argument may common individual debts be applied. Since q's full
cap is fixed, its U_q must be fixed, giving

    C_p(s_q−r_q({k}))+a_p(r_q({p,q})−r_q({p}))=0.

I expanded i's root-minus-base-tail field independently as

    a_pΔ_ip+a[−a_pΔ_ip+C_pΔ_iq+a_pΔ_ipq].

For the FIRST endpoint the exact tie holds over an a-interval and equals
C_p w₀(1−a)P_i. Adding its intercept and slope eliminates w₀P_i, giving
C_pΔ_iq+a_pΔ_ipq=0. This is an identity of affine polynomials; it does
NOT evaluate an actual law at the illegal endpoint a=1. For END the
tie-line derivative instead gives
C_p(Δ_iq+Γ_i)+a_p(Δ_ipq−Δ_ip)=0. Combining either identity with q's
using the displayed elimination formula proves R^e=0 without dividing by
A_q, B_q, A_i or B_i. Vanishing individual coefficients therefore cause
no lost boundary case. I reran the author's Fraction checker: PASS for
2000 exact endpoint/elimination identities. It is arithmetic evidence,
not a substitute for the preceding actual-source argument.

Fresh generic avoidance is compatible with the PRIMARY source packet,
not merely with an already selected numerical table. I re-read its
Sections5,6–10,18–19. Section5 genuinely permits an arbitrary small open
60-coordinate perturbation ball with positive owns and strict separated
gaps BEFORE row scaling and BEFORE all final minimizing sequences. The
derivative of each R^e in the independent coordinate r_i({i,q}) is −B_q,
a nonzero polynomial. Thus each zero set is closed with empty interior,
and the finite union of 48 sets and the row-equality hyperplanes can be
avoided inside that ball. Both row factors are linear in their recipient's
entries, so positive row scaling multiplies R^e by θ_iθ_q exactly.
Nonvanishing survives EVERY allowed positive regular scaling, while the
primary scalarization then supplies common debts at ALL genuine final
unweighted minima. Least-original-Never selection and CW follow only
afterward. No old minimum, law, cap or chronology is transported through
the new reward choice.

The narrow inspected source files/packet contain no existing two-row
resultant or this coupled cap-held source exclusion. Within-row reward
distinctions alone do not exclude this quadratic identity; CB's paid-root
necessity and CS/CT/CU's support restrictions likewise do not state it.
This is an additional ordinary FRESH-source submode restriction, subject
to the explicit endpoint assumptions—not an independent existence class.

The exclusions at the boundary are honest. At z=0 the chart loses an open
proper-hazard neighbourhood and uniform tail approximation; at z=1 its
strict y<x condition becomes a boundary. i's extra tail tie, or p's active
extra tie, introduces another hinge and invalidates the max-two-affines
step. q END-active or endpoint-tied does not have CX.7's held full cap.
These are NOT covered by the conclusion. A root-only p's inactive tie is
correctly allowed. Zero-future, multiple-future and case(I) modes remain
open; no quantitative paid move, full-II consumer or fixed UE target is
produced by this review.

## Bounded CY strict-END bridge extension check

Reviewed `## CY: the strict-END bridge submode is impossible at the original
source` through its frozen EOF, SHA256
`cb2bba19e4df128e72fbc03dedd7e10053e794b964f9cfac817f49ccc37efc87`.
Verdict: ordinary mathematical PASS, with exactly its stated proper-hazard,
strict-endpoint and source-rigidity hypotheses. This is a strengthening of
CX's END arm at the ORIGINAL same-table source, not another full audit or
complete sparse consumer.

Keeping root rates and finite amount f fixed, varying the entire proper
conditional F_z leaves EVERY prescribed coalition probability, the entire
payoff vector and literal joint Never fixed. The already reviewed complete
finite/END/Never formula applies on a genuine two-sided interval because
0<z₀<1. i's strictly END-active envelope is a constant, so its root/END
equality is a max of TWO constants, not a surviving variable hinge. k's own
cap is constant as well. q's later-only strict FIRST branch is affine with
nonzero slope H_q f P_q: both probability factors are positive and the
accepted within-row distinctions give P_q≠0, regardless of its sign. p's
ROOT-ONLY full gap fixes its cap even if its inactive tail endpoints tie;
if later-only, its stipulated strict endpoint fixes one affine cap branch.
Consequently TRUE D is affine locally. There are no omitted moving finite,
late supremum or Never replies in that assertion.

Global minimality makes that affine debt constant on the whole small
interval, not just zero to first order. Every point is a genuine full
minimum in the same augmented carrier. The common individual debts then
force each full cap to be constant because all prescribed values are
unchanged, contradicting q's nonzero slope. Finite proper-geometric
truncations retain literal Never and price all responses just as in CW/CX.
Least-Never itself is not used in this final contradiction; its role is only
in the inherited source input. No new generic polynomial avoidance or
reward perturbation is required.

Thus the END conclusion of the earlier CX review has this strictly shorter
same-table proof; it should not be counted twice as fresh-generic progress.
CX's FIRST-i resultant mechanism remains distinct. z=0/1, i's extra active
tail tie, p's active tail tie, or absence of a strict FIRST later-only
supplier are honestly outside CY. An inactive p tie remains allowed. No
zero-/multiple-future exclusion, general case(I)/(II) consumer, paid port or
fixed UE target is supplied.
