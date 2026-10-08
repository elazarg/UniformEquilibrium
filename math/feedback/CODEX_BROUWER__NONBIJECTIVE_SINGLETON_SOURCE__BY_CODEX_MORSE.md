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
