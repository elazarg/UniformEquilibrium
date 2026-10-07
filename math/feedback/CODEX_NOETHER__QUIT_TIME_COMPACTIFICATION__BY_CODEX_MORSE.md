# Focused earliest-cutoff source review

Reviewer: CODEX_MORSE.

Additional focused verdict: the two-owner diffuse-endpoint argument below
passes at its stated scope. The stronger tracked quadratic cap margin in
fact excludes that entire branch, including the equal-advantage boundary;
the separate addendum records the exact source-to-contradiction argument.

## Exact scope and verdict

PASS for Section 73, “Actual earliest-cutoff tails have a punishment
canonical form”, in
`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`, extracted section
SHA256 `bab2fb7fdaeae69c299158ee7ef4f7ec8300e4d99d4af94b4626cde2d10f2ca0`.
No counterpart review was read. This checks the new ordinary mathematical
source reductions only, not the earlier notebook, an export, or Lean
verification of these exact statements. No unresolved mathematical
objection remains in the stated scope.

The conclusions are distinct: exact true-punishment canonicalization for
a cutoff owner's cap at the genuine sum-debt minimum; exclusion of the
shared earliest nonatomic endpoint when all Never caps are strictly
inactive and the nonempty social maximum is unique; and exact ghost-tail
erasure for a nonatomic cutoff owner with nonnegative own singleton.
None produces an unrestricted equilibrium or eliminates the remaining
binding-response/atomic-endpoint alternatives.

## Finite punishment replacement and limiting source

If z surely quits by d, all prescribed outcomes and every unilateral
experiment of a player other than z absorb by d. Replacing only the
opponents' conditional tails therefore preserves all targets and all
other complete caps exactly. The owner's cap separates as

    b_z=max(E_z,A_z+h_z C_z),

where C_z includes every conditional finite response and Never. When
h_z=0 the second term is A_z and no conditioning is needed. For h_z>0,
conditional independence follows from a product survival event.

True punishment is an infimum over actual opponent plans. Choosing a
near-optimal plan and censoring a sufficiently small finite late mass
to Never gives finite opponent laws whose ENTIRE response cap is at
most P_z+ε, with the tolerance allocated between selection and censoring.
The bounded product-coupling estimate is uniform over deviations. The
tail begins at d+1, so the continuation has exactly its original action
calendar and no artificially inserted pre-tail pure-Quit opportunity.

Consequently a positive gap above max(E_z,A_z+h_zP_z) gives an actual
strict total-debt decrease. Conversely P_z≤C_z supplies the lower bound.
This proves the finite canonical equality. It does not assume attainment
of punishment or turn the punishment into an on-path equilibrium.

For the represented minimum, the original approximants need not already
have a sure cutoff. Moving z's vanishing residual probability onto the
retained cut costs o(1) uniformly in every payoff and cap. At a positive
atom, the marked original date and its vector of masses converge; at a
nonatomic cut, both head masses and moving test kernels converge. Head
maximizers have no missing side limit: a positive atom is isolated in T,
and a nonatomic cut has no payoff jump. Thus E_z,A_z,h_z converge.
The punishment tolerance is fixed before the minimizing index is chosen.
A fixed alleged improvement beats both forcing error and minimum error.
This validates the exact equality at the actual limiting minimum; it
does not require a new general conditional-calendar transport theorem.

## Shared earliest diffuse endpoints

If at least two zero-Never marginals have the same earliest upper support
endpoint d and there is no mass at d, each player-deleted survival tends
to zero as t increases to d. All marginals still have positive survival
at every earlier cut, including those whose support continues beyond d.
Hence the fixed-cut complete-cap/social-max replacement checked in my
separate endpoint review applies with d in place of the calendar maximum.

The constant-winning-coalition argument remains valid in this extension.
For a coalition of size at least two, independent clocks equal almost
surely must be a common finite constant u. If u<d this contradicts
positive joint survival at u; if u≥d an earliest-endpoint player stops
strictly before d almost surely, so this cannot be the first coalition.
For a singleton winner, choose a distinct earliest-endpoint player and
a point u<d at which that player has positive earlier mass; the proposed
winner has positive later mass. Independence contradicts sure victory.
Clocks continuing past d are retained in all cap computations rather
than being discarded by an on-path-only argument.

## Exact ghost erasure and boundary tests

A nonatomic terminal support endpoint of z cannot carry another player's
positive atom: every positive represented atom is an isolated retained
point, incompatible with z's nonatomic support approaching that point.
Thus the literal d-test gives A_z+h_z s_z. With s_z≥0, true punishment
satisfies P_z≤s_z, so the canonical equality gives b_z=E_z. Replacing
every opponent's post-d clock by Never creates only the owner's late
finite value A_z+h_zs_z and Never value A_z, both ≤E_z. Other caps and
all targets remain exact because z still quits by d. This checks BOTH
complete-cap directions, not merely an upper estimate for the new tail.

If z uniquely minimizes the zero-Never support endpoints, every other
zero-Never player has positive mass beyond d. Erasure changes that mass
into Never. Existing positive-Never players retain positive Never mass.
The resulting source has exactly one zero-Never owner, all finite clocks
at or before d, and the same numerical global-minimum pair. The strict
owner Never buffer when s_z>0,h_z>0 is valid, but does not make the
solo-clipped late buffer strict.

Two adversarial scope tests are useful. First, an opponent who surely
quits at the first punishment date can give owner cap 0 when the owner's
singleton is 1 and its passive/joint rewards are 0. Inserting an empty
date BEFORE that punishment would expose value 1. The proof correctly
does not insert it. Second, take two players with owner rewards −1 at
its singleton and −2 at the other singleton and pair. Have the owner
stop at date 0 and the opponent at date 1. The owner's cap is −1, but
erasing the opponent's tail to Never raises that cap to 0. This confirms
why nonnegative own reward is essential to the erasure specialization;
the example is not alleged to be a positive global minimum.

## Exact source alignment

I inspected `quittingBestReplyValue`, `quittingPunishmentValue`,
`quittingPunishmentValue_le`, and `quittingPunishmentValue_le_max_solo`
in `UniformEquilibrium/Quitting/Stationary/MinMax.lean`. Their opponent
plans and deviations are unrestricted behavioral ones. The last bound
is P_z≤max(s_z,0), not punishment=singleton. The source uses it with
the stated nonnegative sign only.

The global sum-minimum moat comes from
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
The cited `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
produces a NEW no-UE table; `singlePivotSingletonTable_punishment_le_solo`
in `UniformEquilibrium/Quitting/Terminal/SinglePivotCanonicalConsequences.lean`
supplies its punishment comparison. Selecting a new minimum for that
new table is legitimate. No transport of the old minimum through an
additive reward normalization is asserted or used.

## Two-owner diffuse endpoint: focused independent check

PASS for “A two-owner diffuse endpoint forces an exact singleton equality”
through immediately before “Fixed-cut reachability”, extracted SHA256
`eb036b875d0abd6da7adc83b7d2e6b40ebbb10ad522db893760cf7613b7b2b87`.
No counterpart review was read. This is an ordinary mathematical verdict,
not a Lean check or an unrestricted UE conclusion. The original necessary
condition and limiting-pair calculation have no unresolved proof objection.
Their stated equal-advantage residual can, however, be consumed entirely by
an existing stronger source theorem, as shown below.

### Actual conditional minima and both complete-cap bounds

The source is a genuine global SUM-debt minimum of value δ>0, not a
positive-debt law or an orbit minimum. Ghost erasure at u's nonatomic
endpoint is legitimate by the nonnegative-own cutoff argument reviewed
above. It preserves the complete semantic pair and gives every outsider
positive Never mass. It leaves the two earliest owners finite almost
surely. The finite original approximants, rather than an abstract change
of conditional game, establish membership in the original carrier.

I checked the fixed-cut reachability argument directly. For each FIXED
t<d, all marginal survivals at t are positive. Each full small-prefix
erasure spends joint survival by a factor at most exp(−κ), whereas all
intermediate joint survivals remain at least the fixed positive R(t).
Thus finitely many erasures reach t. Cumulative conditioning is conditioning
the original finite realizers once at t; its denominators stay bounded
below by the original marginal survivals at this fixed t. There is no
asserted uniform number of steps as t increases to d.

For cuts t_m increasing to d, the outsiders' conditional finite mass e_m
tends to zero. Coupling them to Never changes EVERY prescribed payoff and
EVERY unilateral pure response by at most 2M e_m. The bound is uniform in
the pure tester, so it controls the full cap in both directions.

With outsiders at Never, the active owners' independent nonatomic clocks
do not tie. If θ_m is the probability that u is first, their targets are
s_u+(1−θ_m)a and s_v+θ_m b. A pure u response is a convex combination of
s_u and r_u({v}); the empty first suffix cut attains the former, and d
or Never attains the latter. The v calculation is symmetric. Hence the
complete caps converge to s_u+max(a,0), s_v+max(b,0). No dense-calendar
assumption or invented pre-atom response is used: all cuts here are
nonatomic, and both endpoint responses are in the retained test set.

The weak moat therefore gives a,b≥δ. After a subsequence, all payoffs
and caps converge to a pair in the closed original carrier with total
debt δ. The inspected declaration
`minimumTerminalSemantic_strictSingleton_of_punishmentNormal` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumLawFiniteAtom.lean`
does apply to this limit. True punishment is bounded by each nonnegative
own level through `quittingPunishmentValue_le_max_solo` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`. Thus θ=0 or θ=1
is impossible. The inequality δ≥θa+(1−θ)b then forces a=b=δ and zero
outsider debts, exactly as claimed. Positivity of each finite θ_m alone
would not justify this step; the proof correctly uses the actual limit
minimum and the strict source theorem.

The reward-perturbation discussion also has the correct quantifiers:
|D_*'−D_*|≤2|I|ζ, off-diagonal singleton perturbations preserve own signs,
and each new table receives its OWN minimum. No old-profile optimality
or additive-normalization ancestry is inferred.

### Stronger source consumes the equality boundary as well

I independently inspected
`positive_minimum_nonnegativeOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
Its hypotheses are original carrier membership, GLOBAL sum-debt
minimality, M>0 bounding every reward, positive minimum debt, and the
selected owner's nonnegative singleton. It internally produces its strict
preemptor; no preemption certificate or auxiliary Nash input is supplied.
At EACH genuine conditional minimum it gives

    b_u−s_u≥δ+γ,   b_v−s_v≥δ+γ,   γ=δ²/(8M)>0.

The complete-cap limits already established therefore yield
a,b≥δ+γ. For ANY subsequential θ∈[0,1], the two limiting debts sum to
θa+(1−θ)b. Nonnegative outsider debts now imply

    δ≥θa+(1−θ)b≥δ+γ,

a contradiction. Neither the positive-weight lemma nor a generic reward
perturbation is needed for this stronger conclusion. Thus under the
candidate's original nonnegative-own assumptions there is NO two-owner
diffuse earliest-endpoint minimum, even at a=b. This is a whole source
branch exclusion, not an improved bound on a surviving equality case.

For exactly four players the same file's
`positive_minimum_fourPlayer_allOwner_quadraticMargins` provides strict
cap margins without any own-sign assumption. That fact does not by
itself remove the nonnegative-own hypothesis from this ghost-erasure
proof: its earlier canonicalization still uses the cutoff owner's sign.
The stated proof above retains that hypothesis honestly.

## Strict margins force an original stage without a Never floor

Focused independent PASS for “Strict margins force an original coalition
stage without a Never floor”, ending immediately before the frozen
two-owner section, extracted SHA256
`0932bfaf49a3b85e1a39fe71b86350727dc40e6bb0de2bc072171fd5c53f52e0`.
No counterpart review was read. There is no unresolved objection in the
stated scope: Fin4 with arbitrary signed owns, or arbitrary finite players
with all owns nonnegative. This is ordinary mathematical source consumption,
not a Lean check or a uniform-equilibrium conclusion.

### The polynomial-axis identity is exact and uses the correct source

The selected nonatomic cut has 0<H≤δ/(4M), so all conditional denominators
are at least 1/2. The previously checked erasure theorem supplies two
DISTINCT facts: the future-branch multiaffine polynomial is constant on
the head-coordinate face, and the all-tail endpoint is an ACTUAL global
minimum with all caps retained. Neither fact alone would suffice.

On the axis for one original head owner i, that head quits alone before
all opponents. Thus its own contribution is B_i−[(1−z)V_i+z s_i], while
every other player's passive singleton contribution cancels between its
future cap and prescribed payoff. Summing gives exactly

    P(z e_i)=δ+z[(B_i−s_i)−δ].

This is an identity for the polynomial P. It does NOT identify the full
cap objective with P at the head-only vertex. Applying strict margins
only to the already established all-tail actual minimum is legitimate,
and contradicts constancy. No small-collision approximation or fictitious
new response date appears. All complete-cap finite transports are inherited
at one fixed nonatomic cut before taking its source limit.

### Reachability of a finite atom, including shared exhaustion

I checked the missing-Never cases separately. With all Never masses
positive, any marginal finite atom is reachable as a singleton. If none
exists, a nonzero small nonatomic head is available unless all laws are
Never; the latter is inconsistent with the strict minimum margin.

If some Never masses vanish, let d be the earliest terminal support
endpoint of such a player. At every earlier t all players have positive
strict survival past t. A marginal atom there therefore has a reachable
singleton stage. If no atom occurs at or before d, at least one earliest
owner has unit finite mass strictly before d. Its cumulative mass, along
with all other heads up to d, varies continuously from zero and must pass
through a positive value at most κ. A gap can be moved to its retained
endpoint without changing this mass. Thus the axis contradiction applies.

If the first useful atom is exactly at d, its retained point is isolated
in T. Every zero-Never owner with support maximum d then has positive
mass AT d; it cannot approach that isolated point diffusely. All other
players have positive strict survival past d. The product event that
exactly the earliest owners quit at d therefore has positive probability.
This handles two, three or all four simultaneous exhausted owners without
assuming any positive Never mass or deleting their actual cap tests.

### Original-date trace and all-profile quantifiers

At a retained atom its entire original interval converges with both
endpoints. Bounded likelihoods plus weak-* convergence therefore give
convergence both of each player's mass AT the original marked date and
of its strict-survival mass AFTER that date. The latter includes Never.
Their finite product is exactly the ORIGINAL first-coalition stage
probability, not a conditioned or counterfactually modified stage. The
reachability argument gives a strictly positive product even where some
Never masses are zero. It is important that the right interval endpoint,
not the retained midpoint, computes strict survival.

The failure of the claimed uniform near-minimum restriction supplies an
actual sequence with D≤δ+1/k and all stages below 1/k. A marked subsequence
with one positive original stage contradicts it. For infinite laws,
finite-tail censoring to Never preserves all earlier stage probabilities
EXACTLY and creates no new finite stage; uniform complete-cap coupling
keeps the sequence minimizing. Hence the conclusion concerns every actual
behavioral profile, with one fixed table and no Never-floor parameter.
It does not assert a bounded date or a singleton stage in the zero-Never
branch, and it does not convert terminal delivery to a claimed UE.

The named terminal-law atom and modified-singleton-target declarations
discussed above do not supply this whole-original-profile trace. The new
condition restricts every actual positive-gap minimizing sequence, rather
than merely adding an atom verifier. My separately developed atomic-cut
extension and first-collision strengthening in Sections 39–41 of
`../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md` are not used in this
PASS: this argument succeeds using only the already reviewed nonatomic
erasure theorem, and those stronger sections remain separately unreviewed.

## Independent review: quadratic triple incompatibility and TC6 coverage

Scoped artifact: the section “Quadratic triple incompatibility and a raw
strict-payoff consumer,” labels TC1–TC12, in the whole-note snapshot SHA256
`6b42b8b494d4b35ade3e231e7e14d9e050a928004ae8e87ddeaa59b13d8e35fc`.
This review checks the whole-clock product injection, the advertised
strict payoff deficit and uniform-payoff consumer, and actual implemented
producer overlap. No Lean build or kernel verification was performed.

Verdict: TC2–TC3 and TC7 are valid ordinary mathematics. The uniform-payoff
conclusion for TC6 is valid, but the ENTIRE raw class is already covered
by a stronger existing SINGLETON-ONLY producer. Pair/triple/grand rewards
and the new product inequality are unnecessary for its UE conclusion.
This is stronger overlap than the section's acknowledged exact raw-P
classifier. The sharp product inequality should be retained; TC6 must
not be presented as additional UE coverage.

### Ordered-copy injection and its probability coefficient

Write S={b,c,d}, T={a,c,d}, and take two independent ORDERED copies of
the same four-player independent clock profile. On the original event,
X_b=X_c=X_d=u<X_a and Y_a=Y_c=Y_d=v<Y_b, with u,v finite.
If u<v, exchanging just c gives pair {b,d} in X and singleton {c} in
Y, both at u. If u>v, it gives singleton {c} in X and pair {a,d} in
Y, both at v. If u=v, exchanging b gives pair {c,d} in X and grand
I in Y. A missing original clock may be Never; none of these comparisons
or first-outcome identities changes.

The three ORDERED image categories are disjoint. The same fixed swap
recovers every input within its indicated category, so the piecewise map
is globally injective. Each fixed coordinate swap preserves the product
measure because both copies use the SAME own marginal. One does not
need equal player marginals, finite support, or public randomization.
The event is countable and every branch measurable. The resulting bound
is precisely

    t_a t_b <= sigma_c (beta_bd+beta_ad)+chi beta_cd
              <= (sigma_c+chi)(beta_bd+beta_ad+beta_cd)
              <= e^2/4.

The two factors in the middle inequality enumerate disjoint finite
nontriple outcome sets. Their sum is at most e, without charging Never.
There is no missing factor of two: the domain has ordered probability
t_a t_b, not the union of its reversed outcome-pair event. The supplied
half-hazard a,b / sure c,d example attains equality. An independent
finite structural check on clocks {0,1,2,Never} gave 36 original ordered
pairs with 36 distinct images: 11 strict-before, 11 strict-after, and
14 equal-time inputs. This check is not the proof.

### Raw deficit and its consuming quantifiers

Assuming every U_i>=s_i-1/100 gives sum U>=24/25. The triple total
ceiling 8 and nontriple total ceiling -390 imply
e<=88/4875<1/50. The separate coordinate bound U_0<=4t+5e then yields
t>89/400 and m=max t_a>89/1600. For the three other triples, TC2 gives
sum t_b<12/2225. The omitted dominant-triple player's payoff satisfies

    U_a < -89/400+48/2225+1/10
         = -3593/35600 < -1/100 <= s_a-1/100.

All inequalities retain arbitrary additional negative entries and actual
Never probability. The contradiction proves the full actual-clock TC7,
not a bounded-menu statement. Fixing the selected owner on a convergent
subsequence gives a semantic limit coordinate <=s_i-1/100. The inspected
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`
instead makes every prescribed coordinate strictly above its singleton
at a positive GLOBAL SUM minimum, since every own debt is at most the
sum. Thus the stated zero-minimum/uniform-payoff argument is valid.

The actual alternative source definitions and consumers were also read:
`HasQuittingActualStrictSingletonDeficit`,
`hasQuittingFiniteCalendarRawStrictSingletonDeficit_iff_actual`, and
`hasQuittingFiniteCalendarRawStrictExclusion_iff_exists_positive_actual`
in `UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPredicates.lean`;
`exists_uniformEquilibriumPayoff_of_finFour_rawPayoffExclusion` and
`exists_finFour_finiteWord_exactLaws_of_rawPayoffExclusion` in
`UniformEquilibrium/Quitting/Paths/FinFourRawPayoffExclusionFiniteLaws.lean`;
and the exact strict-decision correctness declaration in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawStrictDecision.lean`.
They confirm the author's explicit raw-P overlap. The 1/400 reward
neighborhood costs at most 1/200 in payoff-minus-singleton and is valid,
including perturbations of zero singleton signs: its Fin4 consumer is
all-sign, not a silently translated old profile.

### Stronger whole-class overlap: only the singleton totals are needed

Here is the source-level retirement, valid for EVERY TC6 table, not only
TC12. Define the literal receiver-row matrix

    Gamma_ij=r_i({j})-s_i.

TC6 gives, in every column j,

    sum_i Gamma_ij = sum_i r_i({j})-sum_i s_i
                   <= -390-1 = -391 < 0.

For ANY nonnegative simplex lambda, therefore,

    sum_i (Gamma lambda)_i
       =sum_j lambda_j sum_i Gamma_ij <= -391 < 0.

In particular Gamma lambda cannot be strictly positive in every row.
But the exact already implemented declaration
`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`
produces precisely such a simplex from arbitrary Fin4 no-UE data, with
NO extra sign, punishment-normality, strategy, or reward-bound premise.
Its sibling
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`
is the ambient standard-Q source. The file's imports are
`MathUE.LinearProgramming.StandardQSimplexImage`,
`UniformEquilibrium.Quitting.Classification.LCP.CopositiveQBridge`,
`UniformEquilibrium.Quitting.Classification.LCP.FullNormalCoreHomogeneousTransfer`,
and
`UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination`.
I read the actual declarations under these imports, not a conference
paraphrase. The matrix orientation was separately checked against
`quittingProjectiveLCPMatrix` in
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`; it is exactly
Gamma above, not its transpose or its negative.

Consequently TC6's UE conclusion holds with ALL nonsingleton rewards
arbitrary. Even nonnegative singleton signs are unnecessary for this
specific singleton-only contradiction if the displayed column sum bound
is retained directly. TC12 has exact Gamma column sums
(-590,-591,-591,-591). It fails the existing all-outcome weighted floor
as claimed, but it satisfies this different singleton-only exclusion.
Failure of one linear screen cannot establish source noncoverage.

The complete TC12 table and every deterministic escape check are correct.
The boxed-charge failures are also literal: I and each triple are premium
traps; P_I({0,1})=8>0 and L_{012}({0})=195>0 violate their indicated
finite hypotheses in
`exports/BOXED_NASH_CHARGES_UNIFORM_EQUILIBRIUM.md`. Those comparisons do
not remove the whole-class singleton-source overlap proved above.

No mathematical objection remains to the sharp whole-law inequality or
the strict-deficit implication. A genuinely new UE class from this
mechanism must survive the ambient positive-simplex singleton condition
before imposing pair/triple/grand penalties. The two-copy map itself is
a probability proof, not an actual legal profile repair or correlation
device; that boundary is correctly stated by the author.
