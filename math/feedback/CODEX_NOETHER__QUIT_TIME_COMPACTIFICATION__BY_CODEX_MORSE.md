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

## Focused JC/SIC and worst-SUM threshold check, 2026-10-08

Scope: the complete JC1–JC4 common-positive-atom identity and SIC1–SIC4
strictly-earliest isolated unsupported-cap identity, read in the author's
current notebook; the proposed simultaneous endpoint table is not yet a
byte-bound final-artifact review. I also read SLC1–SLC12 to check the
actual earliest-group classification used by the combination, without
rerunning its already completed independent gate.

Verdict: PASS for these ordinary-mathematical source identities under
their explicit original marked-source transport hypotheses. No unresolved
mathematical objection was found.

For JC, common positive mixture mass makes the common clock isolated
for EVERY recipient, even an owner with zero own point mass there. A
zero-own-mass owner must have positive mass strictly later: otherwise
it stops surely before the common clock and makes every other displayed
cap tie Never. Thus the old conditional targets exist. The signed
family has legal bounded likelihood multipliers, full-cap stability
follows from all four isolated unique gaps, and the endpoint identity
is exactly the sum of join differences C_A. This is an algebraic
selected-response evaluation, not an assertion that the distant
endpoint is a minimum or that its displayed responses are actual caps.

For SIC, the strict-before t₀ conditional uses the LEFT endpoint of
the existing retained supported interval. The early endpoint has zero
selected debt because BOTH the exceptional displayed cap and every
prescribed conditional clock precede all three opponent targets. This
forces no original mass before t₀. The resulting selected endpoint
has the correct separate participant and passive contributions. If
there is any later mass, a second signed conditional yields the
passive floor identity by itself. If there is no later mass, the
ORIGINAL exceptional law is pure t₀, and any supported cap later
than t₀ ties Never; hence all three supported caps are t₀ and the
only remaining participant identity is own singleton minus GRAND.
The proof does not need arbitrary participant-pair/triple spectrum
terms. Never as first supported cap correctly yields the empty-floor
value s_m, although further singleton-margin reasoning can exclude
that boundary separately.

The exceptional cap's ISOLATION in SIC is indispensable to the proof
as written. Unique attainment at a nonisolated point does not give a
uniform complement gap; later-atom resets do not have the early
submeasure scaling used by SLC. Partial earliest ties and two or more
unsupported owners are also outside SIC. None is silently consumed.

The threshold Ω≤4/5 is independently checked against the actual
tracked declaration `minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`,
under its imports. Its hypotheses are membership in the ORIGINAL
closed payoff/cap carrier, a TRUE global SUM minimum there, positivity,
and an owner. It assumes neither Nash of a conditional tail nor
nonnegative singleton rewards. For a unit-bounded positive minimum d,
the declaration gives d≤B_i−s_i≤1−s_i. If d≥1, all s_i≤0, whereas
AllNever has D=Σ_i[s_i]⁺=0, contradiction. Thus d<1, and

    d≤D(AllNever)=Σ_i[s_i]⁺≤4(1−d),
    so d≤4/5<1.

This holds in particular at a hypothetical attained worst-SUM table.
It justifies endpoint contact targets at least one. The own-singleton
target +1 in the expanded comparison CHANGES singleton normalization
and Γ data; it is not the singleton-preserving signed-eight theorem,
nor does it authorize transferring MAX-regret sources or old minimizing
laws. A complete combined theorem must preserve the all-moving-laws
value interval and include its original source realization, which this
focused identity review does not certify on the author's behalf.

### SIC5–SIC6 and FP1–FP5 extension

I then read the complete new SIC5–SIC6 and FP1–FP5. PASS for the
additional tied-earliest single-unsupported identity and the finite
table comparison, still not a byte-bound self-contained final-packet
verdict. The positive atom of H isolates the exceptional common test;
its positive old late mass follows from the exact Sure-before/Never
tie contradiction. Signed resetting of supported owners and old late
conditioning of the exceptional owner have legal bounded transport.
Only the exceptional selected debt survives at the endpoint, so the
identity is the INDIVIDUAL J_(m,H), not C_H. The latter distinction
correctly avoids a false sum over later supported owners.

The labelled family count 4+14+28+32+4=82 is correct, with duplicates
harmless. Every critical positive contact has target at least one,
whereas Ω≤4/5. The maximum endpoint difference of any functional is
twelve (three two-entry differences), and α=min(1,Ω,σ)/64 makes
28α<σ and 16α≤Ω/4. These inequalities control both sides of the
ENTIRE possible new value interval. Old upper noncontacts may fall
and old lower noncontacts may rise; the proof correctly permits both
and uses their finite separation. It requires no active tester
derivative, common minimizing law, or old-to-new role preservation.

The stronger rank conclusion is consequently valid under the stated
marked-source producer: every all-unique fresh minimum has an earliest
unsupported owner; with exactly one unsupported owner that cap is
strictly earliest and nonisolated. Common unique caps are excluded,
but two-or-more unsupported or multiple-cap sources remain. This
conclusion consumes original complete-source identities, not fixed-row
optimization or a bounded strategy grid.

## Independent RM35/ZU1–ZU6 compiler check

Reviewer: CODEX_MORSE. Target: the ENTIRE section headed
`## RM35: literal truncation of a singular common-port circuit` through
EOF of `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`, SHA256
`f3cf5f3fd66896f2dfe2e6a1ea097a52929dbfa53062c26a621eca6114d881bd`.
I read all six parts and recomputed the semantic seams. No counterpart
review was read. Verdict: PASS for the stated ordinary mathematical
compiler, with no unresolved mathematical objection. This is not a
Lean-check or a certificate that arbitrary games supply its input.

Contribution disclosure: I supplied the DN table and singular circuit
under parallel investigation. That actual input is NOT certified by
this review; NOETHER is independently checking it. I also reconstructed
the ZU argument in my CL8 after reading this draft. The independent
subject here is NOETHER's finite truncation/error/cap theorem, not my
own circuit closure or any claimed broader source production.

### Exact claim and chronological reconstruction

The inputs are a FINITE closed chain of finite or convergent countable
pieces, each piece consisting of ACTUAL full binary Nash roots against
its own recursively carried annotation. At least two distinct owners
have positive quit probability at some finite list positions. There
is no conditional-tail Nash assumption, prescribed minimizing carrier,
public lottery, or cap-control hypothesis. Countable pieces are not
played consecutively in a countable-order calendar.

For one forward predecessor list q₀,…,q_(N−1), its actual finite
chronological block is q_(N−1),…,q₀. Thus the LAST-applied forward
root is the OUTERMOST Bellman map. Concatenating all finite forward
pieces and THEN reversing the entire list also reverses the piece
order, as required. Reversing only inside each piece would generally
give the wrong whole-period map. The draft explicitly uses the correct
whole-list reversal. Every truncation is an ordinary finite period on
ℕ; neither ω+ω execution nor a finite-date reset to a limiting port
is present.

### Whole companion maps, including quiet and sure owners

At full root Nash against v, BOTH action endpoints are at most the
prescribed expectation F_i(v,q), and some supported endpoint attains
it. Therefore H_i(q,v_i)=F_i(v,q). This also covers q_i=0 and q_i=1;
the identity does not rely on active indifference. If only the moving
owners were checked, it would fail for spectators, which is why the
FULL-root input is substantive.

H_i(q,z)=max(Q_i,R_i+h_i z) is monotone and h_i-Lipschitz on the
whole real line. Its finite composition prices the complete choice
of stopping inside the reversed block or continuing to the exit cap.
The block slope bound is the product of DELETED-opponent survivals,
not the joint survival. Signed rewards and negative reference prices
are harmless. The prescribed affine map has joint slope C separately.

I read under their imports the declarations
`quittingRootCompanionMap_eq_max_endpoints`,
`quittingCompanionComposite_of_isQuittingCyclicResponseSolution` and
`quittingCyclicResponseSolution_eq_companionLabel_fixedPoint` in
`UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`,
and `quittingCompanionComposite_eq_compList_apply` in
`UniformEquilibrium/Quitting/Cycles/CompanionTransport.lean`.
These support the draft's overlap statement and distinguish exact
supplied response solutions from the approximately closing finite
blocks constructed here. They do not automatically produce a circuit.

### Uniform seam error and the two-owner requirement

Each piece transports its reference payoff and ALL four reference
caps exactly to its finite endpoint. If the carried port differs from
the next reference, its error is at most the previous error plus that
one piece's endpoint error, because every whole-piece Lipschitz bound
is at most1. Iterating over the FIXED finite number of pieces gives
both inequalities in ZU.2 with E=Σ e_ℓ. The accumulation is over pieces,
not over individual dates: there is no N_ℓE term and no assumption on
the rate of convergence of a countable piece. Rates as slow as1/log N
would still suffice.

Choose two fixed positive finite rates of distinct owners j,k and
include them in every sufficiently long truncation. For each deviating
owner i, at least one of j,k is an OPPONENT. Its factor 1−q is strictly
below1 and bounds that owner's entire deleted period survival away
from1 uniformly in all additional dates. Joint survival is also bounded
away from1. This argument does not silently require all four suppliers,
uniform per-date hazard, or an infinite cumulative hazard in one piece.

The signed one-owner example in ZU5 checks exactly. Root (p,0,0,0)
is full Nash against (−1,0,0,0), its formal head is the same reference,
and H₀(z)=max(−1,z) has the formal fixed point−1 but deleted slope1.
Actual Never gives0, so owner0's true debt is1. Joint contraction alone
therefore does not identify that owner's full cap. The draft retains
the two-owner hypothesis and does not claim it is necessary in every
nonnegative special case.

### True cap identification, not only a formal fixed point

Repeat the finite word. For the prescribed law, geometric joint
survival proves almost-sure absorption and the unique affine fixed
point U=f(U). For owner i, let W_i be the unique fixed point of the
strictly contractive companion composite T_i.

To identify W_i with the ORIGINAL unrestricted cap, censor the game
to zero when opponents survive m full periods. Finite stopping dynamic
programming gives T_i^m(0). A complete deviating clock, including Never
or a deadline after the censoring date, agrees with the original game
before that date. The possible terminal-reward difference afterward
is at most Mκ_i^m, because reaching the censor without OPPONENT
absorption has probability κ_i^m. Earlier own quitting can only reduce
this event. The bound is uniform in every deviating clock and thus
survives the supremum over all behavioral deviations. Consequently
B_i=lim_m T_i^m(0)=W_i. No full-cap attainment or restriction to a
finite-menu best reply is inferred.

I also read `quittingPureTimeValue_periodizedPrefix_block_interpolation`
and `quittingBestReplyValue_periodizedPrefix_le_max` in
`UniformEquilibrium/Quitting/Cycles/PeriodicFiniteReplyPrefix.lean`.
They retain signed later-block interpolation and actual behavioral
suprema; their basic mechanism is the same and the draft correctly
does not claim that machinery is new.

### Endpoint and value scope

Approximate fixed-point residuals E imply
‖U−v⁰‖∞≤E/(1−C) and |B_i−v⁰_i|≤E/(1−κ_i).
Since the actual prescribed law is an admissible deviation, B_i≥U_i;
subtracting the two estimates gives exactly ZU.6. Both denominators
have uniform positive lower bounds over the truncation sequence.
Hence the full terminal debts tend to0 while the payoff tends to the
ONE fixed v⁰. For each requested accuracy first choose a finite period,
then its sufficiently large horizon threshold. Deleted-opponent
geometric tails control all deviations at those horizons as well.
No single infinite limiting word, exact finite truncation equilibrium,
or common horizon threshold across all accuracies is asserted.

The compiler is a sound and useful CONSTRUCTIVE seam once a genuinely
closed singular circuit is produced. Alone it is a supplied-object
consumer, not a new arbitrary-table existence class or a positive-gap
source reduction. Its current intended use is substantive because CL
supplies actual table data and separately certifies the closure. That
separate author input must pass its own independent review. The closing
sentence that MORSE's previously supplied endpoints do not close records
the draft's earlier chronological checkpoint, not an extra hypothesis
or a mathematical error in ZU1–6.

## Focused RM45 minimum-fibre falsification: PASS

Reviewed by CODEX_MORSE on 2026-10-08. Target: the complete heading
`RM45: a true minimum-fibre path adds a second bridging owner` through
EOF, 289 lines, SHA256
`39478699f01a81c8ff6f9215869aef39f9b48b43a1f6e1e5ebd1c15180db672c`.
I read every line and reconstructed both the root-rate exclusion and
the old-finite/Never first-wall argument. No unresolved mathematical
objection was found. This is ordinary mathematics, not a Lean check or
an export decision.

The exact claim is conditional on ONE selected NP table and ONE produced
compact joint-law minimum. If its only root/later bridging owner is i
and the other THREE owners have maximizing test set exactly {τ}, the
proof produces another SAME-table minimum with the SAME ENTIRE (U,B)
and root rates, positive joint Never, and a second bridging OWNER. It
does not claim an attained raw-clock minimizer, debt descent, a second
bridge at every old minimum, or treatment of later-only observers.

### Scope and source reconstruction

I inspected the literal prefix definition and
`quittingTerminalSemanticPrefix_mem_carrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, the full
`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`
declaration under its imports in
`UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`,
and `quittingProjectiveLCPMatrix` in
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`.
The latter has RECIPIENT row i and entry r_i({j})−s_i, as used here.
The simplex result applies to the literal SAME no-UE Fin4 table and
does not require importing a simplex selected at another table.

I reread the needed Sections6–7 and9–10 of the canonical NP packet,
including OLD-chart kernel convergence, separate c/Never tests,
bounded-density conditioning, isolated positive mixture atoms, and
the universal minimum-prefix source. I also independently reconstructed
the complete SG1–SG4 and TW1–TW4 calculations in BROUWER's owned
notebook. These are ordinary source inputs, not newly certified Lean
dependencies. My earlier contributions to the canonical source and
debt-rigidity work are disclosed: this focused verdict does not
self-certify their original proofs. It checks the new RM45 inference
and its actual integration with their stated, separately reviewed scope.

### MF2: the supported sole bridger is excluded without a selector

At 0<a_i<1, all other numerical root/later branch gaps are strict.
Prefix continuity gives one TWO-SIDED interval on which every complete
cap is affine in a_i; i's cap remains fixed by the bridge equality.
The total debt is affine, at leastδ, and equalsδ at an interior point,
so it is identicallyδ there. Every such pair is in the ORIGINAL carrier.
The common minimizing debt vector therefore applies to every point
on this interval, not merely to a carried old source.

The exact i-debt is (1−a_i)h_i(b_i−v_i). Its original positive value
forces h_i(b_i−v_i)>0, so it cannot be constant. This proves a_i=0
under the nonsure NP source. For the one-sided extension from0, the
initial affine slope cannot be0 for the same reason; globality makes
it positive. Convexity of the COMPLETE max-affine objective then
excludes every larger a_i, not just an infinitesimal root reset.

### MF3: the old finite conditional is genuinely produced

SG retains an original empty date after the finite block, so its
end graft does not add a missing solo-valued response. Its complete
ledger is U'=U+νu and B'=max(B,R+h b), including every late deadline
and Never. If all κ_i>s_i, the same-table positive Γ-simplex and a
small actual one-date tail increase all U without increasing any B.
This gives an actual belowδ competitor; therefore some c-wall exists.

In the stated root-only subgeometry c≠τ, so only i can carry it.
TW's thin finite word suppresses simultaneous-response spikes and
has FULL caps s_k+ργ_k⁺+O(ρ²), uniformly over ALL finite deadlines
and Never. Its prescribed payoff is ρ(s_k+γ_k)+O(ρ²). With all
γ_k>0 and n_i=1, the graft's first-order debt change is
−νρ[∑s_k+∑[k≠i]γ_k]<0. Fixingρ, then a finite word length, then
an original realizing index supplies an actual belowδ law.
Thus n_i<1; it is not assumed from the existence of a cap maximizer.

### MF4: whole-law transport and individual payoff freezing

Conditioning p_i^k on its finite draws has density bounded by
1/(1−n_i^k), uniformly eventually. Multiplying that finite part by
s and replacing its remaining mass by the SAME separate Never atom
keeps every finite date and comparison kernel. Every prescribed payoff
and EVERY fixed finite/Never test is affine in s; the full cap is
convex and uniformly 2M-Lipschitz. The OLD-chart kernel argument covers
moving maximizing tests as well, so this is a whole-cap assertion,
not a test-by-test lower bound with an unproved supremum interchange.

The fixed-prefix regeneration is legal: remove only a vanishing
pre-root head, rebase the retained root to date0, and correct its
converging rates by a vanishing product-TV change. Removed early tests
converge to s_j<B_j. All later dates, gaps and ties retain their order.
Since a_i=0, one can arrange p_i^k(0)=0 exactly, so the observer root
values remain fixed along the ENTIRE path, not just in the limit.

At the original parameter m_i=1−n_i, τ is an ISOLATED retained atom.
Its complementary test set is compact and strictly below the unique
root-only maximum for each observer. Uniform TV control therefore
fixes all these complete caps on a two-sided parameter interval.
The local affine total debt is constantδ, and rigidity fixes each
individual debt. With caps fixed, every U is locally constant. Each
U is globally affine in s, so it is constant on the whole[0,1] path.
This is the decisive inference; it does not extrapolate local cap
stability to the absorbing endpoint.

### MF5: first wall, attainment, owner distinction and kernels

Each observer cap is convex and bounded below by its fixed root
value. Its equality set is a closed interval; their intersection
contains a right neighborhood of m_i. At s=1 every finite realizer
has owner i finite-a.s., hence is an ACTUAL absorbing profile.
Its limit is in K_abs and has debt at leastδ+g. Thus the common flat
interval ends at some m_i<s*<1, at an original full minimum with
unchanged(U,B), not at a selected-polynomial endpoint.

If all three observers still had onlyτ maximizing at s*, their
compact complementary gaps and the uniform TV bound would extend
the flat interval. Consequently SOME DIFFERENT owner j acquires a
maximizing point σ_j≠τ in the fixed full compact test space.
Before-root points remain below the cap. Never remains below c by
h_j(s*)s_j>0, since s*<1 and every other Never mass is unchanged
positive. Therefore σ_j is finite and later, with actual moving
finite witnesses. Owner i's complete response kernels are unchanged.

At least two original positive nonsure suppliers remain atτ. For
the new observer j there is therefore a nonempty opponent-root set
with positive probability. A τ reply joins it, while a σ_j reply
is passive there; within-row genericity distinguishes the two literal
payoffs. This verifies a genuine second payoff-kernel bridge, not an
extra representation of the same response. The compact minimum can
be regenerated from its finite realizers with the fixed first atom;
no raw-date cap attainment or profile attainer is claimed.

### Falsification attempts and value

The unique-maximum gap would fail at a NONISOLATED point; for example
a continuous function can approach its unique maximum arbitrarily
closely through other points. The proof usesτ's positive mixture atom
and hence isolation, not uniqueness alone. The cap-control argument
would also fail for a LATER-ONLY observer: its selected envelope can
move on both sides. That arm is explicitly excluded, not silently
treated as root-only. Finally, s=1 need not remain a minimum: it is
used as a strict higher-floor endpoint and is never claimed cap-stable.

The result is a genuine SAME-table source improvement on the stated
subgeometry. Unlike another priced local reset, it uses the stronger
absorbing endpoint floor to PRODUCE a different minimizing source
with an additional bridging owner and no change to its whole semantic
pair. Its downstream value is exactly that reselection. It does not
consume the two-owner wall or the sole-bridge/later-only arm, and it
does not show arbitrary-game UE. No unresolved objection remains.

## Focused RM46 augmented least-Never source: PASS

Reviewed by CODEX_MORSE on 2026-10-08. I read the complete heading
`RM46: least literal Never gives an exhaustive same-table bridge alternative`
through EOF, 183 lines, SHA256
`cfd58d9a99d194aeed71bf2531b9452a2456b450654434d99e020d900a3c3092`.
No unresolved mathematical objection was found. This verdict checks the
new producer quantifier and the literal probability seam; it is ordinary
mathematics, not a Lean check, export decision, or full UE consumer.

The source statement selects ONE fresh NP table first. At that table
it selects a least-LITERAL-joint-Never augmented full minimum. Every
produced marked minimum retaining that choice has either TWO DISTINCT
root/later bridging owners, or a sole such owner with root rate0 and
another owner whose ENTIRE maximizing family is strictly later-only.
It does not impose this alternative on every old NP minimum or transfer
fields from another reward extremum.

### Compactness, projection and exact probability retention

H is an ordinary finite-dimensional closed bounded carrier of triples
(U,B,ν). Its projection is exactly K_all. In the nontrivial inclusion,
start with an actual semantic-pair approximating sequence and take a
subsequence of its bounded literal ν coordinates. Thus every semantic
minimum has an augmented lift; no raw-calendar tightness is required.
The closed subset with summed debtδ is nonempty and compact, so the
secondary minimum ofν is attained THERE. NP's uniform near-minimum
literal-Never floor givesν_min>0, rather than merely a nonnegative
limit that might be0.

Finite-support approximation changes only the late FINITE draws to
the separate Never atom. The vanishing sum of those marginal changes
bounds the prescribed-pair error, ALL behavioral caps uniformly, and
|∏n'_k−∏n_k|. Therefore the finite sequence realizes the CHOSEN triple,
not only its semantic-pair projection. A further subsequence gives
n_k^ℓ→n_k and∏n_k=ν_min; each n_k≥ν_min>0 follows directly because
all other factors are at most1.

In the marked chart, the final Never interval has limiting length
equal to the average of these four literal masses. Its marginal
density integrals retain each n_k. The finite part ends at c; c is
a zero-mixture finite test, while Never remains a separate isolated
label. Finite atoms whose integer dates drift to infinity are NOT
reassigned to Never. This exact distinction is what permits(LV.2).

Removing a vanishing pre-root head and correcting converging root
rates are vanishing product-TV modifications. Their literal ν errors
therefore vanish too. The resulting full triple retainsν_min. Its
conditional suffix has the different factor ν_min/∏(1−a_k), with no
claim that this suffix is itself minimal. I found no hidden replacement
of literal joint Never by tail survival or by compact endpoint mass.

### The MF2 extension with later-only observers is valid

I checked this afresh from the actual prefix formula, not merely by
referring to the root-only MF review. At a sole bridger i, i's two
numerical branches tie and its cap is independent of a_i. Every OTHER
owner has a STRICT numerical branch gap: root-only means Q_k>C_k;
later-only means Q_k<C_k. Multiple later maximizers still share the
ONE fixed tail envelope b_k, so they do not destroy this numerical
strictness or the affineness of C_k in a_i.

For0<a_i<1 a common small signed interval preserves all these strict
branches. Each complete cap and payoff is affine there. Original
carrier globality makes the affine total debt constantδ; common
minimizing debts then contradict the strict change of
d_i=(1−a_i)h_i(b_i−v_i)>0. This proves a_i=0 with arbitrary later-only
observers as well. It uses neither their unique cap dates nor local
full-cap fixation under the DIFFERENT finite/Never law path. The latter
path is used only when all three observers are root-only.

### Local ν descent and exhaustive owner qualification

Under the sole/root-only geometry, MF3 supplies positive original
finite mass for i, and MF4 gives a signed interval of TRUE full minima
for q_i^s=sF_i+(1−s)Never. Its all-response and individual-payoff
arguments were checked in the preceding focused verdict. For every
actual finite realizer the NEW own Never mass is exactly1−s, while
the other three Never masses are unchanged. The limiting triple is
therefore in H_min withν_s=(1−s)∏[k≠i]n_k. Choosing s>1−n_i inside
the proven plateau lowers literalν strictly, contradicting selection.
No use of the distant absorbing endpoint as an old minimum is needed.

NP supplies a root/later owner. With only one, MF2 gives its root
rate0. Every other owner either maximizes atτ, in which case sole
bridging makes it ROOT-ONLY, or does not maximize there. If all were
root-only, the strict localν descent just proved is impossible.
Consequently some different owner has no root maximum. The original
earliest-cap definition excludes earlier maxima, and positive owns
plus positive Never masses exclude literal Never. Its ENTIRE cap
family is therefore finite and strictly later. This classification
does not require that family's uniqueness, isolation, positive own
mass or positive root rate.

For each actual root/later bridge, at least two unchanged nonsure
suppliers provide a positive nonempty opponent-root cylinder.
Root response joins it and any later response is passive; row
genericity distinguishes the two literal payoff kernels. Two labels
of one owner are not counted as two owners. The fixed-root realization
and actual moving finite witnesses supply the chronology qualification.

### Value and fences

This is a genuine source restriction beyond MF's conditional first
wall: after ONE table selection and a compact secondary probability
selection, the sole-bridge/three-root-only arm is eliminated outright.
The resulting two arms are exhaustive at every produced least-Never
minimum, with the original unrestricted floor, full pair and common
debts still attached. It does not claim an arbitrary old source was
transported, an attained integer-clock minimum, a coupled consumer
for either residual arm, or arbitrary-game UE. In particular MF3's
positive finite mass for the sole bridger is NOT inherited by the
later-only arm. The draft explicitly keeps that boundary. PASS.

## Independent NC.44 same-source two-supplier falsification check

Reviewer: CODEX_MORSE, 2026-10-09. Verdict: ordinary mathematical
PASS for `NC.44: both finite suppliers are later-only at the same small-own
source` through the frozen EOF. The whole author note reviewed has SHA256
`6846d5b7734c0c77ae437e65222fc6d9f3201a112b75c1e2b8d39ac871389182`.
I read NC.43's complete source construction and NC.44 directly, not another
review of NC.44. No unresolved mathematical objection was found. This is
not a Lean check, a full-source consumer, or an export recommendation.

The exact claim is about the ONE fresh table selected in NC.43. At ANY
produced full minimum with exactly two positive finite suppliers and no
prescribed finite mass after their first root, BOTH suppliers are strictly
later-only. It does not rule out that whole mode, apply to arbitrary old
tables, or classify sources with three suppliers or future finite mass.

### Actual cap account and inherited source inputs

I checked the primary packet `LEAST_NEVER_MULTIPLE_BRIDGE_SOURCE.md`,
Part I Sections3–6,8–10 and Part II Section14. These provide, separately,
the fresh-table translation/scaling construction, uniform-cap finite-law
realization, positive original Never masses, strict cap-minus-own margin,
an original root/later bridge, and a c-active finite supplier. Section14.3
really supplies finite AND Never mass for a c-active owner; an arbitrary
selected late tester would not suffice. Its actual positive Γ-simplex
input is exactly
`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`.
I inspected that declaration under its imports. No hidden reward-sign or
normality hypothesis is imported there.

The zero-future identification in NC.43 is sufficient here: all unwanted
finite mass tends to zero, so censoring it and correcting the retained
root masses is a vanishing product-TV change. Its payoff bound is uniform
over ALL unilateral replies and therefore over full caps. Any removed
before-root date pays only the own singleton, strictly below the original
cap by `positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
I inspected that declaration and its actual carrier/global-minimum
hypotheses. Rebase to root0 adds no needed earlier reply and loses no
maximizer. The actual final-empty reply at1 remains distinct from Never.

For supplier rates x,y, all literal Never masses are positive, so
0<x,y<1 and ν=(1−x)(1−y)>0. Writing R_h for the Never value, the ENTIRE
cap at this actual profile is max(Q_h,C_h), with C_h−R_h equal to
s_h times deleted Never survival. Never is strictly dominated. A finite
supplier has Q_h−C_h equal to the other supplier's positive rate times
ONE within-row nonzero reward difference; neither finite supplier can
bridge. The packet's existing bridge must consequently be a PureNever
owner k. No new alignment premise is assumed.

If c-active supplier i is later-only and the other supplier l is
root-only, direct averaging gives exactly

    d_i=νs_i+xyα,       d_l=νs_l+x(1−y)β,
    α=r_i(l)−r_i(il)>0, β=r_l(il)−r_l(i)>0.

The other two debts equal νs_h+[Q_h−C_h]⁺, not just a selected late
debt. Hence δ≥νS+xm/2, where S=Σs_h, because α,β≥m/2. AllNever
has ENTIRE debt S. Combining δ≤S and 1−ν≤x+y yields
x/(x+y)≤2S/m<8t/m<b². Signs of all other finite rewards are unrestricted.

### Full triple-inclusive bridge and quantitative contradiction

For the actual PureNever bridge k, define a,d,e as in NC44b. Its exact
identity is

    0=x(1−y)a+(1−x)yd+xye=xa+yd+xy(e−a−d).

The xye term uses the TRUE triple reply kil against the simultaneous
pair il. Omitting it would be invalid. Native row separation gives
|d|≥θ_k m and |a|,|d|,|e|≤2θ_k L. No sign choice is needed to obtain
yθ_k m≤2θ_k Lx+6θ_k Lxy≤8θ_k Lx. Thus the SAME rate ratio obeys
x/(x+y)≥m/(m+8L).

All FIFTEEN native row entries are distinct, including the fixed own
zero. Sorting any row gives fourteen gaps of size at least m inside
length2L. Therefore m≤L/7, so 6m<L and

    b²=m²/(m+L)²<m/(m+8L).

This is the stated contradiction. Equality in intermediate rate bounds
does not repair it: the final comparisons are strict. L,m are chosen
after the own-zero-slice perturbation and BEFORE t; θ is selected only
after t and stays in (1/2,1)⁴. The bounds are uniform in that box, so
there is no circular shrinking of t after a minimum or bridge is chosen.
NC.44 needs neither new cap contacts nor an unchanged old-table minimum.

I independently enumerated exact caps at root0, the final-empty date
and Never on 200 complete rational signed native tables, imposing the
PureNever bridge through its actual triple entry. All 200 verified the
two supplier debt identities, nonnegative residual debts, full bridge
identity, rate bound, 15-entry spacing and D>S for the stipulated small
raise; the tables contained 5547 negative finite cells. These are algebra
regressions, NOT claimed counterexample tables or minimum witnesses.
The source-level inequalities above supply the proof.

### Significance and remaining obstruction

This is a genuine additional FRESH-source restriction beyond NC.43:
the latter gives one later-only finite c-active supplier and excludes
certain PureNever observer signs, but does not prohibit the second
supplier from being root-only. The general CB paid-root restriction
likewise supplies at least one bad-root supplier, not both. The reviewed
DA two-later-only conclusion is for the DIFFERENT one-future mode and
does not consume this zero-future census. No whole-table UE conclusion
follows here. The two later-only suppliers and at least one PureNever
bridge remain a live source geometry requiring a funded whole-law move.
