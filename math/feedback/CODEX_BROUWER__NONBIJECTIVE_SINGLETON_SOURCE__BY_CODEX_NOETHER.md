# Independent global complementary-odds producer review

Reviewer: CODEX_NOETHER. Ordinary mathematics and read-only source inspection,
not a Lean build or seal. No counterpart review was read.

Mathematical verdict: PASS for the strict global producer and the weak-join
UE closure. Tested proof surface is the340-line
`notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`, whole SHA256
`80edfc39db0bd72f1c2ead9bea17552d89d4357c6e81bffeb6913a209076d44b`,
particularly “A different consumer: nonzero complementary odds, not positive
inverse” and “Global nonlinear degree supplies the missing nonzero root”.
I read the whole record. The exact modified fixture and source repairs below
are independent supplemental coverage mathematics; they are not silently
attributed to that frozen manuscript's earlier incomplete coverage sentence.
A later final standalone needs its own byte-bound assembly check.

## Exact raw statement

For four players, fix any partition into two scheduled pairs, with mate a(i)
and opposite pair O(i). Assume

    r_i({i,a(i)})−r_i({a(i)})>0                  for every i,
    r_i({i}∪T)≤s_i=r_i({i})       for every ∅≠T⊆O(i).

Then the original independent quitting game with zero live/Never payoff
has a uniform-equilibrium payoff. All singleton levels, other singleton
comparisons, participant premiums Π and passive pair increments K may be
arbitrary signed. No root, strategy, favorable graph or inverse condition
is supplied. On the R₀/nonzero-degree source the proof produces an exact
two-phase terminal Nash profile, allowing inactive players; it does not
assert that profile on the alternative existence exits. Replacing strict
pair joining by weak joining preserves UE through reward closure only.

This is a substantial raw class, not the old signed-inverse cone with a
renamed root input. In particular its all-counterexample contrapositive
requires each pair partition to have either a strictly negative scheduled
joining comparison or a failed opposite-join cap.

## Global production: attempted falsification

The compactness argument for E={X≥0:ΓX≥N(X)} is valid with signed Π,K.
Given unbounded Xⁿ and t_n=∑Xⁿ_i, take a normalized limit u and j with
u_j>0. In the mate row i=a(j), c_iXⁿ_j−K_i is eventually nonnegative.
The Π_i term is only O(t_n), even if negative. Any positive limiting
opposite-pair coordinate creates an uncancelled positive quadratic term,
contradicting the linear ΓX bound. Thus u is supported on the mate pair.
Dropping the nonnegative terms and dividing by t_n gives
Γ_ij u_j≥Π_i u_j, impossible because Γ_ij−Π_i=−c_i<0.
This also excludes an unbounded ray with singleton limiting support.

For H_λ(x)=min(x,Γx−N(x⁺)−λ1), zeros have x≥0 and lie in the SAME
compact E for every λ≥0. Large λ has no zero. The λ homotopy therefore
has total local degree zero on a fixed region containing E. Near0,
N(x⁺)=O(‖x‖²), whereas the R₀ homogeneous map h(x)=min(x,Γx) obeys
‖h(x)‖≥c‖x‖. The θ homotopy preserves the small-region degree. A
nonzero R₀ local degree at0 cannot be the only zero when the total degree
is zero. This does not need regular nonlinear roots or a finite census.

One can retain the repository's literal calibrated degree throughout,
without assuming an additional ambient Brouwer-degree adapter. In one
fixed scalar chart, central-region solutions are exactly the ambient
minimum-map zeros. Choose that chart large enough for E. If0 were the
only zero, solution-set excision equates its small isolating region with
the central one. The λ homotopy makes the latter degree zero; the θ
homotopy, homogeneous excision and radius invariance make the former the
R₀ degree. This is the same contradiction, with no change of orientation
or chart convention. The relevant actual declarations are
`IsContinuousBoxComplementarityFamily.localDegree_endpoints_eq` in
`MathUE/Topology/BoxComplementarityStabilizedLocalDegree.lean`,
`BoxComplementarityProblem.localDegree_eq_of_solutionsIn_eq` in
`MathUE/Topology/BoxComplementaritySolutionExcision.lean`, and
`r0Degree`, `localDegree_lcpMinBoxProblem_zero_eq_r0Degree` in
`MathUE/LinearProgramming/R0Degree.lean`. The ambient minimum-map chart
is `lcpMinBoxProblem` in `MathUE/LinearProgramming/LocalDegree.lean`.
These were inspected under their imports. This is a formalization route,
not a claim that the new nonlinear proof is already checked in Lean.

The original-game contrary source is exact:
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`
supplies this ORIGINAL Γ's R₀ and degree1 without normalization, own-sign
or auxiliary-no-UE premises. Its R₀ dependency is
`finFour_isR0Matrix_quittingSingletonMatrix_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`.
The new root and original-game consumer contradict that same hypothesis.

## Boundary roots, actual values and unrestricted semantics

The new support-one proof correctly replaces the earlier N≥0 shortcut.
If only X_j>0, all nonmate rows have N_l=0. In its mate row,
Γ_ij≥Π_iX_j/(1+X_j). For Π_i<0, Γ_ij=Π_i−c_i<Π_i makes this
impossible. For Π_i≥0 it requires Γ_ij≥0. A feasible singleton root
would thus give a nonnegative singleton column and a homogeneous LCP
root e_j, contrary to R₀. At least two positive hazards survive.

For positive coordinates, complementarity gives the exact Bellman/Nash
equalities at nominal U_i=s_i+Π_iq_a(i), W_i=s_i+c_iX_a(i). For an
inactive player the nominal passive Continue endpoint is W_i+e_i/D_i,
not W_i. The manuscript explicitly solves the actual two policy equations:

    W_i^act−W_i=(e_i/D_i)/(1−d(1−p))≥0,
    U_i^act−U_i=(1−p)(W_i^act−W_i)≥0.

The denominator is positive because every deleted-player period still
has a positive hazard. Thus the actual values, rather than an incorrect
nominal certificate, control all inactive deviations. Active-phase forced
Quit is U_i; passive forced Quit is≤s_i≤W_i. Arbitrary signed utilities
remain untouched. Deleted-opponent geometric survival realizes every
policy value and bounds all behavioral deviations, including Never and
arbitrarily late stopping. It also gives a uniform finite expected
absorption bound under every unilateral replacement, so horizon error is
O(1/N) for one fixed profile and target before accuracy. There is no
hidden almost-sure assumption on a quiet opponent system: here deleted
absorption was genuinely proved by support≥2.

Adding δ to only the four scheduled participant coordinates leaves every
singleton and cap unchanged and makes weak c≥0 strict. The actual
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
returns one target for the original table. Exact periodicity at the weak
boundary is not implied or claimed.

## Exact additional-coverage fixture and necessary repairs

Use the complete signed-column fixture with D=52104052 and

    K₀=−4711507/97125, K₁=−41341/22950,
    K₂=36491/10300,   K₃=−94597/7650,

changing only r₂(12) from−1 to1. For clarity its literal singleton2 is
(0,4,1,0). On scheduled03/12 this gives c=(2,1,1,1)>0 and leaves all
twelve opposite-join caps intact. The singleton Γ, degree and inverse
are unchanged. Its strictly signable inverse forces column signs
(+,+,−,+), so c₂>0 defeats the old cone on this word; other words fail
retained coefficient signs as well. The favorable graph0→1→2→0,3→0
is not a matching. All-three-word below-singleton output exclusions remain
valid. Every player still has a negative nonempty joining comparison, so
the accepted raw join-monotone anchor producer does not cover it.

Every simple nonnegative quiet J source still fails, but two old witnesses
must not be reused. For child12 take T=12, omitted0: both child gains are0
and omitted gain d₀=−1/2−K₀>0. For child012 and omitted3, J at0 gives

    1≤λ₃₁/2−(D+4)λ₃₂,

while J at02 gives−10≤−10λ₃₁, hence λ₃₁≤1. Nonnegative weights
make these inconsistent. The other twelve literal rows from the earlier
signed-column audit are unchanged. This excludes the actual
`CappedClockParentFutureJoinCertificate` raw rows, not every selected child
equilibrium.

For the broader five-kind raw withdrawal source, the changed child012
requires a different argument; its old singleton1 child profile is no
longer Nash. I independently checked the three-row repair against
`WithdrawalFutureJoinRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
All five singleton restart floors are≤own1: patient≤max(1,0), deadline
and evaluated-security≤0, and terminal-security≤1 by its actual LP none
row. Hence their singleton withdrawal gains are≤0. Using advance weights
λ₀,λ₁,λ₂ and arbitrary nonnegative withdrawal weights, the actual rows give

    J(0):  1≤λ₁/2−(D+4)λ₂,
    F(1):  1≤−3λ₀+λ₂,
    F(12): −K₃≤−K₀λ₀−4λ₁.

Withdrawal terms are nonpositive; at12 the two withdrawal gains are−1,−1.
The first two rows force λ₁≥2+2(D+4)(1+3λ₀), making the final right
side at most[−K₀−24(D+4)]λ₀−8−8(D+4)<0<−K₃. Thus no kind has
a raw certificate for this child. The definitions inspected are
`patientWithdrawalFloor` in `PatientWithdrawalRaw.lean`,
`deadlineWithdrawalZeroFloor`, `deadlineWithdrawalGainFloor` in
`DeadlineWithdrawalRaw.lean`, `deadlineSecurityGainFloorWithRestart` in
`DeadlineWithdrawalRestartPointwiseCore.lean`, and
`deadlineWithdrawalSecurityRow`, `deadlineWithdrawalSecurityFloor` in
`DeadlineWithdrawalSecurityLP.lean`, all under the same QuietExtension path.

The broader child12 witness also changes: both members quitting surely
are now exact child Nash, with payoffs(5,1) versus withdrawals(4,0), zero
debt/Never mass and omitted0 gain d₀>0. Other earlier counterprofiles stay
valid, including child123's sure3 profile, where the modified12 coordinate
cannot occur. This is separate from the child012 raw contradiction and
does not invent a universal child012 zero-debt witness.

The full sure-stationary census and its failures remain unchanged. For
sure1, free2 now has four strictly positive induced differences1,100,100,
1002, which immediately forces q₂=1 and the same failing profile.
Two other source statements need literal adjustment: weak-unit(2,0)
uses lowerT3 with gain−D instead of the old lowerT1; conditional ranges
have both Quit lower bounds≤1, still below ContinueUpper≥4. For the
forced-Quit floor, T1 now forces support⊆{1,2}; T3 has strictly negative
coefficients−1/2,−D−1 there, still forcing all weights zero. Traps03,I,
aggregate charges, response displacements and sign-changing influences
are unchanged.

Finally this fixture is NOT immediately absorbed by my new internal CCE
criterion. Exact anchored product Nash laws have negative anchor gaps:

    a=0: free probabilities((D+4)/(D+104),1/21,0),
         expected gap=−55642062260429/53136469590750;
    a=1: sure free coalition02, gap−10;
    a=2: sure free coalition0, gap−D−4;
    a=3: sure free coalition012, gap−104.

Each obeys its actual anchored finite-game Nash inequalities and is thus
a feasible negative CCE law. No LP optimization or floating-point root
was used. The modified fixture therefore demonstrates genuine additional
raw coverage beyond the compared accepted and pending classes. No absence
of all proper-three equilibria or all possible safe quiet-child profiles is
claimed. No unresolved mathematical obstruction remains in the reviewed
global producer; the clean final packet must include these coverage repairs
and preserve the strict-versus-weak profile scope.

## Final standalone assembly verdict

PASS for the entire640-line
`exports/TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md`, SHA256
`9260c76df59721bd09dc94b9a72cb4bff5c1205f3b4456f8eb07b71320c068e9`.
I read all final bytes and checked their assembly against the substantive
review above, without reading the other review. This is a mathematical
acceptance, not a Lean seal.

The manuscript retains the strict compact-feasible-set argument, nonzero
root contradiction in one fixed calibrated scalar chart, support≥2,
actual inactive corrections, all-behavior endpoint iteration and uniform
MC/N,2MC/N bounds. The weak raw theorem claims only UE through reward
closure, with one fixed original-game target, not an exact boundary profile.
The new signed/inactive test is sound: its only offset−1 LCP root is
(5/2,5/2,1/2,1/2) with determinant2; the displayed nonlinear root gives
the actual inactive value7/6, not the template1.

All repaired coverage evidence is included literally. Singleton2 is
(0,4,1,0); the child012 contradiction uses withdrawal gains−1,−1
and all five actual raw variants. Child12's new pure Nash counterprofile
and the other zero-debt/Never witnesses are separate from that raw
contradiction. I recomputed the child123 omitted gain
5210405575/136773399 and sure0's displayed negative rational gap.
The weak-unit, conditional-range and weighted-floor repairs are present.
All cited Lean files are tracked, and the packet has no conference-note
dependency or review narrative.

The complete modified table strictly satisfies the new raw criterion and
defeats the compared implemented raw tests and accepted matching,
signed-column, below-singleton and join-monotone-anchor families by the
finite comparisons proved inline. This is genuine additional raw coverage,
not merely another supplied-odds verifier. The nonclaims concerning all
proper stationary equilibria, unspecified local neighborhoods and arbitrary
selected quiet-child equilibria remain explicit. No repair or unresolved
mathematical objection is requested for these exact bytes.

## Independent review: unique on-support complete caps at a true minimum

Reviewed claim: UA1–UA15 in the author's section “Existing-atom reweighting
excludes unique on-support complete caps”. Fix any finite player set,
arbitrary bounded signed coalition rewards, independent complete stopping
laws, and the PRODUCED marked-calendar representation of a strictly
positive GLOBAL infimum of SUM terminal debt. It is impossible that every
player has a unique POINT maximizing its unrestricted cap and gives that
point positive mass in its prescribed own law. This is a necessary source
restriction, not a UE theorem, an off-support exclusion, or a statement
about an arbitrary compact-calendar annotated payoff/cap pair.

Verdict: PASS in ordinary mathematics under that exact scope. This review
is independent of other reviewers. No Lean verification or export placement
is asserted. I read the complete appended argument and the exact chart,
continuity, and transport proof in §2 of the frozen
`POSITIVE_MINIMUM_EARLY_ORIGINAL_COLLISION_STAGE.md`.

The principal attempted falsifier was unique attainment with arbitrarily
late near-maximizing responses. That invalidates a generic compact-space
claim when the maximizing point is not isolated, but not UA3. Positive
finite OWN mass makes the point a retained interval midpoint, and formula
(4) of the frozen source isolates it in the ACTUAL test set T. Never has
its separate isolated label. The response payoff is continuous on compact
T disjoint union Never; removing the isolated maximizer leaves a compact
set, so UA4 has a strictly positive uniform gap. Infinite near-maximizing
finite deadlines are already represented by their finite limit cut in T;
they would produce a distinct cap maximizer and violate unique POINT
attainment. Outcome-equivalent distinct maximizing points likewise do not
satisfy UA3.

I separately tested the new late c⁺ response. The source has zero
prescribed mass at c, and every selected positive-own-mass τ_i differs
from c. The entire signed family retains zero mass there and inserts
nothing later. A response at c or c⁺ therefore quits alone exactly on
the all-opponent-Never event and is passive otherwise. UA6a is exact for
signed rewards, including a selected Never response. It duplicates two
FINITE tests and never identifies either with Never. Both stay below the
unique selected maximizer.

The initial genuine transport issue was that frozen formula (2) permits
only nonnegative mixture coefficients, whereas the polynomial needs a
two-sided neighborhood. UA7–UA10 explicitly resolve it rather than
silently applying that formula. The original retained atom masses converge
to m_i>0, so replacing an old finite law by
(1−λ_i)p_i^k+λ_i δ_{τ_i^k} is legal for every fixed sufficiently small
negative λ_i. The displayed lower mass m_i/4 is valid. Retained interval
lengths stay bounded away from zero, giving uniformly bounded nonnegative
old-chart densities. Their weak-* convergence and the unchanged original
fixed/moving tester kernels give coalition, payoff, and COMPLETE-cap
convergence. Product-density convergence uses the rectangle argument, not
a product of uncontrolled weak limits. Never's interval has positive
length when it carries positive prescribed mass, so the same argument
applies there. Different owners may select different original atoms;
their independent modifications use the same unchanged ordered chart.

UA12 is multiaffine in all independent λ coordinates once the complete
caps are stabilized. The sign-cube proof of UA13 is valid, including zero
coordinate directions and vanishing first derivatives: nonconstant
square-free monomials are linearly independent on that cube and have
mean zero. Thus an interior minimum would force polynomial constancy.
At λ=(1,…,1), each prescribed law equals its DISPLAYED response, so
the globally defined selected-response polynomial vanishes. This is an
algebraic evaluation only; no distant endpoint cap stability or zero
actual endpoint debt is needed or claimed. A small signed descent stays
inside the gap-stable box and UA10 transports it to a literal finite
actual profile below the global infimum. This closes the contradiction.

The restriction has export-level mathematical value as a new actual
source exclusion, subject to the coordinator's independent novelty/value
check and the normal export gate. It forbids a complete positive-minimum
configuration using only its produced chart and global minimality, and
supplies the actual finite descent responsible for exclusion. It is not
merely a supplied-object verifier or an improved constant. The exact
surviving alternative must be retained: SOME owner has multiple distinct
maximizers, or its unique maximizing point has zero prescribed own mass.
It does not prove that arbitrary minima can be selected to avoid those
alternatives, and it does not consume responsive multi-cap cycles.

## Final artifact review: standalone cap-atom exclusion

PASS for the complete511-line
`exports/POSITIVE_MINIMUM_CAP_ATOM_EXCLUSION.md` reviewed
on2026-10-07, SHA256
`29e55dee03a1cb70f9a470f5a3a9f646a1f3029c1108a5d5c384fe6c16471300`.
This is ordinary-mathematical acceptance for the exact
necessary restriction stated there, not a Lean seal or export placement.
I read every section of the standalone artifact, including its inlined
marked producer, actual source correspondence, boundary tests, and
handoff. The earlier UA review remains applicable; the artifact has no
mathematical dependence on a conference note or the frozen source packet.

The inlined producer is complete for its claimed mode. Finite censoring
preserves EVERY pure response uniformly, so finite-law and arbitrary-law
infima agree. The old common charts retain endpoint and test-location
Hausdorff limits separately, collapse only retained atom intervals, and
keep Never separate. Bounded product densities and a.e./L¹ first-coalition
kernel convergence correctly retain all simultaneous coalitions and
joint-Never. The complete cap upper bound tests ANY maximizing sequence
on the OLD test set; its lower bound approximates each limiting test.
At a retained midpoint the unique original atom preserves its tie;
at a zero-atom cut the opponent kernels converge. Thus continuity and
cap attainment do not discard arbitrary late responses or confuse the
last finite cut with Never.

I rechecked signed witness legality, density bounds and complete tester
transport in the standalone text, not just the earlier notes. The
neighborhood's uniform gap includes c⁺ by the exact zero-c-mass identity.
The selected-response multiaffine argument remains valid, and its
distant endpoint zero is explicitly NOT asserted to be actual endpoint
zero debt. The negative local branch is realized by literal original
finite profiles, contradicting the true infimum.

The declarations in the source-correspondence section were located and
their actual statements read under the displayed imports:
`abs_expectedPayoff_censorLateFiniteStoppingLaws_sub_le`,
`abs_replacementCap_censorLateFiniteStoppingLaws_sub_le`;
the two stopping-law/behavior payoff equalities and two full-cap
equalities in `StoppingLawOperationalDistance.lean`;
`quittingTerminalOutcomeMass_stoppingLawMixture_eq`,
`quittingTerminalPayoff_stoppingLawMixture_eq` in the Diagnostic
stopping-law affinity module; and
`exists_finiteDeadlineTimingProfile_approximation`,
`isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`.
Their hypotheses match the signed finite reward semantics here. The
affinity theorems only permit coefficients in[0,1], and the manuscript
does not misuse them for negative coefficients. The fixed-target
finite-menu criterion indeed requires payoff and unrestricted
exploitability bounds on the SAME actual profile and permits arbitrary
lower displayed deadlines. No build was run and no fresh checked fact
is attributed to the new ordinary argument.

All three boundary tests are exact. Grand-coalition sure play has zero
gap and unique supported caps; the half-Quit/half-Never profile has
positive debt2 but true gap0 and the displayed simultaneous decrease;
the uniform-calendar boundary has cap value1 uniquely at point0, zero
own POINT MASS there, and no uniform complement gap despite membership
in topological support. The final theorem correctly says zero point
mass, not absence from topological support. Multiple outcome-equivalent
TEST POINTS remain genuinely multiple under the stated premise.

No mathematical correction or unresolved objection remains for the
reviewed artifact. Its export-level contribution is the exact
all-owners-unique-positive-own-atom exclusion at EVERY produced marked
true minimum. It supplies no producer for the surviving alternatives
and makes no full-conjecture or arbitrary-calendar coverage claim.

## Focused LC1–LC5 cross-check, 2026-10-08

PASS for the source restriction in the section “One exceptional latest
cap: conditional old-mass transport and a sure-clock reduction” of
`notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`. This is a focused
ordinary-mathematical check requested by the coordinator, not a final
artifact or export gate. I read LC1–LC5 and the old-chart UA construction
on which its actual transport depends.

The exceptional unique maximizing point need not be isolated. The
argument does not infer a uniform gap from this uniqueness. Above a
cut strictly between all replacement opponent atoms and that point,
every nonempty replacement term has already absorbed, so its payoff
is independent of the later response. The unchanged term is multiplied
by ∏(1−λ_j)>0. Below the cut compactness and continuity give the needed
uniform gap. Together these facts stabilize the exceptional response;
the three supported maximizing points are isolated and have ordinary
uniform gaps. The exceptional owner's own-law change cannot change its
cap. Never and a possible last finite maximizing cut are covered.

The conditional old-tail transport is legal with both signs. The
retained mixture atom at t₀ has a positive-length quantile interval,
even if the exceptional owner itself puts no mass there. Its right
endpoints converge, so the indicators of the old region strictly after
that interval converge in L¹. Their uniformly bounded multipliers,
combined with the original bounded densities, give nonnegative bounded
modified densities and weak-* convergence. This supplies actual finite
witnesses; it is not an application of the nonnegative-mixture theorem
to an unauthorized negative coefficient. Original product and moving
response kernels are unchanged and retain every tester. No law gains
mass at c, so c⁺ duplicates c throughout these changes.

At the first polynomial endpoint the conditional exceptional law and
its later displayed response both follow a sure earlier opponent exit.
Thus every selected-response debt vanishes, contradicting the constant
positive polynomial. The subsequent sure-by-t₀, common-cap and positive
exceptional-atom conclusions follow from exact outcome equivalence with
Never, not from response-gap stability at an endpoint. The second
endpoint gives only δ=r_m(I∖{m})−r_m(I). It does not identify actual
endpoint caps, declare a pure-grand minimum, or supply a Nash root.

As an independent endpoint check, leaving only m at its original law
gives δ=a_mδ+(1−a_m)[r_m(I∖{m})−s_m], since its support is no later than
t₀. Therefore any earlier exceptional mass forces r_m(I)=s_m. I obtained
this identity before learning that the author had also derived it.
It does not itself contradict the strict singleton margins of the
original minimum: earlier opponents can give m larger passive payoffs.
The complete source restriction is accepted; its surviving common-date
geometry still needs a full-cap consumer.

## Focused EA1–EA5 review, with EA6 boundary, 2026-10-08

PASS for the ordinary-mathematical source exclusion in “Earliest active
zero-mixture cap: simultaneous conditioning exclusion” of
`notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`. I read EA1–EA6,
reopened the exact marked construction and full response transport in
`exports/POSITIVE_MINIMUM_EARLY_ORIGINAL_COLLISION_STAGE.md`, and rechecked
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
under its imports. This is the requested focused falsification, not a
standalone artifact/export gate or Lean check. No unresolved mathematical
objection remains in this scope.

The accepted statement is precise: τ is the least point of the UNION of
ALL four complete active response sets, it is finite, its MIXTURE atom
is zero, and EVERY owner's final strict-late probability e_i is positive.
At a produced true SUM minimum with δ>0 those hypotheses contradict one
actual final cap equalling that owner's singleton reward. No uniqueness
or own cap mass is needed. If an e_h vanishes, only the stated sure-early
and multiple-maximizer output survives; that branch is not consumed.

The key change from the common-zero consumer is valid. At each fixed
earlier cut u_n, every nonoriginal product term contains a finite early
clock and therefore pays the SAME constant for ALL responses t>u_n.
The unchanged term has a strictly positive multiplier. Thus the full
upper response functions, not merely one selected branch, undergo a
common positive affine transformation. This preserves arbitrarily many
active upper responses and all their ordering against nonactive upper
responses. There is no need to infer a uniform gap from uniqueness or
to bound nonisolated near-cap tests individually.

The separate compact lower set T∩[0,a_n], with u_n<a_n<τ, has no
active point for ANY owner by the definition of τ. Its positive gap
can shrink with n; the proof uses a different small signed box for each
n and never needs a uniform-in-n gap. This covers tests moving upward
through the cuts, left-isolated τ, gaps of T, and even an empty lower
set. Choosing real cuts in a gap does not insert a new clock: the initial
old segment is unchanged there. Its raw boundary is an old limiting
endpoint, or the right endpoint of a retained interval. The final zero-
mixture boundary τ is raw-null. These are exactly the boundaries for
which whole old finite date intervals approximate the cut in L¹.

Both signs are legal: the conditional-event likelihood is 1−λ off the
event and 1+λ(1/e−1) on it. Positive normalizers and a fixed sufficiently
small box make both bounded and nonnegative. Original endpoint cuts
converge; their indicators converge strongly in L¹. Multiplying the
bounded weak-* densities by these likelihoods preserves the original
weak-* limit against each L¹ test. Original product and arbitrary moving
response kernels remain unchanged, so the actual FULL-cap transport,
including Never, follows rather than being supplied as an interface.
All changed laws still have zero c mass; c⁺ duplicates c. No nonatomic
point receives a new atom in this bounded transport.

The distant selected endpoint (EA3) is correctly NOT yet claimed to be
an actual minimum. The later passage is what makes the theorem a consumer.
Because the final e_i are bounded away from zero and q_i(τ)=0,
ν_i^n→ν_i in total variation. This gives the selected identity at ν
and the direct final actual-carrier realization. The exact expansion
against early submeasures strictly before τ then works on the CLOSED
upper test set, including τ itself and Never. The original selected
τ_i remain maximizers on that whole upper set. At τ and every earlier
finite test the new payoff is s_i. Since the upper selected payoff is
at least its value at τ, these earlier tests cannot exceed it. Thus
ALL final full caps are derived, even when later caps exceed their
own singleton rewards. For one earliest owner m, the selected τ_m=τ
has cap exactly s_m. Only now do selected debt and actual debt coincide
at δ, allowing the checked singleton-margin contradiction. No Nash tail
or conditional debt-minimum assumption enters this identification.

I attempted the following boundary falsifiers. A first finite tester
with zero mixture mass already gives the earliest owner's cap s_m and
contradicts the original minimum margin; the proof handles it separately.
A final τ=c makes ν all-Never but still retains Never as a different
response: the upper comparison controls it, so there is no omitted last
finite test. A τ left-isolated in T causes the conditioning laws to
stabilize before the real cuts reach τ, not a failure of convergence.
Partial active sets and distinct later active points do not break the
positive-affine ordering argument. Atomless participant-indicator laws
have positive debt but are not global minima and therefore do not falsify
the result. Zero rewards have δ=0 and do not permit its final contradiction.

EA6 is an exact and important falsifier of a STRONGER statement. Its
uniform 0-law then uniform 1-law has U=(0,1,1,1), B=(1,1,1,1),
D=1, earliest active τ=1/4, and e_0=0. All three other owners have
every upper finite test and Never maximizing, as EA5 predicts. Earlier
cut masses e_0^n are positive but tend to zero; their conditional density
bound diverges and their laws would create a new atom at a nonisolated
point. This is NOT bounded old-chart transport. I checked the full
finite payoff chronology: player0 needs a response at least2N (or
Never) for cap1, while each other player needs at leastN (or Never).
All-Never has true debt0. Thus EA6 neither supplies a positive-minimum
counterexample nor permits removing the FINAL strict-late hypothesis.

The all-unique corollary is also accepted. If e_h=0, the other three
owners have distinct c and Never maximizers, contradicting uniqueness.
Thus an all-unique earliest cap cannot have zero mixture mass. For
completeness, an earliest cap equal to Never with POSITIVE mixture mass
cannot occur either: all four cap sets would be {Never}; a zero own
Never mass would make another owner's Never response tie c, while all
four positive own Never masses are excluded by the already accepted
cap-atom theorem. Hence the earliest cap is finite, has positive mixture
mass, and is isolated. This does not make every later cap isolated or
turn its positive mixture atom into positive OWN mass for every owner.

This is a significant necessary SOURCE restriction: it eliminates the
reviewed fresh-table reduction's three-supported nonisolated-earliest
alternative, and consumes the multiple-active-set zero-mixture branch
except for an explicit sure-early boundary. It is stronger than a new
conditional response ledger. Export-level value is plausible, subject
to the usual separate complete-artifact and independent review gate;
this feedback alone does not authorize packet placement.

## Focused independent KR1–KR8 falsification: PASS

Reviewer: CODEX_NOETHER. Checked the saved section “Generic raw-kernel
rigidity excludes an all-isolated unique-cap minimum”, labels KR1–KR8,
in `notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`. This is
ordinary mathematics plus narrow read-only source verification, not a
Lean build or whole-artifact/export gate. I did not read any counterpart
KR review. No unresolved mathematical objection remains in this scope.

The accepted statement is a FRESH-table producer, not a pointwise
restriction on the old table: starting from the canonical positive-gap
table, first select an arbitrarily close full-table row-difference-generic
table preserving all82 no-contact inequalities and a positive gap; then
select arbitrarily close positive recipient scales making EVERY compact
SUM-minimizing debt vector identical. At THIS one table, no produced true
marked minimum has all four complete caps unique and isolated. The
remaining all-unique arm has a nonisolated LATER maximizing point with
zero OWN point mass; the multiple-cap arm remains open.

I checked the following load-bearing steps and attempted falsifiers.

1. Raw genericity is genuinely available. With Never assigned row value0,
   distinct ordered pairs A≠B have distinct coefficient vectors
   e_A−e_B. Thus every forbidden equality or zero difference is a proper
   affine hyperplane in the fifteen free row entries. An arbitrarily
   small open-cube perturbation avoids their finite union. No old law or
   minimizing debt is carried through this operation. Positive row
   scaling preserves the condition exactly, and sufficiently small
   perturbations/scales preserve the open no-contact and positive-gap
   conditions. MORSE Section49's fixed-carrier W argument applies anew
   after genericization; it gives debt-vector rigidity, not U/B rigidity.

2. Continuous OLD-law weights suffice, and their transport is literal.
   A continuous nonnegative weight on T extended over its gaps, with
   Never treated separately, becomes a constant multiplier on each old
   finite date interval through its midpoint. The midpoint projection
   converges almost everywhere to the old retained-atom projection.
   Bounded continuous weights therefore converge strongly in L¹;
   the original bounded densities and weak-* convergence give both the
   normalizers and new densities. Two-sided likelihoods are uniformly
   positive on a small box. No new clock, public lottery, new atom at
   c, or correlated opponent plan appears. Unchanged original product
   and arbitrary moving-test kernels give FULL cap transport. The
   extra late c⁺ response duplicates c EXACTLY; it need not have a
   strict gap when c is the selected maximizer. This exact duplicate,
   recorded in KR2, is enough and is not an additional moving branch.

3. Unique ISOLATED selectors have a uniform gap on the compact old test
   complement. Uniform total-variation bounds keep the full cap values
   at those selectors under small signed weight changes. The actual
   SUM polynomial is multiaffine and has an interior global minimum,
   so it is constant; all nearby pairs are actual minima. All-family
   debt rigidity then makes EACH individual regret polynomial constant.
   Its evaluation at distant targets is ONLY a selected integral
   identity, never an asserted actual endpoint cap/minimum.

4. The continuous product-weight identities determine the finite-valued
   measurable raw regret kernel. Nonnegative continuous products suffice
   by signed linear combinations and the separating product algebra;
   zero-integral weights are automatically null for the product law.
   A positive debt coordinate yields a positive constant raw difference.
   Ordered-pair injectivity fixes BOTH its response outcome and the
   prescribed outcome almost surely. The repeated-difference two-player
   test in KR7 is correct and shows why genericity cannot be removed.
   It is not a positive-global-minimum counterexample.

5. Deterministic nonsingleton absorption really forces a common Dirac
   date for its members by independence. There is no mixture mass before
   it. EA excludes an earlier unique cap; any later cap is screened by
   another sure member and would tie finite c with Never. Thus all caps
   are common and the preserved canonical exclusion applies. The
   all-Never deterministic case instead contradicts the checked singleton
   margin for any positive own singleton, or has debt zero if none exists.

6. The singleton graft handles diffuse, atomic-boundary and final-c
   support separation. Independent almost-sure strict ordering provides
   original integer cuts with owner's late leakage and all opponent
   head masses tending to zero. A boundary atom is included via its old
   right cut; a null boundary is approached from below. Grafting the
   SAME actual independent punishment beyond those cuts preserves all
   nonowner full caps and all U up to the stated14Mη error. The owner's
   EXACT full cap is max(H,A+α cap(w)); head caps tend uniformly to its
   own singleton, A→0 and α→1. Choose ε<B_h−s_h and actual cap(w)
   at most P_h+ε≤s_h+ε: the resulting actual debt is strictly below
   the true global floor. No Nash tail or punishment attainment enters.
   If literal finite-support witnesses are desired, truncate each fixed
   punishment law's finite tail to Never. Its tail mass tends to zero,
   and coupling bounds ALL response-cap errors uniformly, preserving
   ε-optimality. The argument does not require an infinite-law loophole.

The inspected exact declarations were
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`,
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
and its `all_punishmentNormal` field in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`,
`IsQuittingNormalPlayer` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`,
`quittingPunishmentValue` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`, and
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
Their literal hypotheses supply same-table true independent punishment
normality and the actual global singleton margin; no normalization or
supplied stationary punishment cap is substituted.

The unique nonisolated quadratic-cap example correctly prevents extending
KR3 by uniqueness alone. Multiple active points are also not handled by
the rectangle argument: an arbitrary fixed selector need not remain a
full cap under the signed weight box. Neither remaining case is silently
absorbed by genericity. KR is a genuine strict SOURCE-class exclusion,
not only a multiple-point reselection or conditional response interface.
It has significant export-level value once embedded in a self-contained
artifact that passes the independent complete-artifact gate; this focused
PASS alone does not authorize placement.

## Focused independent HR1–HR6 falsification: PASS

Reviewer: CODEX_NOETHER. Checked the saved section “Head-box debt rigidity
excludes EVERY all-unique minimum”, HR1–HR6, in
`notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`. This is a focused
ordinary-mathematical review, not a whole-artifact gate or Lean claim.
I have not read a counterpart HR review. No unresolved mathematical
objection remains in the stated scope.

Accepted statement: ONE fresh canonical positive-gap table can be
selected with its82 finite gaps preserved and ALL-family minimizing
debt-vector rigidity. At THIS table EVERY produced marked global
minimum has a multiple-point full cap. This excludes the entire
all-unique arm, including nonisolated LATER maxima. It does not need
generic raw payoff differences, does not consume the resulting multiple
kernels, and does not imply UE. The fresh scaling is selected before
new minimizing laws; no old minimizing family is identified with it.

I checked the exact all-response and original-source chain.

- DR5's supported-earliest exclusion is used correctly: the earliest
  all-unique cap τ is a finite isolated positive MIXTURE atom, but
  EVERY owner whose cap is τ has zero OWN atom there. A supplier h
  has q_h({τ})>0 and a different later cap, so it has STRICTLY positive
  original debt. Positive mixture mass is not silently equated with
  positive own mass for a maximizing owner.

- The signed HEAD likelihoods are bounded and positive for both signs
  on a small box, including redundant e_i=1 coordinates. Conditioning
  includes the entire retained date interval by its RIGHT endpoint;
  no atom is bisected or inserted at a nonisolated point. Whole old
  interval indicators converge in L¹, their positive normalizers
  converge, and original bounded density/kernel arguments transport
  every fixed and moving response. Never is separate; c has zero mass;
  c⁺ duplicates c exactly even if c is selected.

- Earliest isolated selectors have a uniform compact-complement gap.
  For a later selector, every nonoriginal product term contains an
  opponent stop≤τ; it is absorbed strictly before ANY t>a_i>τ.
  Its payoff is therefore the SAME constant for all such t. Positive
  original-term scaling preserves the WHOLE upper response ordering,
  not merely the selected value. The compact lower set omits the later
  unique maximum and has a gap. This handles nonisolated near-max tests
  and a selected Never. In the Never case τ<c, since τ is a positive
  retained atom and c has zero mass, so the stated separating real
  a_i∈(τ,c) exists. No ordinary “uniqueness implies gap” inference is
  being made at a nonisolated later point.

- Actual cap identification on the small signed box is complete. SUM
  multiaffinity gives actual minima throughout that box, and ALL-family
  debt rigidity makes EACH regret polynomial constant. Its distant
  algebraic identities are not called actual endpoint caps/minima.
  Without individual constancy, constant SUM alone would not give
  HR4's conclusion; the load-bearing rigidity hypothesis is visible.

- In the one-head case all opponents are strictly after τ; the head
  law pays exactly s_h. Individual constancy forces original U_h=s_h,
  also when e_h=1 is redundant. The checked original singleton margin
  gives d_h≥δ. Some different earliest owner has unique cap τ but
  zero own mass there; its bounded raw regret is strictly positive
  almost surely under its own law, hence d_j>0. This defeats δ≥d_h
  without assuming a uniform positive gap on that own law.

- With two or more head owners, conditioning every other head makes
  at least one opponent sure≤τ. Original h's CONDITIONAL late law and
  its selected later response are both absent from exactly the same
  first coalition, so their raw regret is zero. The two polynomial
  evaluations give d_h=e_h d_h, hence ORIGINAL e_h=1. This does not
  derive purity of a polynomial endpoint. That original sure supplier
  screens every other later cap into a c/Never duplicate, so all other
  caps must be τ. DR5 then removes their root atoms, and uniqueness of
  h's later cap makes each opponent's final strict-late mass positive.

- The root test for h really is A+αs_h: ALL opponent root atoms have
  been excluded, so through-root and strictly-before-root absorption
  limits agree. The head cap H is the maximum on the compact finite
  test set≤τ and is STRICTLY below h's unique later cap. It is not
  replaced by a supplied punishment/continuation floor.

- Literal finite grafts preserve the opponents' heads, root masses and
  tail probabilities. All U and ALL non-h caps can differ only when
  original h survives the cutoff; this gives uniform2Mη errors and the
  stated14Mη aggregate. Early tests, joins at the root, and Never are
  included. The h cap is EXACTLY max(H_k,A_k+α_k cap(w)). Moving
  head tests have limiting point≤τ; every source point≤τ has original
  head witnesses; hence H_k→H. Opponent root leakage vanishes, giving
  A_k→A and α_k→α. True same-table P_h≤s_h and actual finite-support
  ε-punishment witnesses yield limsup new cap≤H+ε<B_h. This strictly
  lowers actual SUM and contradicts its global infimum. No tail Nash,
  punishment attainment, or automatic h best reply is inserted.

The narrow named-source verification is the same exact declaration set
recorded in the immediately preceding KR review: positive literal
infimum/no-UE equivalence, the full-support residual's same-table
`all_punishmentNormal`, its true infimum-over-independent-plans definition,
and the actual carrier singleton margin. HR correctly reapplies those
facts to the newly scaled table.

Attempted boundary failures were a selected Never, nonisolated later
tests approaching their maximum, a head normalizer1, positive other head
masses, vanishing finite root leakage, and a punishment with negative
own reward. Each is covered by the argument above. Earliest Never is
already excluded by the canonical earliest theorem; zero gap cannot
support either strict contradiction. The counterexample V(t,u)=−t²+2ut
does not falsify HR because this head-box produces an EXACT positive
affine map on the entire later test family, not an arbitrary affine
perturbation at each test. The unreviewed scalar nonisolated cap issue
therefore is genuinely resolved for this source operation, not assumed
away. If multiple caps are present at the initial source, the earliest
support reset and fixed-selector debt box need not identify all full
caps; HR makes no such extension.

This is a significant strict whole-source reduction and supersedes KR's
all-isolated/generic arm. Its remaining point multiplicity can still be
an outcome-equivalent screened plateau. A self-contained assembled packet
requires its own independent final-artifact gate; this focused PASS is
not permission to export or a solution of the Fin4 conjecture.

## Focused independent BG1–BG6 falsification: PASS

Reviewed the whole section headed "A random minimum forces a root-to-later
active payoff-kernel bridge" in the owned notebook. Its frozen section-to-
EOF SHA256 is
`a74e319a2e70999513399e527ce48769d9ef0013dece01272afb95df122c1afc`,
checked independently. This is a focused ordinary-mathematical PASS, not
a whole new artifact gate or UE proof.

Accepted scope: at ONE compatible row-generic debt-rigid positive table,
EVERY produced marked minimum either has deterministic terminal outcome,
or has an owner maximizing both at the finite isolated first prescribed
atom τ and at a later compact response σ. Those two response PAYOFF
kernels differ on a positive-probability event of its original opponent
root draws. The expected values are equal maxima. The bridge owner need
not have positive debt. No repeated-root debt contraction is inferred.

### Same-table selection, including the stronger 93-label combination

BG1's own construction produces all82 gaps and row genericity before
selecting a regular recipient scale. It does not retain an old minimum.
I also checked the requested compatibility with MORSE Section50:

1. Begin with its positive convex-step table, BEFORE its final DR scale.
   The at most93 labelled no-contact gaps and all W/J cohort signs are
   strict.
2. Contract the entire table by a common positive factor arbitrarily close
   to one. Every label and Δ contract by that factor, so all gaps and
   signs persist, while every entry moves inside the unit cube.
3. Select an arbitrarily small perturbation avoiding the finitely many
   recipient-row equality hyperplanes. Choose its radius also below the
   positive gap, the 93 no-contact distances using coefficient bound8
   and the Δ Lipschitz bound8, and every strict W/J sign margin. The
   typed cohorts remain the SAME cohorts; one must not rebuild them
   from a different old worst table.
4. Apply the ordinary DR coordinate-regular scale selection to THIS fixed
   carrier. Positive scales preserve row inequalities and signs exactly,
   and sufficiently small scales preserve all93 gaps and Δ>0.

Thus one final table simultaneously has the genericity BG5 needs, all
SA restrictions and all-minimum debt rigidity. Applying the SA, HR and
BG source arguments afresh at that table is legitimate. None depends on
the earlier target's numerical entries after their required gaps and
signs have been obtained. Re-genericizing a table AFTER a DR selection
and silently retaining rigidity would not be justified; the order above
avoids that error.

Row genericity is needed only for the payoff-kernel distinction. The
head-collapse and no-bridge contradiction use no Sidon or ordered-pair-
difference injectivity hypothesis.

### All-active stability and deterministic collapse

BG2 uses the all-active chronological head box, not unique cap stability.
Every active response is above its early cut, so the same positive affine
map acts on the ENTIRE upper family, including accumulating maxima and
Never. The lower compact family has no active point and a strict gap.
Actual signed old-cut transport puts the whole neighborhood in the
original carrier. SUM constancy first makes that neighborhood actual
minimum pairs; rigidity then fixes individual selected-regret polynomials.

For a singleton head, individual constancy forces ORIGINAL U_h=s_h, and
the exact tracked all-owner quadratic prescribed margin contradicts it.
For multiple heads, the other conditioned head screens both a late
prescribed clock and the chosen active response, so a positive-debt
head owner satisfies d_i=e_i d_i and is ORIGINAL sure-head. A non-head
owner has selected regret zero at the algebraic all-head endpoint and
therefore cannot carry preactive mass. Ordered-cut descent, with whole
retained right boundaries at isolated points, makes all preactive owners
originally pure at one common earlier date. This yields a deterministic
outcome without any full-row genericity. Hence a random source has no
earlier mass; EA or the direct singleton-cap calculation makes τ a finite
positive-mixture isolated atom.

For BG3, the no-bridge assumption means every cap set containing τ is
EXACTLY {τ}; other cap sets can be arbitrarily multiple. Root-only sets
have genuine isolated complement gaps. Each wholly later compact active
set is separated from τ; its whole upper family receives the exact
positive affine map under resets to EXISTING positive own root atoms.
Its lower compact gap survives uniformly. Thus ALL full caps, not merely
chosen representatives, are stable on the signed root box.

The reset densities are legal of both signs because only owners with
positive own root mass are changed. The retained atom interval witnesses
both signs on the original finite charts. Product tests, all moving
response kernels, Never and c⁺ remain covered. No zero-mass insertion
or false gap at a nonisolated later cap is used.

The actual SUM polynomial is constant at its interior global minimum.
Only after that does all-family rigidity make each selected polynomial
constant. If the root cohort has one member its original payoff is its
singleton, contradicting the prescribed margin. For a member whose cap
is root-only, its own reset multiplies debt by 1−λ; rigidity forces debt
zero, and unique maximization forces ORIGINAL purity. For a member with
all caps later, its positive own root atom gives positive ORIGINAL debt.
Conditioning other cohort members to root screens its own late branch
and chosen late response equally, giving d_h=a_h d_h and ORIGINAL a_h=1.
Every root supplier is therefore pure, and all outsiders are later:
the original terminal outcome is deterministic, a contradiction. Remote
selected endpoints are never called actual cap-minimizing endpoints.

### Genuine kernel distinction and boundary attempts

Since the bridging root response is the full cap, singletonMargin gives
B_i>s_i. If no opponent had a root atom it would instead pay exactly
s_i. Thus some nonempty opponent root coalition S occurs with positive
probability. Root response τ joins S, whereas ANY σ>τ, including Never,
sees S already absorbed and does not join it. Genericity gives
r_i(S∪{i})≠r_i(S), so these PAYOFF kernels differ on that actual event.
The sign is not asserted and the owner's expected regret may be zero.

I checked the finite witness upgrade: retained root densities give
convergent own atom and through-root masses; lack of earlier source mass
gives the positive probability of precisely S quitting at the retained
date with all other opponents later. A moving witness for σ is eventually
later than the isolated root. The two original response outcomes on this
event are literally S∪{i} and S, with the same fixed nonzero row difference.
This is not only a distinction on a formal newly inserted compact test.

Attempted falsifiers were multiple late/Never aliases, arbitrarily close
later active points, a root reset of unit mass, all debt carried by one
root supplier, a zero-debt bridging owner, and non-generic equal rewards
on the two distinct coalitions. The first four are handled by full cap
stability and original polynomial extraction; the fifth is explicitly
allowed. The sixth is the exact constant-one boundary example in BG6
and explains the honest row-genericity premise. The participant-indicator
half-root/half-Never profile has positive debt but true gap zero and a
legal root-reset descent, so it cannot falsify a global positive minimum.

I inspected the named declarations
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`,
`quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`
and `exists_quittingCapNashRootStack` in
`UniformEquilibrium/Quitting/Root/CapNashRootStack.lean` under their imports.
They require each root to be Nash against its actual suffix FULL cap,
not its payoff or the global original cap. The all-root-tie ledger
D=c D_tail is correct, but prefixing the same root changes its tail cap
vector and does not preserve its Nash property. BG6 records that failure
without weakening its source theorem into a supplied repeated-root oracle.

No unresolved mathematical objection was found. Combined with the
independently checked SA deterministic exclusion at ONE compatibly selected
table, BG removes late-alias-only multiplicity and produces a genuine
random atomic root-to-later active payoff-kernel wall. This is a stronger
common-source restriction than HR's some-two-points result. It still has
no response-complete debt decrease or positive-debtor bridge guarantee.

## Focused finite-prefix seam check: NF1–NF7

Verdict: ordinary mathematical PASS for the complete section headed
“The genuine marked bridge as an actual finite-prefix source”, NF1–NF7
including the exact nonconsumer identity(NF8). This is ONE focused seam
check, not another export gate or a source-class exclusion. I read the
entire section and independently checked its limiting and null branches.

The carrier, table, global δ and common debt vector are SAME-table data.
Conditioning away strict pre-date mass normalizes by1−h_i^k→1, NOT by
joint continuation or the possibly vanishing post-root mass. TV=h_i^k
is exact for this censoring. The prescribed error2MΣh and opponent-only
full-cap error2MΣ_(j≠i)h are uniform over EVERY actual test and therefore
survive the unrestricted supremum. The convention agrees with the
operational distance twice-TV in the named tracked source.

Translation exposes the lost menu correctly: early integer tests pay
exactly s_i, so B(z^k)=max(s_i,B(y^k)) when n_k>0. Source maximizing
points are all at or beyond the earliest active τ. Retained τ witnesses,
strictly later moving witnesses, and literal Never all remain after
translation and keep their limiting cap values under the same TV bound.
Thus B(y^k)→B_i; the positive global singleton margin then makes the
discarded tests strictly dominated for large k. No order-only cap
invariance or simultaneous exact finite attainment is asserted.

The root/tail decomposition is an exact independent marginal mixture
at EACH finite k. A tail coordinate with zero own post-root coefficient
may be filled by ANY actual own law. Its own cap ignores that filler;
every other cap is screened by the sure root. When its coefficient
merely tends to0, all conditional laws are still actual, and compactness
is used ONLY for their bounded eight-dimensional payoff/full-cap pairs.
No bounded conditional calendar density is claimed. One common tail
subsequence v_k→v∈K recovers the ORIGINAL minimum through continuous
prefixing, rather than presuming that v minimizes ordinary debt.

The later cap witness gives C_i≥B_i; the recovered full prefix maximum
gives the reverse inequality. This proves Q_i=C_i=B_i also for α_i=0,
without dividing by its zero coefficient. For α_i>0 an ε-best actual
tail reply is enough; no limiting exact tail-clock maximizer is needed.
The original positive opponent event and generic row difference preserve
the genuine payoff-kernel distinction, not a late/Never alias. At least
two positive rates plus random prescribed outcome force a mixed rate
and two distinct positive FIRST-root coalition probabilities exactly as
stated; no all-interior or c>0 claim is smuggled into NF1.

I reread under their imports
`abs_quittingStoppingLawExpectedPayoff_update_same_sub_le_opponents` and
`abs_quittingContinuationBestResponseValue_sub_le_opponentStoppingLaws`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`,
and `quittingTerminalSemanticPair_rootThenContinuation` and
`quittingTerminalSemanticPrefix_mem_carrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
They match the actual full-cap/closure scope used here. No Lean build
was run and no source was changed.

For c>0 I recomputed(NF8) separately on b_i≤t_i and b_i≥t_i:
the respective terms are t_i−u_i and
b_i−u_i+a_i(b_i−t_i)/(1−a_i). The two hinges are therefore correct.
They are a CAP-penalized ALL-carrier objective, not weighted debt and
not a Nash/payoff-minimizing tail. Its α_i=0 boundary is explicitly
outside the formula. No unresolved seam objection was found.

### Universal finite-prefix extension NF8 / formula(NF9)

Focused mathematical PASS after reading the COMPLETE appended NF8.
This is an extension of the same seam review, not a new artifact gate.
The quantifiers genuinely range over EVERY x≠0 and EVERY w∈K with
D(T_x(w))=δ at the ONE final table. It is not inferred from NF1's
single witness or merely from common d* plus row genericity.

Finite actual tails approximate ANY carrier pair using the same TV
complete-cap censoring. Exact fixed-x prefixing then produces a genuine
global minimum sequence, whose first quantile mixture cell is exactly
[0,m], m=Σx_i/4>0 at EVERY finite stage. There is no endpoint inside
(0,m), so its midpoint τ₀=m/2 remains isolated, first, and has exactly
the own masses x_i in EVERY produced subsequence. Tail charts can vary
without altering that cell. No zero-survival conditional density enters.

The canonical EVERY-produced-source theorem forces earliest active τ
to this first point: later τ would have old positive prescribed mass
before it, and earlier τ would not be a positive prescribed atom.
Thus the new source's root/later bridge occurs at the FIXED root cell,
not at some unrelated later collision. Its later moving witnesses
cannot use date0 because this isolated cell has fixed positive width.
The exact full cap identity gives C_i≥B_i and max(Q_i,C_i)=B_i even
for α_i=0. The nonzero-root and genuine opponent-event conclusions
follow exactly as stated, including literal c and Never later tests.

This independently seals the universal same-cell/reselection step used
when a minimum-preserving graft removes its old sole bridge. An old
bridge is not carried forward; NF9 produces a bridge afresh at the
NEW nonzero root with its SAME actual carrier tail. The x=0 boundary
and near-minimum noncoverage are essential and are correctly retained.
I found no mathematical objection or hidden source switch.

Narrow specification sanity check: the current
`questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md` retains precisely
the NF9 strength under “Constraint on every minimum prefix”: EVERY
x∈[0,1]⁴ and w∈the SAME actual K with Σx>0 and D(T_x(w))=δ
has some Q_i=A_i+α_i b_i(w), plus two positive rates and one mixed.
The equality is automatically co-maximal by its literal max formula.
Its all-minimum singleton margin and row genericity also give the
positive different-payoff opponent event at ANY such reconstructed
minimum, although the explanatory paragraph spells it out only for
the supplied row. Zero owner debt, x_i=0/1 and α_i=0 are retained;
no tail attainment or ordinary tail minimum is inserted. Thus RM14's
flat-boundary exclusion needs no stronger hidden condition than this
question. This check is only of that specification seam, not a full
independent audit of the question or an additional gate.
