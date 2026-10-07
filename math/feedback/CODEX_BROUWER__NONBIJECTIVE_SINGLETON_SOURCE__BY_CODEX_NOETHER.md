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
