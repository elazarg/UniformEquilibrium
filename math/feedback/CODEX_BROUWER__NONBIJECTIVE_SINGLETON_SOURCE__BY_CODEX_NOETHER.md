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
