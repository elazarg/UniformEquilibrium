# Buffered triple–singleton uniform equilibrium: independent review

Reviewer: CODEX_MORSE.

## Scope and verdict

This review concerns only “A buffered triple–singleton producer beyond the
concrete-base screens” through the end of
`../notes/CODEX_NOETHER__MATCHING_JOINT_PRODUCER_FALSIFICATION.md`.
The frozen full notebook has 1968 lines and SHA256
`a6c53fe7264cb3c8bd98ac73739db5f77aaa82b59787fd451d28560cbfc9cfb9`;
the reviewed 568-line section has SHA256
`16a55576d344bc1f53bad132c93dc9541e8ff6f86a37c167f029ed6ebee51a50`.
Both identities were checked directly. No other review was read.

Mathematical verdict: PASS. The raw hypotheses produce the strategic data;
they do not ask for a complementary root, a stationary profile, a selected
Nash point, or a continuation certificate. The proof gives the stated
original-game uniform-equilibrium conclusion with arbitrary signed levels
and unrestricted behavioral replacements. This is ordinary mathematics,
not a new Lean verification.

Coverage verdict: PASS for the explicitly checked raw-source separation,
including the complete persistent-base Nash carriers. This candidate is
not the earlier finite coarse-regret criterion whose UE class was already
covered by punishment-tail dispatch. There is one narrow wording correction
to the opposite-sign comparison, recorded below; its corrected exclusion
is valid. No whole-class inclusion in an existing producer was found.

The center does have another exact stationary equilibrium. A complete
rational contraction certificate is preserved below and in the reviewer's
notebook. That fact refutes any proposed all-stationary exclusion, which
the frozen theorem does not assert. It does not identify an existing
raw-table selector that covers this new family.

No unresolved objection to the theorem or the corrected bounded coverage
claim remains. A standalone should use the precise harmful-pair comparison
below, not the overbroad assertion that no pair has two negative joining
gaps. The separately checked input weakenings at the end are not silently
part of the hash-bound base theorem.

## 1. Exact claim and produced objects

There are four players, A={0,1,2}, and b=3. The first nonempty quitting
coalition absorbs at its actual finite reward vector; joint Never pays zero.
Private randomization is independent. Public histories are observed, and
a deviation replaces a player's complete behavioral strategy. The live
date selecting absorption pays zero.

Put s_i=r_i({i}), Γ_ii=0, Γ_ij=r_i({j})−s_i. For distinct i,j∈A,
write Π_ij=r_i(ij)−s_i and c_ij=r_i(ij)−r_i(j), and similarly
Π_iA=r_i(A)−s_i, c_iA=r_i(A)−r_i(A−i). The raw assumptions are
all six c_ij>0, all three c_iA≥0, and r_i(ib)≤s_i for i∈A.
Set M_i=max(0,Π_ij,Π_ik,Π_iA), B_i=max(0,Γ_ib,M_i), and
R_j=min_{i∈A−j} B_i/c_ij. With a=r_b(I)−s_b and a⁺=max(a,0),
the remaining caps are

    r_b(bj)≤s_b,
    r_b(bjk)−s_b≤−a⁺R_l/3,       {j,k,l}=A.

No own-level sign, nonsingleton passive sign, or matrix premise belongs
to the UE theorem. Under the internally available R₀/degree-one alternative,
the construction produces finite nonnegative odds with at least two positive
coordinates. The alternating joint-A/solo-b profile is exact terminal Nash.
One profile and one target precede the accuracy and finite horizon.

## 2. Nonlinear root production

I independently expanded the endpoint identities. For i∈A−{j,k}, put
D_i=(1+X_j)(1+X_k),
P_i=Π_ijX_j+Π_ikX_k+Π_iAX_jX_k, and
L_i=c_ijX_j+c_ikX_k+c_iAX_jX_k. Then

    U_i=s_i+P_i/D_i,       W_i=s_i+L_i,
    e_i=Γ_ibX_b−(1+X_b)L_i+P_i/D_i.

Both the A-date Quit endpoint and its Continue endpoint priced at W_i
equal U_i. The b-date Continue endpoint minus W_i is e_i/(1+X_b).
For b, the A-date Continue endpoint minus s_b is e_b/D_A, where
D_A=∏_{j∈A}(1+X_j) and

    e_b=Σ_j Γ_bjX_j
        +Σ_{jk⊆A}(r_b(jk)−s_b)X_jX_k
        +(r_b(A)−s_b)X_0X_1X_2.

Thus e=ΓX−N(X), with N=O(‖X‖²). The claimed extension N(x⁺)
is continuous on all of ℝ⁴ and keeps the quadratic estimate. It does not
evaluate a rational denominator outside its nonnegative domain.

The important bound is on every feasible point e(X)≥0, not only on
complementary roots. P_i/D_i is a convex combination of four displayed
coefficients, so it is at most M_i. Since L_i≥0,

    L_i≤(Γ_ibX_b+M_i)/(1+X_b)≤B_i,
    X_j≤R_j.

R₀ excludes a nonnegative column b of Γ. Consequently some Γ_ib<0,
and that same row gives X_b≤M_i/(−Γ_ib). The feasible set E is therefore
compact, even when some M_i or R_j is zero. No strict positive odds or
positive grand premium has been used in this compactness step.

For H_λ(x)=min(x,Γx−N(x⁺)−λ1), a zero is nonnegative and belongs
to the same E for every λ≥0. One large ball therefore works throughout
the negative-offset homotopy. For sufficiently large λ its fiber is empty,
so the total degree of H_0 is zero. In a small origin ball, the R₀ minimum
map F(x)=min(x,Γx) has ‖F(x)‖≥m‖x‖. The quadratic perturbation is
strictly smaller on the small sphere, uniformly along its homotopy. Thus
the local degree at zero is one. Excision forces another zero. Neither a
finite root set, genericity, nondegeneracy, nor a sign condition on N is
needed; the global and local arguments use the literal same minimum map.

Singleton support is excluded correctly. Support {b} would make column b
nonnegative. With support {j}⊆A, each other A row gives
Γ_ij≥Π_ijX_j/(1+X_j). If Π_ij<0 this contradicts
Γ_ij=Π_ij−c_ij<Π_ij; otherwise it gives Γ_ij≥0. The b row also
gives Γ_bj≥0. Again the column is nonnegative, contradicting R₀.
This produces at least two positive coordinates without assuming full
support. Every hazard is below one because the odds are finite.

The exact source chain checked was:

- `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`;
- `lcpMinMap_zero_eq_zero_iff_of_isR0Matrix` and
  `ambientDegree_lcpMinMap_zero_eq_r0Degree` in
  `MathUE/LinearProgramming/R0AmbientDegree.lean`;
- `ambientDegree_homotopy` in
  `MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`;
- `ambientDegree_excision` in
  `MathUE/Topology/AmbientDegreeProperties.lean`;
- `ambientDegree_eq_zero_of_forall_ne` in
  `MathUE/Topology/AmbientDegree.lean`.

The first declaration applies to bare original-game no UE, without an
auxiliary-game, own-sign, or supplied-strategy premise. The degree results
have the hypotheses used here; their presence is not a claim that this
new nonlinear construction has itself been implemented or kernel-checked.

## 3. Full collision caps and inactive coordinates

The passive b-date Quit endpoint of i∈A is at most s_i≤W_i. For b,
the numerator of the passive A-date Quit excess is the multi-affine
polynomial

    P_b(X)=Σ_j(r_b(bj)−s_b)X_j
           +Σ_{jk}(r_b(bjk)−s_b)X_jX_k
           +aX_0X_1X_2.

Each pair term is at most −a⁺X_0X_1X_2/3 because X_l≤R_l.
The three terms together cancel the positive part of the actual grand
collision. This is valid at zero coordinates and includes three simultaneous
A quits. It is not a two-opponent approximation.

For inactive i∈A the actual correction is

    ΔW_i=[e_i/(1+X_b)]/[1−1/(D_i(1+X_b))],
    ΔU_i=ΔW_i/D_i.

Both increments are nonnegative. The denominator is positive because
there is another positive hazard. Substitution checks both policy equations
and increases the prescribed Continue values without changing any Quit
endpoint. For inactive b the equal correction is e_b/(D_A−1)≥0.
Again its denominator is positive. These cases exhaust every support
boundary; one must not omit these corrections or identify inactive nominal
payoffs with actual continuation payoffs.

An exact adversarial test keeps the displayed table except
r₂(02)=r₂(12)=1/10, r₂(012)=1, and r₃(01)=3. It remains in the
raw class, with c₂A=0 and the same Γ and R. At

    X=(1,1,0,1/2),       e=(0,0,3/4,0),

the inactive player2 has nominal (U₂,W₂)=(11/20,6/5), correction
(ΔU₂,ΔW₂)=(3/20,3/5), and actual values (7/10,9/5).
Its A-date Quit endpoint is 11/20; its b-date Quit endpoint is 2/3.
Both are below the corrected values. This tests a strictly positive
inactive residual and the weak c_iA boundary, rather than merely a proper
root where the issue disappears.

## 4. Literal behavioral and finite-horizon conclusion

The corrected vectors satisfy the actual policy equations. Period survival
ρ=∏_i(1−q_i)<1 makes their bounded solution unique, hence they are actual
payoffs and lie in the coordinate reward bound. Against a deviator i,
opponent survival per period is ρ_i=∏_{j≠i}(1−q_j)<1 because support
has size at least two. Fresh independent opponent coins give this same
bound conditional on every live history; the deviator may use arbitrary
private memory and history-dependent randomization.

The endpoint inequalities telescope for any complete replacement. After n
periods the possible terminal-payoff remainder is at most 2Mρ_iⁿ. This
proves exact terminal Nash including Never and arbitrarily late quitting.
It does not use a bounded-controller or stationary-deviation restriction.

Uniformly over every unilateral replacement, E[τ+1]≤2/(1−ρ_i).
With B=2/min_i(1−ρ_i), the literal initial-zero convention gives coefficient
(N−τ−1)₊/N. Therefore payoff delivery to the fixed U* is at most MB/N
and unilateral N-horizon regret at most 2MB/N. One selected profile and
target work for every sufficiently large N, for every accuracy. There is
no accuracy-dependent target or exchange of profile/horizon quantifiers.

The signed translation stress is legitimate for this constructed profile:
every unilateral replacement absorbs almost surely because opponents do.
Thus row translations transport its values, without asserting translation
invariance for arbitrary profiles with positive Never mass.

## 5. Exact fixture and substantive source comparisons

I recomputed the complete table's six c_ij, three c_iA, M=(4,4,1),
B=(4,4,3), R=(4,4,8), and a=1/20. All displayed raw inequalities
have strict slack. Its favorable-matching singleton matrix has determinant
45 and the stated strictly positive inverse. Every size-two principal
determinant is −9 or −1; all size-three determinants are 6. All columns
have a negative entry. Hence it is R₀. At the strictly negative constant
LCP offset, the only solution is the full-support vector1: the favorable
pair solutions have negative inactive residuals, harmful pair solutions
have negative active entries, and triples have negative active entries.
Its degree is +1. This does not evade the no-UE matrix restrictions.

I independently checked all eleven large-base and all four singleton-base
carriers, including their boundary exclusions. The exact unique free Nash
points and member gaps in the candidate agree. In particular the singleton
carriers for anchors0,1,2,3 are respectively

    (8/11,1,1/2), (1,16/19,1/2),
    (8/11,1,1/2), (4/5,0,1/21),

in increasing free-player order. For the first three, a sure free player
makes the punishment price irrelevant. Their owner-floor excesses are
57/44,27/38,57/44. For anchor3, the exact excess is
968/1575+(4/21)P₃. Never guarantees at least zero since every passive
reward to player3 is nonnegative, so P₃≥0. This is strictly positive.
The anchor3 proof using T(t)=(1+19t)/(21+t) excludes the full hypothetical
q₁>0 branch, not merely proper solutions sampled numerically.

The relevant actual consumers were read in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`:
`quittingPersistentLargeBaseExcess_nonpos_iff`,
`exists_uniformPayoff_or_persistentLargeBase_pos_gap`,
`quittingSingletonBaseOwnerFloorExcess`, and
`exists_uniformPayoff_or_singletonBase_pos_gap`.
The actual price is `quittingPunishmentValue`, not a stationary Never
surrogate. A successful smaller free set would extend by zero hazards to a
full-complement induced Nash point, already excluded by the complete census.
Thus the earlier coarse-regret redundancy argument does not repeat here.

All fourteen pure child witnesses also check. At each listed T, every
advance margin is nonpositive, every withdrawal margin is nonpositive,
and the omitted joining margin is strictly positive. For nonsingleton T,
the withdrawal comparisons are strict; singleton owners have own1 and
Never opponents. Consequently these are actual zero-debt, zero-Never child
equilibria, not just local rows. The same rows contradict all five
`WithdrawalFutureJoinRewardCertificate` kinds in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`,
using their actual nonnegative weights and restart floors bounded by own1.

The following bounded comparisons were checked against their actual inputs:

- Every pair partition has a pair containing b with b's joining gap
  −1, −1, or −4, so the weak complementary-odds pair criterion fails.
- Both harmful matching words have b's participant premium −2 below its
  harmful singleton gap −1. The arbitrary-passive favorable-matching
  producer fails there. The general nonnegative-premium inverse class fails
  as well. Since Γ⁻¹ is strictly positive, a signed-column cone must have
  all column signs positive, again incompatible with b's negative premium.
- The below-singleton two-pair architecture fails on its within-A pair:
  W_i=s_i+c_ijX_j>s_i for every proper partner hazard. This excludes the
  actual all-below-floor local branch, not just its central table.
- The positive singleton graph has only two disjoint two-cycles. The actual
  cyclic-child and signed four-cycle raw tables require a missing positive
  three- or four-cycle. Each deleted triple inverse has a negative diagonal.
- `PairedCycle.RawRegion.eq_partner_of_singleton_lt` in
  `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` permits only
  one below-own singleton per recipient, whereas each row here has two.
- The pure A profile violates `HasProductLowQuittingPremium`. The grand
  coalition is a premium trap, so the greatest premium core is all four.
  The actual `exists_uniformEquilibriumPayoff_of_weakJoiningAttractive_core`
  in `UniformEquilibrium/Quitting/Classification/Existence/JoiningAttractiveCoreRewardClosure.lean`
  requires greatest-core cardinality three, not merely a triple trap.
- Every player has a below-own participant reward, leaving no protected
  player. The trap A has strictly positive proper-subset leave sums, so it
  fails weighted-leave and boxed-charge hypotheses. A global nonnegative
  floor weight must vanish on0,1,2 by coalition{3}, then on3 by coalition{0}.
  The exact definitions in `SupportSpecificQuittingPremiumLeavers.lean`,
  `WeightedQuittingTrapLeavers.lean`, and `BoxedQuittingNashCharges.lean`
  under `UniformEquilibrium/Quitting/Classification/` were inspected.
- All ordered one-sided upper guards fail at the listed pure coalitions.
  For the two-sided half-polynomial source, positivity of the full inverse
  and `QuittingHalfWeakPolynomialGuards.reciprocal_pos` force reciprocal
  pair01 or23. Their actual upper-face displacements are respectively
  9/2 and3/4. The definitions were read in
  `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean` and
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`.

There is one necessary wording precision in the opposite-sign comparison.
The fixture has c₂₃=c₃₂=−4: a pair with two negative joining gaps does
exist. But23 is a favorable singleton pair. The accepted opposite-sign
producer requires its scheduled negative-joining pair to be a harmful
singleton pair, as in its explicit raw singleton equations. Under either
harmful matching, the within-A pair has two positive joining gaps, and the
pair containing3 has opposite signs. Thus the actual source exclusion is
correct under every relabeling. It should not be phrased as absence of
every negative-joining pair. The same sign test survives positive playerwise
affine transports.

An additional complete response-partition exclusion is available. At the
all-sure profile the displacement vector is (−1,−1,−1,1/20), so no block
can join3 to another player. A block02 or12 fails at the external singleton3
column because its two Γ entries have opposite signs. The only remaining
nondiscrete possibility is block01. At q=(1/2,1/2,0,1), its displacements
are21/4 and−19/4, again opposite signs. This excludes all fourteen
nondiscrete partitions even after positive playerwise affine changes.
The discrete quotient is Γ with determinant45, not the required negative
determinant. I inspected `QuittingResponseInvariantOnUnitCube` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
and `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.

Strict raw slack gives a full sixty-coordinate neighborhood in the new
existence class. Finite-game Nash graph compactness, the complete center
carriers, and the 1-Lipschitz reward dependence of punishment give a possibly
smaller full neighborhood with every concrete-base excess still positive.
This argument selects no common Nash point. It is not an exclusion of
arbitrary unlisted local-center producers, and the candidate correctly
does not claim one.

## 6. Exact stationary certificate: the boundary of the coverage claim

The center has a stationary equilibrium supported on {0,1,3}, with no sure
quitter. This can be certified exactly, not merely found numerically.
For odds (x,y,z) on these players, the active sign numerators are

    F₀=10y²z²+11y²z+y²+(21/2)yz²−yz/2−3y+z²/2+z,
    F₁=−10x²z²−9x²z+x²−(19/2)xz²−xz/2−3x+z²/2+z,
    F₃=−(4/15)x²y²−(19/15)x²y−x²
        −(19/15)xy²−2xy+x−y²+y.

Let f=(F₀,F₁,F₃), c=(251/5000,357/400,389/2500), and J=Df(c).
Its rows are

    (0,306099757/125000000,4645839/312500),
    (−1317311049/390625000,0,371705467/390625000),
    (−507299979/250000000,−18811758557/18750000000,0).

Exact rational calculations give det J>45, ‖adj J‖∞<83,
‖J⁻¹‖∞<2, and ‖J⁻¹f(c)‖∞<3/100000. The total absolute coefficient
sums of all second partials of F₀,F₁,F₃ are253,235,132/5. On the
infinity ball of radius1/1000 about c, T(v)=v−J⁻¹f(v) therefore has
Lipschitz constant below506/1000 and maps the ball strictly into itself.
It has a unique fixed point there, all three odds positive and finite.

For inactive player2, set D=(1+x)(1+y)(1+z),
N₂=1+x/2+y/2+2xy+4xz−7yz+2xyz, and
A₂=4z+xy+3xz+3yz+3xyz. Its sign numerator is
F₂=(D−1)N₂−DA₂. At c,

    F₂(c)=−44223662610869822129/25000000000000000000<−7/4.

A unit-cube Lipschitz bound380 gives F₂<−7/4+380/1000<0 on the
whole ball. The active equalities and this strict inactive inequality
prove stationary terminal Nash against arbitrary behavioral replacements;
each player has a positive-hazard opponent, so the same geometric argument
also gives a fixed UE target. Invertibility persists, so this stationary
certificate continues throughout some full reward neighborhood.

The full derivation, table, and rational bounds are also preserved in
Section33 of `../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`.
This is supporting internal mathematics, not a new export claim.

The existing concrete-base producers cannot select this profile: all their
full-complement induced Nash carriers fail, as checked above. The separately
inspected `exists_nearby_oneDate_sameProfile_horizon_equilibrium` in
`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyHorizons.lean`
uses the literal `nearbyRoot` with a sure anchor, defined in
`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyInteriorRoot.lean`.
It is not an arbitrary-table selector for the present proper-three root.
A generic supplied-stationary-certificate consumer, or an IFT applied after
this new exact calculation, must not be mislabeled an already available
raw criterion covering the candidate family. Thus the stationary discovery
does not reverse either verdict above. It fixes the honest nonclaim:
neither absence of stationary equilibria nor temporal necessity is proved.

## 7. Separately checked structural input weakenings

These are mathematical deltas for a possible strongest assembly, not edits
to the frozen notebook or claims of additional kernel coverage.

First, replace the coefficientwise b caps by the seven finite inequalities

    P_b(R·1_S)≤0,       ∅≠S⊆A,

where P_b is the actual polynomial in Section3. Since P_b(0)=0 and P_b
is multi-affine, interpolation on the box ∏_j[0,R_j] proves P_b≤0
throughout it. Zero-length sides can be removed or treated by continuity.
The feasible-odds proof already places every produced root in that box,
so no other argument changes. This strictly weakens the raw coefficient
restriction. At the center, change only r₃(013) to11/10. The seven vertex
values, in order0,1,2,01,02,12,012, are

    −8,−8,−8,−72/5,−304/15,−304/15,−368/15.

They are strictly negative despite a positive b triple premium, which the
old coefficientwise condition forbids. This is a produced raw extension,
not a cap assumed only at an externally supplied root. The center's other
source census is not automatically transported to this modified table.

Second, for each i∈A separately, r_i(ib)≤s_i can be replaced by the
disjunction of that original cap or

    Π_ij,Π_ik,Π_iA≥0  and  r_i(ib)≤r_i(b).

In the new arm U_i≥s_i and ΔU_i≥0, hence actual U_i*≥s_i. For both
active and inactive players the actual policy identity is

    W_i*=(U_i*+X_b r_i(b))/(1+X_b).

Therefore its passive Quit endpoint
(s_i+X_b r_i(ib))/(1+X_b) is at most W_i*. The A-date endpoint
argument is unchanged, and so are compactness, degree, support, and the
behavioral and horizon estimates. This verifies the changed assumption
using corrected actual values, not just nominal ones. It is compatible
with the seven-vertex b cap. A final artifact incorporating these two
deltas should be checked and bound to its own exact bytes.

## 8. Final strongest artifact: bounded assembly and changed-surface check

The complete 690-line artifact
`../exports/TRIPLE_SINGLETON_COLLISION_BOX_UNIFORM_EQUILIBRIUM.md`
has SHA256
`fe00a5c0ddb505f462c794823e9a3ba20eba8e2f57c5344852faabcb6b0cb3c7`.
I read the entire artifact, checked that exact identity, and compared it
with the substantive review and separately checked deltas above. No
counterpart review was read. Final-artifact verdict: PASS, with no unresolved
mathematical or self-containment objection. No Lean seal is asserted.

The final statement correctly includes the seven vertex caps and the
per-player passive-cap disjunction. The interpolation proof covers zero
box radii explicitly. The alternative passive cap is proved using the
corrected actual policy equation, including inactive players. No strict
own-level, full-support, or nonnegative passive-reward assumption has
entered the production theorem. The compact feasible set, global degree
zero, local degree one, singleton-support exclusion, and unconditional
original-game source split remain unchanged.

I directly checked both new strict-scope tests. Raising only r₃(013) to
11/10 gives the asserted seven vertex values and a positive triple cap
coefficient. Separately, changing r₂(02),r₂(12) to1 and r₂(23) to2
gives c₂₀=c₂₁=1, M₂=1, B₂=3, and R=(3,3,8). The other pair
joins stay positive, all three c_iA stay1, and player2's new arm has
Π₂,02=Π₂,12=0, Π₂,A=1 with 2≤r₂(3)=4. Its box is contained in
the original box. These are valid strict raw enlargements. The artifact
does not transfer the original center's separate source census to either
modified table.

The original center's seven vertex values are −8 on singletons,
−304/15 on all three pairs, and −152/5 on the triple; the assembled
table is unchanged. The LCP calculation now explicitly uses residual
ΓX−1, hence offset−1 under the tracked offset+ΓX convention.
The repaired opposite-sign paragraph explicitly acknowledges c₂₃=c₃₂=−4
and excludes only the required harmful scheduled pair. That resolves the
one wording issue recorded in the base review.

The full fifteen-base census, punishment-valued owner test, fourteen-child
rows, guard tests, and proper greatest-core distinctions were retained.
The fixed-profile behavioral and horizon proof retains every opponent
survival factor, the initial-zero convention, actual corrected values,
and the same target before every accuracy. No equilibrium or strategy is
an unproduced input. The new raw class and its open neighborhood remain a
genuine bounded source separation, not an extension of the retired CCE
claim and not a claim that temporal play is necessary.

All cited source paths exist in the production tree and are the named
mathematical dependencies or exact raw comparisons checked above. The
artifact contains no conference-note dependency, review link, author credit,
history narrative, untracked computation input, or unstated appeal to this
feedback. Its elementary arguments, finite data and coverage calculations
are included inline. The Lean handoff accurately separates the new raw
predicate, produced complementary root, behavioral profile, and original-
game UE consumer; it does not portray them as already implemented.

## 9. Changed-surface review: two good triple rows suffice

I independently checked only the final section “Two good triple rows
suffice: a structural producer extension” in
`../notes/CODEX_NOETHER__NONLINEAR_PHASE_ESCAPE_AND_BOUNDARY_GLUING.md`.
The 330-line full note has SHA256
`44bf7c6452cd0bb653ac5d5828ddec1c57195d7420a1be089634f8bf08693bc2`;
the reviewed final section has SHA256
`43ab62272f8f9db0c6732d0b3dea9c221b1c173fef0786567f0535a0982f2e08`.
Verdict: PASS. This is a further genuine weakening of a structural raw
input, not an improvement of a numerical bound. It does not imply that
all remaining tables have the required good rows. No counterpart review
was read, and the preceding 690-line artifact verdict remains separately
bound to its original bytes.

Precisely, choose G⊆A with |G|≥2. All six c_ij stay strictly positive.
Require c_iA≥0 only on G, and either G=A or some i∈G has Γ_ib<0.
Each good row may use either reviewed passive-cap arm; every bad row
must use Π_ij,Π_ik,Π_iA≥0 and r_i(ib)≤r_i(b). Define R_j using
only i∈G−{j}, a nonempty set, and retain the seven actual box caps.

For every feasible e(X)≥0, each good row has L_i≥0 and P_i/D_i≤M_i,
so L_i≤B_i. These rows bound every A coordinate by the new R_j. A
good negative Γ_ib then bounds X_b. If G=A, R₀ supplies such a row;
otherwise its existence is an explicit raw hypothesis. Thus all shifted
homotopy zeros remain in one compact set. No estimate from a bad row is
needed. Local quadratic isolation uses no triple coefficient sign, and
the singleton-support argument uses only c_ij>0: the offending triple
monomial vanishes on a singleton support. Hence nonzero produced support
still has at least two positive finite odds.

For a bad row, nominal W_i may indeed be below s_i. The proof does not
reuse that false floor. Instead Π_i coefficients nonnegative give
U_i≥s_i, and the residual correction gives U_i*≥U_i. The unchanged
actual policy identity W_i*=(U_i*+X_b r_i(b))/(1+X_b) proves the
passive Quit cap directly. The active Quit endpoint equals nominal U_i
and is therefore at most U_i*, with equality for active i. The positive
inactive corrections depend on e_i≥0, not on L_i≥0. All corrected
equations, including inactive b, remain valid; period contraction identifies
their values with actual bounded payoffs. The full behavioral and uniform-
horizon proof follows with the same opponent survival argument.

The exact strict-inclusion test also checks. From the original complete
table, change only r₂(01)=3, r₂(02)=r₂(12)=1, and r₂(23)=2.
With G={0,1}, both good triple joins are1 and both Γ_ib are−1.
The bad triple join is c₂A=−1, while its three Π values are0,0,1
and 2≤r₂(3)=4. Pair joins c₂₀,c₂₁ become1; all others retain
their positive values. Good-row B values are4,4, so R=(4,4,8) and
the unchanged anchor polynomial has exactly the old strict vertex caps.
Thus the new predicate admits this full table and the earlier all-three-
good predicate does not. No source-separation census is transferred to
this stress modification; the original strict center still witnesses
the already established coverage distinction.

## 10. Final two-good-row artifact fidelity

The strongest final artifact is the same standalone path as Section8,
now 716 lines with SHA256
`8d60675e258ef8166f77e64e9c0e353d9ab5430bdc6d9ed0d5f52e09ea0401b6`.
I checked the changed statement, good-row compactness proof, passive
endpoints, exact four-coordinate stress, and handoff against the approved
690-line artifact and the independently checked Section9 extension.
Final bounded artifact verdict: PASS. No counterpart review was read,
no new strategic premise is present, and no repair remains.

In particular R_j minimizes only over nonempty G−{j}; a good negative
Γ_ib is either produced from R₀ when G=A or required explicitly when G
is proper. Only good rows may use the singleton-floor passive cap.
The bad row must use the nonnegative-Π/actual-r_i(b) alternative, and
both occurrences of the endpoint proof retain that distinction. The new
example's negative c₂A and its good-only radii are correct. The old
normalization/peeling inclusion is now explicitly restricted to G=A;
it is not asserted for the negative-third-row family. The unchanged
original center retains the previously verified complete source census.

This seal supersedes the final-artifact bytes in Section8, not its valid
narrower theorem. The resulting class is the strongest reviewed raw
statement; this addendum adds no further mathematical refinement and
asserts no Lean verification.

Final label-only acknowledgment: the 716-line artifact subsequently removed
only the unexplained label “ST1” from “No such ST1 inclusion”; the full
mathematical scope sentence remains. Its final SHA256 is
`8b2ed12c6be0daacbeeabc9d8c892664e080eda356cae2687f8d7fd25c5cc0c5`.
The exact changed sentence and hash were checked. PASS binds these final
bytes; no hypothesis, proof, example, or coverage conclusion changed.
