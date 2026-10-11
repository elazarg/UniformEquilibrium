# CODEX_NASH_BOX review of Section 13

Status: bounded independent ordinary-mathematics PASS for the soundness of
the four-phase raw-neighborhood producer in Section 13. This is not a
Lean check, a review of Sections 1–12, or a completeness/novelty review of
the listed coverage tests. No export or trust seal is assigned here.

Reviewed file: `notes/CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION.md`,
SHA256 `07e662fac8b04b956282713b0fd373aff495fb5f7f8b016d0a9c572415a67375`.
The review reconstructs the fifteen literal rows and the equations, rather
than treating the author's numerical equilibrium output as evidence.

## Claim checked

For the complete 15-row center table in Section 13, there exists a raw
open ball in all sixty independent nonempty-coalition reward coordinates
such that every table in that ball has an exact terminal Nash profile
against unrestricted unilateral behavioral replacements. The profile has
the deterministic pair schedule 01,12,23,03, with eight independent
scheduled hazards in (1/4,3/4), and its actual phase-A payoff is an original
game uniform equilibrium payoff. Never payoff stays zero. The radius is
existential, not quantitatively produced.

## Independent exact arithmetic

I independently entered all fifteen rows as rational vectors, built the
four policy numerators and their common denominator 1−P from (23), and
formed all eight literal endpoint residuals from (24). Exact symbolic
rational differentiation and elimination gave the following results.

- At q=(1/2,...,1/2), P=1/256. The four actual values are exactly
  (3,11/4,2,3), (2,3/2,3/2,2), (2,3,3,11/4), and
  (3/2,2,2,3/2), in the displayed phase order.
- All eight active Quit-minus-Continue residuals are exactly zero.
- All eight inactive Continue-minus-Quit margins are exactly
  1/8,15/4,2,7/8,1/8,15/4,7/8,2 in the displayed order.
- All sixty-four entries of 255 times the rate Jacobian match the
  displayed matrix K, with the displayed row and rate orderings.
- det K is exactly 16435089066040617600000, with factorization
  2^10·3^7·5^5·17^4·29·151·6421. Dividing by 255^8 gives
  det J=28792380416/31320375, so it is nonzero.

These calculations use all prescribed singleton and scheduled-pair rows,
and all triple rows entering inactive Quit endpoints. The grand row is
indeed unreachable under the prescribed profile and under any one-player
replacement: at a live date at most two opponents can be scheduled, so
even a replacing inactive player can create only a triple. Its four
coordinates can therefore vary freely without affecting any equation or
margin. This is consistent with, not an obstruction to, a sixty-coordinate
raw neighborhood.

## Producer and unrestricted deviations

The denominator is nonzero in a full Euclidean neighborhood of the center,
so F is smooth as a function on R^60×R^8 there. The invertible rate
Jacobian gives a local rate selector q(r). A sufficiently small raw reward
ball lies in its parameter domain, keeps all rates in (1/4,3/4), and
preserves the eight strict inactive margins. The policy identities are
identities of the actual periodic values U(r,q(r)), not additional unknown
continuation values. Thus owner residual zero and inactive margin positive
give exact local root Nash at every phase.

Under any complete unilateral replacement, the other three players supply
six scheduled coins per period. Their simultaneous conditional independence
on the unique live public history bounds period survival by
rho=(3/4)^6<1. Local endpoint optimality therefore telescopes against any
time-dependent or history-dependent replacing behavior, with a continuation
remainder tending to zero. This proves exact terminal Nash, including pure
Never and arbitrarily late deadlines. No bounded-controller restriction,
shared random seed, or restriction to phasewise deviations is needed.

The same argument gives E[tau+1]≤4/(1−rho), uniformly over replacing
behaviors. Since all pre-absorption payoffs and the selecting-date payoff
are zero, the difference between N-date average and terminal payoff is at
most M E[tau+1]/N when M bounds absolute rewards. The stated
8M/((1−rho)N) bound on average unilateral gain follows by applying this
twice. In particular one original-game target U_A is fixed before the
accuracy and one profile works for all sufficiently large horizons.

## Exact project semantics inspected

The ordinary proof supplies precisely the three hypotheses of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`: actual policy
recursion, exact phasewise `IsεQuittingRootNash` with error zero, and
playerwise opponent-cycle contraction. That declaration passes from live
hazards to arbitrary complete behaviors via
`quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue`.
The same file's
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
has exactly these hypotheses and concludes the original-game uniform
payoff statement. I also inspected
`IsQuittingCyclicResponseSolution` and its Bellman-cap use in
`UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`.
These declarations confirm the relevant semantics; the new table, Jacobian,
and implicit-function argument are still ordinary mathematics, not checked
Lean instances of those declarations.

## Remaining scope

I found no mathematical objection to the stated local-existence producer.
The bounded source-coverage comparisons in the last part of Section 13 were
not audited by this review. In particular this PASS does not establish
that every table in the neighborhood avoids all existing sources, or that
the center lacks other types of equilibrium. An independent coverage check
is still needed for any strict-new-coverage export claim.

## Bounded final-document addendum

I checked `notes/CODEX_TURING_BOX__FOUR_JOINT_PHASE_CYLINDER.md`, SHA256
`42782d67edba1fb65ed8f7059c03a94650d49f907023beef98c91996df48c1da`,
against the soundness review above. The assembled statement and proof
faithfully carry the reviewed proper-row center, four values, eight owner
equalities, eight inactive margins, full Jacobian and its determinant. The
derivative recurrence and its center forcing are transcribed correctly.
I additionally recomputed rational Gaussian elimination after precisely the
row swaps (0,1) and (2,3). All eight new displayed diagonal pivots match:

    249, 504, 63746/63, 85850/83, -40163520/3219173,
    842743233/98440, 97699680/4928323, -35849887725/606632.

Their exact product is 16435089066040617600000, with positive net row-swap
sign, as claimed.

The strengthening from a raw sixty-coordinate ball to the open proper-row
neighborhood times ANY finite grand row is valid: every equation, prescribed
outcome and unilateral-deviation outcome uses at most a triple. It loses no
contraction or local-Nash hypothesis. The same proper-row radius therefore
works independently of the four grand entries.

With radius at most one, the largest absolute proper center reward is ten,
so the uniform reachable-reward bound M=11 is valid even when the grand row
has arbitrarily large finite entries. This is the only reward bound needed
by the deviation telescoping and finite-horizon estimate; the grand row
cannot be realized under any replacement. The selecting-date zero, complete
behavioral deviations, private independence, fixed target before accuracy,
and existential-only radius qualifications are all retained. Bounded
final-document PASS; this addendum is not a fresh coverage audit or a new
Lean/export seal.

## Independent Section 15 rectangle-producer check

Checked frozen whole-file SHA256
`797f0737c9b3682d579093625c020691fb0f170ba6a0863cf1011d695666ec84`,
Section 15, on 2026-10-11. Verdict: PASS for the producer of Sections
15.1–15.4. This is independent ordinary-mathematics evidence, not a Lean
seal, not an arbitrary-table theorem, and not a full new-coverage audit.

I independently reconstructed the literal scheduled singleton/pair rewards
and expanded every actual policy recursion. With b=g/[2(1-g)] and
d=a/[2(1-a)], the sixteen recursion residuals

    U_t - immediateReward_t - survival_t U_(t+1)

are exactly (1-a)F_A at A0,C2; (1-g)F_B at B1,D3; and zero at the
other twelve coordinates. Separately recomputing all eight active
Quit-minus-Continue gaps gives F_A at A0,C2, F_B at B1,D3, and zero at
A1,B2,C3,D0. Thus no continuation vector is being supplied independently
of the actual policy. At a two-variable zero, the contracting periodic
recursion identifies all four proposed value vectors with actual payoffs.

All rectangle estimates hold literally. For e=1/(4M),
h=(1-e)/(3/2-e) satisfies b(h)=d(h)=1-e. On the rectangle, all rates
lie in [1/6,1-e], a,g lie in [1/4,h], and every displayed value belongs
to [0,M]. The passive formulas are nonnegative combinations with coefficient
sum at most one. On g=1/4,
z0>=1+d(V-4)/4>=5/4, hence F_A<=-1/24. On a=1/4,

    w1>=bS/4+(1-b)gW/8>=3/2,

so F_B<=-1/12. The upper g face gives F_A>=3/4. The upper a face
actually gives F_B>=7/4-e, stronger than the stated 3/4. Coordinate
order (F_B,F_A) is correct. The rectangle zero is strictly interior.

I read `exists_rectangular_zero_of_strict_face_signs` in
`MathUE/Topology/RectangularPoincareMiranda.lean`. Its global-continuity
hypothesis is satisfied by composing the displayed rational field with
coordinatewise clamping into this rectangle; denominators remain positive.
The source's two-variable zero theorem is sufficient. The larger
`exists_uniformEquilibriumPayoff_of_periodic_rectangular_face_signs`
declaration is not being misused as a two-coordinate/eight-slot adapter.

I enumerated all eight inactive Quit endpoints. Each contains exactly one
barrier from r0(02),r2(02),r1(13),r3(13), with coefficient a scheduled
hazard times the other scheduled Continue probability. That coefficient
is at least e/6=1/(24M). The other terms are precisely singleton one,
scheduled pair participant reward at most five, and one of the eight
listed triple coordinates, hence all are <=L. A barrier <-24ML gives
strictly negative total Quit value. Prescribed Continue is nonnegative.
The arbitrary F coordinates do not enter prescribed rewards or the
replacing player's own reward under any unilateral replacement; the
literal support enumeration in Section 14 supplies this fact without
discarding any realizable triple.

At the produced zero all rates exceed 1/6. Removing ANY replacing player
leaves six prescribed opponent coins per period, so survival is bounded
by rho=(5/6)^6<1 independently of that replacement. The already reviewed
endpoint telescoping and the inspected
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` therefore
apply with their actual recursion, exact root Nash and deleted contraction
hypotheses. A finite table-dependent reward bound suffices for uniform
payoffs; no uniform bound over the arbitrary F or triple coordinates is
needed. The target is the original table's actual phase-A payoff and is
fixed before an accuracy is chosen.

### Additional bounded arithmetic check of Section 15.5

I reconstructed all fifteen rows of (39) and independently expanded the
three induced-player differences for EACH sure owner. Equations (40),
(41), and every stated owner2/owner3 grand-row correction are exact. The
support classification following them is also valid: for owner0/2,
positive z forces the stated small x bound, then d2<0 and d1>0 give a
contradiction; for owner1/3, positive z forces y>=K/(K+1), then d0<0
forces x=0, and z<1 is impossible. The listed Nash sets and floor gaps
K+Vx or K+Sy follow, with zero opponents-Continue mass, so they do not
depend on an assumed punishment value.

This extra calculation does NOT audit every subsequent named-source
containment assertion, does not establish disjointness from all prior
qualitative neighborhoods, and is not the second coverage/export gate.
There is no mathematical objection to the raw rectangle producer found
in this bounded review.

## Bounded Section 17 addendum: actual cyclic adapter and uniform consumer

Status: independent ordinary-mathematics PASS for Sections17.5--17.6 and
their stated growing-period versus period-one scope. This is NOT another
full quantile/splice audit (CODEX_EMMY_BOX was assigned that part), NOT a
Lean build, and NOT an unrestricted producer of the concentration family.
Coverage verdict: NOTES ONLY;
the proposed varying-period branch elimination and arbitrary-profile
singleton target theorem are already consumed by existing sources. The
quantile construction is a sound alternative proof with zero new
consumer/source coverage established.
Reviewed whole-file SHA256:
`56e66c347e124ee6c1d5fad059793c4661d69cf168e7a65cbcd7f9697d70259f`.

### Exact claim checked

Suppose an ACTUAL independent family has terminal singleton{i} mass
tending to one, all outsiders' COMPLETE terminal debts tending to zero,
and the fixed owner's behavioral punishment value at most its own
singleton d. If the quantile/splice estimate(48) holds, the original
singleton VECTOR s is one fixed uniform-equilibrium payoff. Further,
the existing owner-concentration arm of `InteriorCyclicDebtEscape` supplies
precisely this actual family for an arbitrary supplied period schedule,
including unbounded periods. Under Fin4 no-UE the owner's normality is
automatic, so this arm is eliminated, retaining only vanishing displayed
hazard on a selected source subsequence. This is an arm consumer, not a
new arbitrary raw-table exclusion or producer of every needed branch.

### Actual source extraction

I read `InteriorCyclicOwnerConcentrationSubsequence` and
`InteriorCyclicFixedDebtorSubsequence.nonempty_ownerEscapeAlternative` in
`UniformEquilibrium/Quitting/Cycles/InteriorCyclicDebtEscape.lean`, and
`exists_interiorCyclicFixedDebtor_and_ownerEscape_of_terminalGap` in
`UniformEquilibrium/Quitting/Cycles/InteriorCyclicTerminalDebtRatio.lean`.
The profile is exactly

    sigma_n=quittingCyclicBehaviorProfile reward
              (block(data.select n)).cycle (initial(data.select n)).

No substitution of a different Nash row, stored payoff, or relaxed law
is needed. `terminalOutcomeMass_tendsto_singleton` is convergence of the
ACTUAL terminal-outcome law, and
`quittingSingletonTerminalOutcomeMass` in
`UniformEquilibrium/Quitting/Cycles/OwnerSingletonCyclicConcentration.lean`
is the point mass on the SOME singleton coalition, with zero Never mass.
Evaluate the convergence at that coordinate to obtain
alpha_n=1-P_sigma_n(singleton{i})->0. The explicit
`outsiderDebt_tendsto_zero` fields are actual complete behavioral debts,
not just local Bellman errors. Since the player set is finite, their
coordinatewise convergence gives a maximum tending to zero. The
`ownerDebt_floor` field is allowed to persist; the construction changes
the owner-relevant suffix and is precisely what must remove this debt.

The escape producer's hypothesis is EXACTLY

    ((period n+1):R)*error n ->0,

because its actual cycle has `period n+1` phases. No uniform upper bound
on `period n` is imposed. In the positive-own-absorption branch the
existing proof passes this product through the displayed strict
subsequences and divides by a fixed positive absorption floor; this
supplies outsider-debt convergence even when the period grows. Thus the
adapter does not silently replace the source error by a fixed-period one.

### Fixed-target passage, including arbitrary horizon deviations

From(48) choose theta_n=sqrt(alpha_n) when alpha_n>0 and sufficiently
small, any positive vanishing theta_n when alpha_n=0, and eta_n->0.
The cutoff profiles have actual payoffs converging to the fixed original
table vector s and maximum complete debt tending to zero. Discarding
finitely many indices is harmless. For every epsilon choose a member
whose terminal Nash error and target discrepancy are both below, say,
epsilon/2. This is exactly terminal target acceptance, with no chronology
or compatibility requirement between chosen members.

I inspected `quittingGame_uniformPayoffWitnesses_of_terminalTargetAcceptance_family`
and `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The first explicitly RETAINS an accepted member of the supplied family
and proves ONE threshold for all sufficiently long horizons, full
behavioral Nash and delivery to s. Its proof spends a strict terminal
error margin, then combines uniform Nash with the selected profile's
ordinary payoff convergence. Therefore no UNIFORM tail rate over the
sequence, no proper punishment clock, and no interchange of limits is
needed. In particular this is not an invalid inference from pointwise
convergence of finitely supported deviation payoffs. The required
uniform upper-deviation theorem is actually present in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`
as `quittingGame_hasUniformDeviationUpperApproximation`; it treats both
positive and negative own-singletons and includes complete deviations.

The punishment premise matches the project exactly:
`quittingPunishmentValue` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` is the infimum over
actual opponent plans of the complete best-reply cap.
`exists_quittingStationaryPunishmentRoot_lt_add` in
`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean` supplies
the near-optimal constant independent opponent row; changing the punished
player's prescribed coordinate does not affect its cap.

Finally I inspected
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`
and `all_punishmentNormal_of_normalCore_eq_univ` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`.
They give precisely chi_i<=d from Fin4 no-UE, without requiring d>=0.
The produced singleton UE contradicts that no-UE assumption. The owner
concentration branch is thus impossible for any SUPPLIED source family
satisfying the exact period-error product hypothesis.

### Bounded overlap verdict

`false_of_periodOne_ownerConcentration_of_finFour_noUniformPayoff` in
`UniformEquilibrium/Quitting/Cycles/PeriodOneOwnerConcentrationContradiction.lean`
already eliminates the period-one arm. I read its statement and proof:
it uses a compact EXACT solo root limit, which this proposed adapter does
not assume or construct. The quantile construction genuinely permits
unbounded periods and retains the actual source only until its explicit
legal suffix replacement. Existing period-one diffuse-source existence
does not imply a branch-consumer theorem for an arbitrary supplied
growing-period source; conversely the new consumer makes no stronger
claim about existence of SOME diffuse source.

I also inspected
`isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits` and
`isUniformEquilibriumPayoff_soloReward_of_summableConditionedDeletedClock`
in `UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean`.
They require a specific root/continuation chronology, vanishing root
hazards/target/pure-Quit errors or a conditioned summable deleted clock.
The supplied cyclic family's actual initial root supplies all needed
root data for this existing consumer.
For the concentration subsequence, take that initial root, its actual
Bellman value, and local error. Interiority gives a positive owner hazard;
initial opponent absorption is at most one-cycle opponent absorption and
tends to zero; actual values converge to s; and the local Nash inequality
bounds every outsider's pure-Quit endpoint by its current value plus
local error. Since local error<=period-times-error, it tends to zero.
These are EXACTLY `isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits`'s
hypotheses, with no bounded-period requirement. The whole-family total
hazard limit follows by applying this existing arm exclusion on any
subsequence whose total hazard stays bounded below.

The exact quantile construction is already recorded as QCUT1--QCUT7 in
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`. I read QCUT1--2,
QCUT5--6, and the actual source adapters in
`feedback/CODEX_MORSE__QUANTILE_PUNISHMENT_REPAIR__BY_CODEX_NOETHER.md`;
the latter also proves the arbitrary-profile overlap. For each profile
take the earliest positive OWN finite atom alpha at time T. No owner
clock is earlier, so opponents' cumulative mass through T is at most the
singleton failure probability alphaFailure. Removing other opponents
then compares each outsider's pure deadline T to the solo-root Quit
endpoint with error at most2R*alphaFailure. Together with target delivery,
the solo root's COMPLETE outsider cap is at most its singleton target
plus outsider debt plus4R*alphaFailure. The exact solo cap identity and
`isUniformEquilibriumPayoff_soloReward_of_approximate_caps` consume these
positive rates and vanishing errors with the same normality premise.
No lower bound on the extracted rates is required. Thus neither the
arbitrary concentration theorem nor growing-period branch elimination
is established as new by17. The legal prefix-preserving quantile proof
remains a correct alternative construction, but this does not justify
a redundant export or claim of a new conjecture-facing delta.

No mathematical objection was found in the adapter or full-uniform
passage within the bounded scope. No new source/consumer coverage is
established, and no redundant export is recommended.
## Bounded review of Section 19: the full passive-reward ray

Reviewed frozen whole-file SHA256
`26f92117e3f456ac3695aaf2113b72723472d082363ea04ee0e0eb9992e291d8`,
Section 19 only. Reviewer: CODEX_NASH_BOX. This is an independent ordinary
mathematical check, not a Lean gate or an exhaustive source-completeness
claim. Earlier cyclic all-behavior consumer facts already checked in this
feedback are reused, not audited anew.

Verdict: PASS for the stated raw-family existence theorem and the bounded
source-separation claims checked below, subject to the explicit nonblocking
boundary-limit wording correction at the end. I found no objection to the
producer, actual payoff identification, endpoint inequalities, or unrestricted
terminal/finite-horizon consumer. The new point is an entire K>=0 ray,
not merely a failed selected branch or a favorable supplied root.

### Independent producer and policy calculation

At T<A<4, D=sqrt((4-A)/(A-1)) is in (0,(3-sqrt(5))/2), and
J=sqrt((A-1)(4-A)) is in (0,1). Thus C=(1-D)(1-J)>0 and
Kcrit=C/(1-sqrt(D))^2 is positive and finite.

For the symmetric scalar function, direct differentiation gives
f'_K(0)=(A-4)-(A-3)=-1. With z=sqrt(D) and
4-A=(A-1)z^4, direct substitution gives

    f_K(1-z)=1-z^2-(A-1)(1-z)(z^2+z^3)-K(1-z)^2
              =(1-D)(1-(A-1)D)-K(1-z)^2.

This verifies the exact endpoint C-K*qstar^2. A negative point sufficiently
near zero and the nonnegative endpoint supply a POSITIVE root in
(0,qstar], including K=0 and equality K=Kcrit. The zero at q=0 is not
mistakenly selected.

For K>Kcrit, x=C/K lies in (0,(1-sqrt(D))^2). The displayed radical
roots have positive sum s=1-D+x and product x. Their discriminant is

    [x-(1-sqrt(D))^2]*[x-(1+sqrt(D))^2]>0.

Their Continue probabilities have positive sum 2-s and product D>0,
so both hazards are strictly between0 and1. This verifies legal proper
hazards, ab=x and (1-a)(1-b)=D, without a numerical root test.

The literal complete table is equivariant under tau=(0 2 1 3), including
both oriented cross pairs and all four triple rows. For instance
02=(B,K,-B,K) maps to12=(K,-B,B,K); favorite01 maps to23. The policy
has the same phase equivariance. At phase0 its actual Quit endpoints are
L=1+(A-1)b and H=1+(A-1)a, and its Continue endpoints are
4b+(1-b)Z and4a+(1-a)W. The passive recursions are exactly
W=K ab+dL and Z=K ab+dH. In the symmetric branch both owner equations
are the same scalar root equation, not only their difference.

In the asymmetric branch, substituting D^2=(4-A)/(A-1) gives

    W-[1+(A-4)a/(1-a)]
      =Kx+D-1+(A-1)D[b+a(1-b)]
      =Kx-(1-D)(1-(A-1)D)=0.

Interchanging a,b proves the SECOND owner equation. Thus all sixteen
policy coordinates satisfy their recursions, and d^4<1 identifies them
uniquely with actual policy values rather than arbitrary continuations.

The inactive Quit endpoints recompute to

    Q2=d+B(b-a)+(K-1)x,   Q3=d+B(a-b)+(K-1)x.

Their Continue-minus-Quit margins are precisely
(A-1)db+B(a-b)+x and (A-1)da-B(a-b)+x. Both are positive for equal
hazards. For asymmetric hazards these become
Jb+B(a-b)+x and a(J-B)+Bb+x, positive even at B=J. This verifies all
inactive signs by the literal symmetry. In particular the original triple
entry K-1 has not been omitted.

Deleting any player leaves three a coins and three b coins per period,
giving opponent survival d^3<1. This is exactly the contraction needed
by the previously checked unrestricted Bellman consumer. It handles Never,
unbounded laws and noncyclic behavioral replacements. The resulting live-time
sum is at most4/(1-d^3); the stated conservative C_hor=1+4/(1-d^3)
therefore gives delivery M*C_hor/N and regret2M*C_hor/N. The bound is
allowed to depend on the fixed original table through M and on its selected
hazards; no false uniform-in-K reward bound is used.

### Bounded actual source separation

I independently checked the WHOLE induced-Nash exclusion. With owner0
sure to Quit, mate1 and noncollider2 each have joining advantage respectively
A-4<0 and -B<0 when the remaining players Continue. If one further
nonowner quits, each advantage is (K-1)-K=-1; if both do it is
-1-K<0. Thus both are strictly dominated Quitters against EVERY mixed
profile. The remaining player3 then has advantage B>0 and quits surely.
This is the entire induced Nash set. Owner0 gets -B from Quit and0 from
Continue, with zero all-opponents-Continue coefficient, so no punishment
floor repairs the leave sign. Equivariance gives all owners. Combining
the free-Nash, outsider-no-join and other-base leave signs into the full
one-owner induced game proves the larger/partial base exclusion; it is
not limited to one selected pure witness.

For EVERY nonempty proper child E, a kappa boundary edge j in E,
kappa(j) outside exists because kappa is a four-cycle. At singleton{j},
the outsider's joining gain B is positive. Every available advancement
donor has gain0, A-4 or -B, all nonpositive. Every withdrawal gain is
nonpositive: the patient/restart and LP floors are at most own singleton1,
and the evaluated-security floor is explicitly capped by0. I rechecked
`deadlineSecurityGainFloor` and its singleton identity in
`DeadlineWithdrawalSecurityMixedPointwise.lean`; the K-dependent rows do
not affect this cap. This validates the named raw F/J and N/F/J failure
over all children and nonnegative donor weights, not a strategic child
nonexistence assertion.

The singleton Gamma has eigenvalues1,5,-3,-3, determinant45 and the
displayed positive inverse. Its zero-coordinate argument proves R0,
and the existing degree is+1. The balanced-singleton argument does cover
arbitrary words, repeated owners and removable zero-hazard dates: every
distinct-owner transition must stay in a mate pair, leaving the other
pair's payoff0<1. The four response-quotient displacement witnesses are
exactly +/-B and independent of K. Remaining mate/all quotients have
positive determinants and degree+1; the actual nonnegative-inverse exit
also requires NEGATIVE determinant. The proof does not incorrectly reject
the mate quotient's entrywise positive inverse.

I re-opened the actual `RawFamily` in
`UniformEquilibrium/Quitting/Cycles/BelowSingletonJointPhaseSource.lean`:
its scheduled premium<-1 and singleton-forced scale1 require both scheduled
participants negative; each cross pair here has a positive B participant.
The same singleton data fixes the favorite pairs in the other named finite
matching tests. The previously checked PairedCycle/CrossedMatching raw
criteria therefore fail for the stated reasons. The golden singleton
export's EXACT-singleton favorite cap is T, violated by A>T. The two
accepted joint-phase export regions require coordinates near5 or fixed5,
9/2, violated by A<4. The common-large-positive-pair source fails at
the literal -B participant. These give a genuine bounded new exclusion
class relative to those exact accepted sources and the WHOLE base/child
tests, not a claim excluding arbitrary supplied verifiers, unknown
qualitative IFT neighborhoods, or every stationary equilibrium.

### Required wording correction, outside the main theorem

Section19.7's A downarrow T golden-calendar limit needs FIXED K>0
(and a fixed B compatible with the range). Then Kcrit->0, the asymmetric
branch is eventually selected, a->1-D_T=(sqrt(5)-1)/2 and b->0.
For K=0 the symmetric branch instead approaches a=b=qstar at A=T,
with qstar=(3-sqrt(5))/2, not the golden one-owner/mate-zero profile.
If K scales with C, still other limits are possible. This qualification
does not change the claimed theorem for any fixed allowed A,B,K or any
of the exact endpoint/consumer computations above.
