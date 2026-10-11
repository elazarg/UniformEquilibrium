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

### Addendum: whole positive singleton-word root uniqueness

Bounded independent check of CODEX_EMMY_BOX's new coverage repair: PASS.
This replaces reliance on an unquantified IFT radius; no other part of
the Section19 audit is repeated here.

For the chronological singleton word0,2,1,3 with arbitrary hazards
p_i in(0,1), put u_i=1-p_i. The actual owner-indifference equations
from the golden singleton export are, after a cyclic reindexing,

    E_i=u_i(4-4u_(i+1)+u_(i+1)u_(i+2))-1=0.

They follow directly by substituting p=1-u in the printed cleared field;
no supplied continuation or local-root uniqueness assumption is used.
Set a=u0-u2 and b=u1-u3. I independently recomputed

    E0-E2=4(1-u1)a-u2(4-u0)b,
    E1-E3=u3(4-u1)a+4(1-u2)b.

All four displayed coefficients are strictly positive. If a or b were
nonzero, the first equality would make their signs equal and the second
would make their signs opposite. Thus a=b=0. Write u0=u2=x and
u1=u3=y. Subtracting the two remaining equations gives

    E0-E1=(4+xy)(x-y),

so x=y. The common equation is

    u^3-4u^2+4u-1=(u-1)(u^2-3u+1)=0.

Its UNIQUE root in(0,1) is (3-sqrt(5))/2. Hence every all-positive
proper singleton-word owner solution at these exact singleton rows has
the golden hazards, not merely the branch selected by IFT. Its inactive
favorite-joining test therefore necessarily imposes A<=T. The A>T
family in Section19 is excluded from the entire stated positive-hazard
four-singleton architecture, including Theorem2's hazards in(1/2,3/4).
Relabelings preserving the paired singleton pattern keep the mates
opposite in this word, so the same calculation applies. This is not a
claim excluding arbitrary singleton calendars, zero/sure hazards, or
other words of arbitrary length.

### Final passive-ray packet: faithful-incorporation check

Checked the final packet
`exports/FOUR_PHASE_PASSIVE_REWARD_RAY_UNIFORM_EQUILIBRIUM.md`, SHA256
`a2cddd539cebb427dee7e1f4254a0966f8d309730c39fb32433990a53a2cbf91`.
The fixed-K>0/fixed-admissible-B boundary qualification, the distinct K=0
limit, and the complete positive singleton-word uniqueness calculation
above are faithfully incorporated, with the same interior-hazard and
architecture scope. The quotient comparison retains the negative-
determinant requirement rather than claiming failure of inverse positivity.
No lost hypothesis or transcription error was found in these reviewed
additions. This is one bounded final-document check, not another audit.

## Section22: entire nonpositive private-tax selector

Reviewer: CODEX_NASH_BOX. Status: bounded independent adversarial PASS;
ordinary mathematics, not Lean-checked or an export review.

Reviewed ONLY Section22 of the frozen notebook, whole-file SHA256
`1c4926c8d41beceb4ecf4cd573820454d9a2840b483a52b26249d22cc31e95f4`,
section SHA256
`8e55d6932e22cd375796bd54c9971e3b41d395419cf80ee0ca19f91d812d1195`.
This block is also preserved in commit `0ac16179`. Later notebook sections
are outside this review.

### Claim checked

On the literal fifteen-row table specified by its core table and sentinel
rule (absent5, joining4, alone0), EVERY exact mixed Nash law on EVERY common
finite menu F_N with EVERY private planned-Never transfer b_i<=0 has all
activity at the final date. The pivot tax is included and is not assumed
zero. For b in[-eta,0]^4, eta<=1/100, every such law has original unrestricted
full exploitability at least18/49-2eta>1/3, although original legal products
with exploitability1/N exist.

No mathematical objection found in this scope. In particular the final
statement resolves both the earlier b0=0 restriction and the private-tax
versus reach-weighted-payment issue.

### Independent checks and falsification attempts

1. The pre-final no-sure-root proof uses a FINITE next-date deviation,
   not Never. It therefore avoids every private tax regardless of size.
   I checked the three core sure cases, including q1=q2=1 separately.
   Core comparisons are unaffected by the sentinel. If the sentinel is
   sure, the finite-Continue core comparison really has zero continuation,
   gives the unique interior rational root(2/7,4/7,1/7), and the sentinel's
   finite-next-date improvement is at leastH*=253/343>0. This establishes
   positive joint reach at every pre-final date without off-path agency.

2. Conditional tails have tax b_i/product_(j!=i)S_j(t), NOT b_i divided
   by joint reach alone. The tail terminal gain is joint-reach weighted;
   the tax change is only own-survival weighted. The sign remains
   nonpositive even when the conditional magnitude grows arbitrarily.
   The one-date high-box lemma is stated and proved at exactly this
   all-magnitude scope, so backward induction does not silently reuse a
   small-tax bound after conditioning.

3. I recomputed all three final gaps and their inverse linear solution.
   When no core hazard is sure, all are positive and the displayed
   increments are correct and nonnegative. The four-corner Quit-value
   minima are exactly31/7,19/7,34/7. For sure supports I checked all
   possibilities: at least two sure players; only0 with q2>=1/2; only1
   with q0>=1/2; only2 impossible. Their lower bounds5,4,5 (or stronger
   by coordinate) suffice. The finite sentinel Quit option gives
   v3>=4H>=1012/343>2, independent of its own tax magnitude.

4. Against ANY augmented continuation vector v>=2, the sentinel gap is
   -H-(1-H)v3<0. The three core pair supports each have the stated
   strictly negative active gap; the full-support summed-gap bound uses
   cube vertex values6,3,2,3. Thus the WHOLE ordinary root equilibrium set
   is all-Continue, not merely a stable selected branch.

5. The private-payment accounting in the backward step is correct:

       currentContinueValue=A_i+A_-i*u_i+b_i*z_i
         =A_i+A_-i*(u_i+(b_i/A_-i)*z_i).

   The b_i*z_i term is deliberately NOT multiplied by opponent reach.
   Current Quit and Continue-with-the-actual-conditional-tail are legal
   complete replacements; varying their mixture proves ordinary root
   Nash. The next conditional tail's tax is exactlyb_i/A_-i, so its
   augmented value is the continuation used by this equation. Once the
   ordinary root is all-Continue, both the value and tax remain unchanged.
   This validates the uniform-in-N backward induction.

6. At small taxes I checked the exhaustive no-sure cases and the bound
   |q_i-q_i*|<=eta, including a negative pivot tax. The sentinel has gap
   -H-b3<0. Pivot mixing gives U0=W0+b0*q0, not W0+b0 or W0 itself.
   A genuine finite clock after the menu therefore gains
   (1-q1)(1-q2)-b0*q0>=18/49-2eta. At eta=1/100 this lower bound exceeds
   1/3 by exactly103/7350. This is an original full-deviation gain, not
   auxiliary or menu-only regret.

7. I checked the uniform-pivot bypass against ALL pure deadlines and
   Never. The outsider values are(7t+8)/N,(7t+5)/N,(5t+4)/N within the
   menu; their late values are7,7,5. Only player1 has excess1/N. Hence
   the original game has zero full-gap infimum, as claimed.

The arithmetic was additionally recomputed with exact fractions, including
all corner minima, H*, the cube vertex inequality and the endpoint margin.
A coarse rational support enumeration found no incompatible one-date
large-tax case; this experiment is supplementary to the exhaustive
ordinary proof, not its justification.

### Source and conclusion boundary

The inspected single-pivot late-cap formula and terminal-all-errors
endpoint are used at their stated scope. Nonemptiness of the finite
PRIVATE-tax equilibrium set follows from the general finite mixed-Nash
theorem; the named finite-deadline theorem does not itself check this
private-transfer proof. No Lean verification of Section22 is asserted.

This falsifies the ENTIRE exact finite common-menu negative-private-tax
source, including joint deadline/tax selection and all Nash components.
It does NOT refute positive subsidies, arbitrary approximate menu products,
the original finite-menu selection question, or uniform equilibrium.

## Bounded independent check: Section23.4, growing discounted periods

Reviewed Section23.4, equations(D4)–(D12), using ONLY the literal table and
source definitions in Sections23.1–23.2. Frozen whole-file SHA256:
`0d31a84eb632ae8bac182b27b0d66b09adf4d6b2331fbae09077a1bd1209c656`,
also preserved in commit `e89e647e`. Section23.3's entire viability-kernel
identification and other notebook claims are outside this check.

**Verdict: no mathematical objection found in this bounded scope.** For
every fixed collision parameter epsilon in(0,1/3), the construction gives
exact realized-discount Nash laws on periods3k for all sufficiently large
k, with discounts tending to1, ORIGINAL unrestricted terminal
exploitability tending to0, and original payoff tending to(1,1,2).
This is an internal calibration on a previously solved three-player game,
not new Fin4 coverage or a universal discounted selector theorem.

### Finite producer and exact boundary agency

I independently derived the root equations at q=(a,b,0). The two Quit
values are1+epsilon*b and1-a. Their Continue values are respectively
alpha*(1-b)*child0 and3a+alpha*(1-a)*child1. The third player's Continue
recursion is3b-2ab+alpha*(1-a)*(1-b)*child2; its Quit value is
(1-b)*(1+epsilon*a). These are exactly(D5),(D7),(D8) and the displayed
inactive comparison.

The rotated child at the END of a phase has value

    (w_0,1,1-a_0),

because b_0=0. Thus the first-owner seam is precisely(D9), the
second-owner seam is(D7) with the virtual next a equal to0, and the
passive seam is precisely w_k=1-a_0. No port is silently identified
with an unrotated child. At the INITIAL phase date b_0=0, player1 is
allowed to Continue while indifferent; the argument does not require
strict positive activity there.

For(D5), its forward map is continuous and strictly increasing in both
lambda and b while0<=b<1. The k=2 crossing is explicit. Inductively,
increase lambda to the unique earlier crossing b_(k-2)=B: all preceding
iterates are below B<1 and the next iterate strictly exceeds B. The
intermediate-value theorem then yields a UNIQUE lambda_k(B) strictly
before this threshold. Strict monotonicity and continuity give continuous
B dependence. This verifies actual finite roots, not just formal small-
lambda expansions. Iterating b_next>=r*b+lambda/epsilon gives exactly
lambda<=B/(r^(k-1)-1), uniformly on the fixed interval I. The backward
a map preserves[0,lambda/2], so every actual a_t is positive and at most
lambda/2.

### Uniform scalar IVT and inactive inequalities

The backward b map is

    x -> (alpha*epsilon*x-lambda)/(epsilon+alpha+alpha*epsilon*x).

On the fixed interval[0,max I] its difference from x/(r+x) is bounded
by a constant depending only on epsilon times lambda. The latter map
has Lipschitz constant at most1/r<1. Starting at the SAME terminal B
therefore gives a uniform O_epsilon(lambda) error for every backward
iterate, and O_epsilon(k*lambda) for their sum. I checked the exact
comparison solution and telescoping product:

    c_j=B/[(1+epsilon*B)*r^j-epsilon*B],
    product_(j<k)(1-c_j)
      =(1-B)/(1+epsilon*B-epsilon*B*r^(-(k-1))).

These give(D10) uniformly, not merely pointwise in B. The passive
comparison uses bounded values in[0,3] and transmission factors in[0,1],
so its accumulated perturbation is O_epsilon(k*lambda), including the
terminal error a_0. Substitution gives EXACTLY(D11). Its only zero on
I is B*=1/(2+epsilon); its signs at the two endpoints are strict and
opposite. Consequently actual roots B_k exist for every sufficiently
large k, and EVERY such selection tends to B*.

At every t<k the remaining b product contains the final1-B_k factor.
Hence the passive comparison value is at least1+2B_k, uniformly in t.
Its perturbation tends uniformly to0, whereas the inactive Quit value
is at most1+epsilon*lambda_k/2. Since B_k>=B*/2, the stated strict
passive margin holds at ALL dates, including both phase endpoints.
After rotation these checks cover every player/date family.

### Actual unrestricted discounted and terminal conclusions

The bounded periodic ports satisfy the actual Bellman equalities, not
only owner equations. Their prescribed remainder vanishes as alpha^n.
For any pure deadline the root Nash inequalities telescope to its full
discounted payoff bound, including the deadline at a phase boundary.
For Never the same bound follows by the vanishing remainder. Arbitrary
complete clock laws are mixtures of these replies. Thus the constructed
laws really are exact discounted Nash against ALL behavioral replacements.

Each individual law survives one3k-date period with probability
J_k=A_k*P_k. The independent opponent pair therefore survives a period
with probability J_k^2. I checked the limit J_k->1/2 and the geometric
bound

    E[T_-i+1] <= 3k/(1-J_k^2).

This bound is UNCHANGED by any full deviation of player i; opponents are
proper, and absorption under that deviation occurs no later than their
first quit. Since |r_i|<=3 and1-alpha^t<=lambda*t, both the prescribed
payoff and EVERY replacement payoff differ from their original terminal
counterparts by at most9*lambda_k*k/(1-J_k^2). Exact discounted Nash
therefore gives the full bound(D12), including omitted late deadlines
and Never. The first port converges to(1,1,2), and the SAME uniform
comparison transfers that payoff to original terminal play.

The fourth player's specified padding pays-1 whenever it joins and0
otherwise; its literal Never has value0 and dominates all complete
replacements, discounted and original. Core deviations keep this player
Never, so the padded conclusion is valid but still three-active.

The named source bridge `discountedAuxEU_quittingGame_none` in
`UniformEquilibrium/Quitting/Bellman/Discounted/PayoffBridge.lean` has the
extra common positive discount factor described in Section23.1; it does
not change Nash. Pure-clock extremality has the stated full-agency scope
in `sSup_range_quittingTerminalPayoff_update_eq_pureTime`,
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
The ordinary proof above is not claimed Lean-checked.

The successful ingredient is a finite-parameter scalar sign change
creating a macroscopic b burst while total discount and companion-a
loss are O(k*lambda). The special cyclic reward rows supply that sign
change; no arbitrary four-player producer or completeness claim follows.

## Section 25.3: actual small-conditional-hazard full-regret floor

Reviewed source: Section 25.3 at whole-file SHA256
`55b7be2d4d22b57a7a2d2ab26ecb2a8d656ce83985820d17df524eece52d11f5`.
Verdict: PASS for the stated whole actual-profile mode. This is ordinary
mathematics, not Lean checking, a full-game positive-gap example, or a
new reward-table equilibrium producer. The hypothesis is a bound on
EVERY conditional hazard, not on unconditional atom sizes.

I independently checked the three complete unilateral replacements.
Moving ONLY one's private Never atom to a late deadline preserves all
finite atoms and gives limiting gain equal to the joint all-Never mass.
The error is supported on opponents' finite clocks surviving that late
deadline and tends to zero by bounded rewards. Matching the original
law before a fixed date and quitting there has gain exactly
J_t(Q_it-v_ti), so (S4) uses actual joint reach, not a conditional regret
assumption.

Most importantly, finite selective suppression is legal. Replace q_i(t)
by zero at just the dates where C_it>Q_it, keeping the other dates and
the original suffix after the window. Bellman telescoping against the
ORIGINAL prescribed value function gives exact gain

    sum_window J'_t q_i(t)(C_it-Q_it)_+.

Here the deviating reach J'_t is at least J_t. Since
v_ti-Q_it=(1-q_i(t))(C_it-Q_it), this gives the claimed (S5), indeed
with the stronger q_i/(1-q_i) coefficient before weakening. It is not
an invalid sum of independently available datewise improvements.

The first hazard-time crossing of one occurs at a finite original date
because the joint Never mass is at most eta<exp(-1). Each cell has
h_t<=5delta, and all used endpoints have J_t>=1/4. The exact singleton
coefficient error is at most 4delta*h_it; collision probability is at
most (3/2)delta*h_t. These give the stated 6Mdelta*h_t stopping-reward
error. Rewriting the exact recursion yields (S6) with
3M*h_t^2+12Mdelta*h_t<=27Mdelta*h_t; linear interpolation gives (S7)
with room in the constant 50. There is no limit-profile or compactness
step hidden in this finite-window interpolation.

For EVERY conditional tail, the collision/absorption ratio is at most
2delta, including imperfectly absorbing tails. At the used endpoints
the conditional Never mass is at most 4eta. Singleton reward sums are
exactly five, so both bounds in (S8) follow. Integrating (S5) after
h_it<=q_i/(1-delta) gives at most 5eta per player; extending the last
partial cell only enlarges a nonnegative bound. This verifies the
20eta+48Mdelta ledger in (S9), with the required reached weights.

For A=I-4P and R=I+4P, AR=-15I and A1=-3*1. The pair-sum/difference
calculation gives -3L^2/2<=x^T A x<=L^2 for nonnegative mass L, and
the translation is exactly

    W=x^T A x+6tau*sum x-12tau^2.

The displayed tau, sigma and kappa bounds imply (S10). Differentiation
therefore gives the stated drift identity and an error at most
525Mdelta, below the used 600Mdelta. Integration yields
W(1)-W(0)<=-3.5168, contradicting its lower bound -2.7. All constants
and signs in this final contradiction check exactly.

The nearby inspected declarations
`Math.PairedFacePotential.translated_face_drift_ge_one` in
`MathUE/Analysis/Examples/PairedFacePotential.lean`, and
`pairedFacePotential_boundedCompletion_face_drift` and
`pairedFacePotential_boundedCompletion_not_fullRoot` in
`UniformEquilibrium/Quitting/Examples/PairedFacePotentialBoundedCompletion.lean`,
concern the singleton-face potential and its distinction from full-root
inequalities. They do not themselves state the actual all-calendar
full-regret transfer verified here. No exhaustive novelty claim follows.

The exact surviving conclusion is that every low-regret sequence for
these singleton rows and a fixed bounded completion must retain some
conditional hazard above 1/(10000M). It does not exclude macroscopic
bursts, selective Never laws or changing calendars, and therefore does
not imply UE nonexistence for any of the covered tables.

## Section 27: whole nonnegative private-bonus selector

Status: bounded independent ordinary-mathematics PASS for Section 27 at
whole-file SHA256
`31357df74f3cf7ff76790d5a9e48dbe39533b89b050aab7b87c8d68b2169db3d`.
Only this section was reviewed in this check. No Lean checking, export
gate, or reward-table nonexistence conclusion is asserted.

The checked claim is literal: for the fifteen specified canonical Fin4
rows, EVERY finite common menu with N at least one and EVERY private
planned-Never bonus vector in [0,1/100]^4 has every exact auxiliary Nash
component idle before its last date, with dummy3 playing literal Never
and original full pivot gain greater than 1/3. This includes zero bonuses
and all four coordinates. The same original game has the actual uniform
equilibrium payoff (1,0,3,1). Thus the result refutes the entire proposed
exact auxiliary selector on its stated domain, not the unrestricted
joint approximate-profile question.

I reconstructed the actual core table by subtracting (0,1,1) from the
OLD table at every nonempty core absorption, and checked the dummy-only
and dummy-joining rows separately. In particular the shift is NOT a
constant on arbitrary improper profiles. For fixed opponents, its exact
own-law identity is U_old=U_actual+c_i-c_i z_i Z_i; replacing the bonus by
b_old=b+c_i Z_i makes the two auxiliary objectives differ by the constant
c_i for EVERY complete own replacement. This verifies (P4), including
the opponents' Never factor and the sign.

The conditional private ledger (P3) also checks directly: suffix
replacement changes original payoff with joint reach but private payment
with own reach. Therefore beta_i=b_i/opponent-survival, and
beta_i(t)=alpha_i(t) beta_i(t+1) when all current hazards are below one.
This is why the ordinary root continuation can be the NEXT AUGMENTED
value despite bonuses being paid after opponents stop. No small bound
on these conditional bonuses is used. The inspected declaration
`timingLawTail_isNash_of_isNash_of_positiveContinue` in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingRecursion.lean`
states the unmodified tail result under positive continuation; it does
not itself formalize this private-payment calculation.

For (P1), direct old-row enumeration gives exactly the displayed
Quit-minus-Continue expression. The three-active odds sum is strictly
negative when w is coordinatewise at least one; the two-active exclusion
and the unique-one-coordinate backward propagation follow. I separately
checked the first-sure-date argument instead of improperly applying this
ordinary-root lemma at zero continuation. At the first sure date m,
predecessor Continue is strict even after its nonnegative private bonus,
successor hazard one would permit the owner's profitable Never, and the
shifted augmented vector has the required unique coordinate one. Earlier
roots have positive continuation, so only the eventual owner can act.
If the successor mixes at m, all later finite actions have shifted payoff
minus one, whereas the used action has shifted payoff two. Its positive
remaining mass must use Never, forcing beta=3 and b=3 Pr(T_owner>=m).
The USED date-m action then has shifted original-root payoff minus one
plus b, below the guaranteed finite Quit0 floor one. This contradiction
uses no omitted date and remains valid when m=N-1. The zero-successor
case gives the same floor contradiction. Hence all three core Never
masses are strictly positive in the three-core restriction.

The pre-final threshold (P5) is exhaustive. Latest pre-final activity
leaves one final augmented coordinate one, forcing its predecessor
inactive at the final date; backward propagation makes that predecessor
literal Never throughout. A zero final successor needs bonus at least
one to reach its Quit floor. A positive final successor forces positive
final owner activity and uses both final finite and Never actions. Their
OLD root values are respectively -1+3l_owner+2z_owner and -1+z_owner.
Indifference gives b_old=3l_owner+z_owner, and the finite Quit0 floor gives
3l_owner+2z_owner>=2, hence b_old>=1. There is no uncharged private bonus
or root-survival factor in this calculation.

All three subsequent canonical threshold contradictions check with the
literal recipient payoffs. In the label2 case, z0,z1>=1-eta bounds the
pivot augmented payoff by 13eta<1. In the label1 case, z0,z2>=1-eta and
the player2 finite Quit floor imply 1-z1<7eta; total finite absorption is
then at most 9eta and the pivot augmented payoff at most 55eta<1. Label0
is immediate. Thus every auxiliary component, not merely a selected
continuation branch, is idle until the final menu date.

I independently expanded the actual final pure endpoints:

    Q0=1+q2-q1*q2,       W0=6q1-q2+q1*q2;
    Q1=q0-q0*q2,        W1=-2q0+5q2+2q0*q2;
    Q2=q1-q0*q1,        W2=5q0-2q1+2q0*q1.

Subtracting the relevant bonus and converting to odds reproduces
(P6)--(P8) exactly. The exhaustive support exclusions force q0,q1>0.
For positive q2, (P6) forbids x1>=3/5 outright, while (P8) and (P7)
give x0<=3x1/5 and x2<=3x0/5. For q2=0 the two displayed exact formulas
follow. Thus all final hazards are at most 3/8. The omitted-date pivot
gain is exactly (1-q1)(1-q2)-q0*b0; its displayed lower bound exceeds
1/3 by 257/4800. This cap is an original complete unilateral deviation,
not an auxiliary best-response claim.

The fourth-player reduction also survives the zero-bonus boundary.
Never weak dominance alone is insufficient, but a used earliest finite
date d forces b3=0 and Pr(d<=min_core T<infinity)=0. Zero joint core
survival at d would give an earlier sure core date, already excluded
while the dummy is inactive. Positive joint core survival and independent
laws instead force every core finite atom below d. The restrictions to
F_d are EXACT auxiliary core Nash with unchanged bonuses: their finite
actions beat the dummy, and all-core-Never gives core reward zero whether
or not the dummy later quits. If d=0 the pivot's immediate Quit already
contradicts equilibrium. Otherwise the core omitted deadline d is LEGAL
in the original larger menu, a simultaneous dummy quit leaves its core
reward unchanged, and its auxiliary gain exceeds 1/3-eta. This proves
literal dummy Never for every component, rather than relying on strict
dominance that fails when b3=0.

Finally the explicit UE bypass is actual full-response mathematics.
At h=2/5 I checked all three phase vector equations exactly. Within a
phase the values lie in [1,4], the active owner's two endpoints equal
one, and an inactive player's Quit surplus is at most
q=1-h^(1/k). Bellman telescoping against ANY complete replacement sums
that surplus with the deviator's reached Quit probabilities, whose sum
is at most one. Deleted-opponent period survival h^2 removes all tail
remainders uniformly, including Never deviations. Every core opponent
is proper in this construction, so the actual canonical shift subtracts
c_i for EVERY response, not only on the prescribed path. Dummy payoff
one is maximal. This gives exact fixed target (1,0,3,1), original full
regret at most q tending to zero, and uniform finite-average transfer by
the same deleted-opponent geometric tails. No conflict with the source
selector falsifier or implication of UE nonexistence remains.
