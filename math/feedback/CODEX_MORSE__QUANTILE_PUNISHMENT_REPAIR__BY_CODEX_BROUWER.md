# Independent review of quantile-cut punishment repair

Reviewer: CODEX_BROUWER.

Reviewed source: `notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`,
from `## Quantile-cut punishment repair consumes varying-period owner concentration`
to immediately before
`## Actual cap-domain control does not automatically select a charged path`.
The complete 301-line extraction has SHA256
`ef61c75ca97bf5f47670573c21a9e5dae9054d2289967bdd5805544d8a3a4065`.

Verdict: ordinary mathematical PASS for QCUT1–QCUT7. No unresolved
mathematical objection was found. Strict export-value verdict: NOTES ONLY
for the proposed produced-branch reduction. The tracked deleted-Quit solo
completion theorem already consumes every produced varying-period owner
concentration branch by the actual adapter proved below. The quantile
argument is a useful different proof for arbitrary concentrating profiles,
but no additional produced counterexample class is exhibited.

I read the complete frozen section and the named source statements under
their imports, reconstructed the cutoff and all-response bounds, and checked
the stationary numerical regression using exact fractions. No other
reviewer's verdict was used. My earlier contributions to the canonical
marked-source work are not inputs to this proof. This is a static source and
ordinary-mathematics review, not a new Lean build or a claim that QCUT is
already implemented.

## 1. Exact claim being checked

Fix one bounded signed finite quitting table r, with zero live and AllNever
rewards, finite nonempty player set I, fixed owner h, and |r_i(S)|≤M with
M>0. The prescribed strategies are independent stopping laws on
ℕ∪{Never}. A unilateral replacement is unrestricted behavioral; its full
cap B_i is the supremum over every finite pure deadline and Never.

Let η(p)=1−P_p(terminal coalition={h}), U_i the prescribed terminal
payoff, and d_i=B_i−U_i. The new ordinary theorem asserts:

    η(p_k)→0,
    d_j(p_k)→0 for every j≠h,
    true unrestricted punishment P_h≤r_h({h})

imply that the ONE FIXED vector r({h}) is a uniform-equilibrium payoff.
It does not assume approximate Nash for h, an attained punishment, a Nash
tail, periodicity, or a bounded period.

For a four-player table with no UE, normal-core production supplies the
punishment inequalities on that SAME table. The existing interior cyclic
producer and fixed-debtor alternative, with arbitrary finite periods L_k,
arbitrary initial phases, and L_k e_k→0, supply either owner concentration
with outsider full debts tending to zero or vanishing total displayed
hazard. QCUT claims to remove the former, and hence force the WHOLE
family's total hazard to tend to zero. No efficient-ratio family or full
UE theorem is asserted.

## 2. Cutoff and every cap across the seam

For 0≤η<ε<1, owner Never mass is at most η, so the least finite T with
a=P(N_h>T)≤ε exists. Minimality gives P(N_h≥T)>ε, including T=0.
The complete old date T is retained. Independence gives

    P(N_h≥T)·P(min opponents N_j≤T)≤η.

The event on the left always prevents the terminal coalition from being
{h}: an opponent is earlier or ties at T. Therefore o=P(min opponents
N_j≤T)≤η/ε. Atoms, simultaneous exits, and Never all have the claimed
closed-cut interpretation. No atom is split and no new test is inserted
inside an old date.

The stationary punishment producer chooses actual independent opponents
with full h-cap below P_h+ζ≤s_h+ζ, where s_h=r_h({h}). Set h's own
punishment-tail law to Continue; this does not change its unilateral cap.
Follow the old behavioral roots through T and graft this tail at T+1.
This is a literal actual independent profile, not a correlated draw or an
ordinal calendar.

Original joint survival past T is at most a, so every prescribed payoff
changes by at most 2Mε. For j≠h, all tests t≤T are exactly unchanged.
For EVERY test t>T and for Never, deleted-j survival past T is at most
a because h remains one of j's prescribed opponents. Thus, uniformly
over all those tests,

    B_j(p′)≤B_j(p)+2Mε,
    d_j(p′)≤d_j(p)+4Mε.

This is an upper bound before taking the supremum; it does not select
old active tests or assume a maximizer. Pure-time extremality then covers
every behavioral replacement, including moving late deadlines.

For h, any finite t≤T yields s_h whenever opponents all survive through
T. The complementary event has probability o, giving the uniform upper
bound s_h+2Mo. A later finite test or Never has value

    R_h(T)+(1−o)V_tail,
    |R_h(T)|≤Mo,   V_tail≤s_h+ζ.

Consequently its value is at most s_h+2Mo+ζ. In particular the surviving
coefficient of s_h is retained before estimation: this remains valid
when s_h<0. Together these bounds control ALL finite/Never tests, not
only the selected punishment test. Since |U_h(p)−s_h|≤2Mη,

    D(p′)≤Σ[j≠h]d_j(p)+2Mη+2Mη/ε+(4n−2)Mε+ζ.

The coefficients agree with the individual bounds. For η>0, ε=√η gives
the stated 2Mη+4nM√η remainder. For η=0, o=0 and arbitrary ε,ζ→0
avoid division by zero. Choosing one family of cuts and actual
punishments produces D(p′_k)→0 and U(p′_k)→the fixed r({h}); the
fixed-target terminal-to-uniform endpoint has exactly these quantifiers.

## 3. Independent boundary tests

Negative own reward does not break the argument. Take two players h,j,
with the complete table

    r({h})=(−1,1),
    r({j})=(−2,1),
    r({h,j})=(−2,1),
    Never=(0,0).

Originally h quits surely at date0 and j Never. Then η=0,
U=(−1,1), B=(0,1), and outsider debt is0. The true h-punishment is−2:
j surely quitting at0 gives h full cap−2, and no payoff can be below−2.
Thus P_h≤s_h is valid with both values negative. Retain date0 and graft
j's sure exit at date1, with h continuing there. Prescribed U stays
(−1,1); h's date0 response is−1 and all later finite/Never responses
are−2, so B_h=−1. All j responses have payoff1. The repaired profile
has full D=0. An AllNever tail instead leaves h's profitable Never
response and D=1. This checks the required signed punishment seam.

The source's opposite two-player table with passive/pair h-reward+1
instead has P_h=0>−1, so its premise genuinely fails. Its original
singleton concentration and zero outsider debt cannot justify debt
vanishing near h-payoff−1. No hidden nonnegative punishment hypothesis
was imported.

For the source's C=1 four-player regression, I independently enumerated
all15 nonempty coalitions using exact rational q=(1/2,1/10000³). The
old infinite stationary profile has D>1. Following100 unchanged roots
then AllNever has D<1/10, with every prefix test, the first late finite
solo test, and Never included. Singleton failure is <1/1000. Decimal
orientation only: old D≈1.0008997901, repaired D≈0.0304557123,
η≈0.0005997601. The verdict uses exact rational comparisons, not those
decimals. The all-interior welfare obstruction and the solved-table
scope are correctly distinguished from a positive-gap counterexample.

## 4. Actual existing adapter already consumes the produced branch

The significant overlap is not merely a supplied solo row. The tracked
theorem

`isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits`
in `UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean`
requires positive owner rate, vanishing opponent-root absorption,
continuations converging to r({h}), vanishing outsider Quit endpoint
error, and P_h≤s_h. Every one of these hypotheses is produced by the
existing varying-period owner-concentration source.

Here is the complete same-table ordinary adapter. On the concentration
subsequence let p_k be the actual cyclic profile and x_k its INITIAL
phase root. Define

    a_k = its h-deleted per-period absorption,
    v_k = U(p_k),
    t_k = max_i |v_k,i−r_i({h})|,
    z_k = max[j≠h] d_j(p_k).

Finiteness and the source fields give a_k,t_k,z_k≥0 and all three tend
to0. Interiority gives x_k,h>0 at the chosen initial phase, even if
that rate tends to0 and even if periods diverge. Initial opponent
absorption is at most a_k: for factors c_phase∈[0,1],
∏phase c_phase≤c_initial. Thus

    1−opponentContinue(x_k,h)≤a_k.

For every j≠h, the pure deadline0 against p_k is exactly the root Quit
value Q_j(x_k), and is one of its full behavioral responses. Therefore

    Q_j(x_k)≤B_j(p_k)=v_k,j+d_j(p_k)≤v_k,j+z_k.

The declaration's continuation sequence can be chosen as v_k. Its
target-error parameter is t_k, hazard-error parameter a_k, and
Quit-error parameter z_k. The source's value at the initial phase is
the actual v_k by the absorbing cyclic value/profile identities; it is
not a hypothetical annotation. Same-table normal-core production gives
P_h≤s_h. These are precisely all the theorem's hypotheses.

Equivalently its proof deletes every non-h root rate and bounds the
resulting solo-root outsider cap by

    r_j({h})+2Ma_k+t_k+z_k.

This follows from its named root-deletion estimate and the exact solo
cap max(Q_j^solo,r_j({h})). It then applies the already tracked
`isUniformEquilibriumPayoff_soloReward_of_approximate_caps` in
`UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean`.
That theorem needs NO positive lower bound, convergence rate, or limit
for the owner's positive rate. In particular varying phase spaces are
not an obstacle to this composition.

This directly contradicts no UE on r for EVERY produced concentration
subsequence. The whole-family H_k→0 argument then follows exactly as
in QCUT5 by applying the alternative to any subsequence H_k≥a>0.
This implication is already within the implemented mathematical
capabilities even if no single umbrella declaration currently packages
this particular composition. No strategic witness is left unproduced.

The general quantile theorem also applies to arbitrary noninterior
concentrating profiles without an initial positive owner rate. That is
a genuine difference in supplied-sequence scope. However QCUT provides
no additional arbitrary-game producer landing in that broader scope.
Its claimed produced counterexample reduction is wholly covered by the
adapter above. Under the export criteria, a different proof and a more
general supplied sequence do not by themselves establish further
counterexample-class narrowing. Recommend retaining this exact proof
in the author's notes and reusing the existing composition for the
varying-period branch.

## 5. Source audit and qualifications

Declarations inspected under their imports include:

- `exists_interiorCyclicFixedDebtor_and_ownerEscape_of_terminalGap`,
  `UniformEquilibrium/Quitting/Cycles/InteriorCyclicTerminalDebtRatio.lean`;
  `InteriorCyclicOwnerConcentrationSubsequence` and
  `InteriorCyclicOwnerEscapeAlternative`,
  `UniformEquilibrium/Quitting/Cycles/InteriorCyclicDebtEscape.lean`.
  Their fields include actual outcome LAW convergence, outsider FULL
  debt convergence, and vanishing per-period opponent absorption.
- `InteriorApproximateNashCyclicBlock` and
  `nonempty_interiorApproximateNashCyclicBlock`,
  `UniformEquilibrium/Quitting/Cycles/EndogenousInteriorCyclicBlock.lean`;
  `InteriorApproximateNashCyclicBlock.value_eq_cyclicTerminalValue` and
  `InteriorApproximateNashCyclicBlock.terminalDeviationDebt_le`,
  `UniformEquilibrium/Quitting/Cycles/InteriorApproximateNashCyclicProfile.lean`.
- `isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits`,
  `UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean`;
  `isUniformEquilibriumPayoff_soloReward_of_approximate_caps` and
  `quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_of_plan_add`,
  `UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean`.
- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`,
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`;
  `all_punishmentNormal_of_normalCore_eq_univ`,
  `UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`.
- `exists_quittingStationaryPunishmentRoot_lt_add`,
  `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`;
  `quittingBestReplyValue_stationary` and
  `quittingPunishmentValue_eq_stationaryPunishmentValue`,
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`.
- `quittingRootSequenceHazardTerminalValue_le_sSup_pureTime`,
  `UniformEquilibrium/Quitting/Cycles/InfinitePureTimeExtremality.lean`;
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
- `false_of_periodOne_ownerConcentration_of_finFour_noUniformPayoff`,
  `UniformEquilibrium/Quitting/Cycles/PeriodOneOwnerConcentrationContradiction.lean`.
  That particular source is indeed only period1; it is NOT the
  stronger overlap identified in section4 of this review.

One nonblocking source qualification: the unconditional interior-block
existence theorem assumes local error e>0, not e≥0. QCUT5's assertion
about ANY already supplied family with e_k≥0 is valid; it should not be
read as an unconditional existence statement at e_k=0. Positive errors
give the actual producer needed for its intended applications.

No SUM minimum, recipient normalization, native absorbing minimum,
tail-Nash hypothesis, punishment attainment, or fixed-period compactness
is needed or silently used. The surviving diffuse regime remains open.
