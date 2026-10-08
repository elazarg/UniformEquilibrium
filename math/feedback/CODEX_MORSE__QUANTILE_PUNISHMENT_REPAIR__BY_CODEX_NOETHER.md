# Quantile-cut punishment repair — independent proof and overlap review

## Exact reviewed scope and verdict

Author section: `## Quantile-cut punishment repair consumes varying-period owner concentration`
through immediately before `## Actual cap-domain control does not automatically select a charged path`
in `notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`.
Frozen section SHA256:
`ef61c75ca97bf5f47670573c21a9e5dae9054d2289967bdd5805544d8a3a4065`.

Independent mathematical reconstruction: **PASS** for QCUT1–QCUT7, including
the literal cutoff, signed-own seam, full finite/Never caps, fixed target,
same-table varying-period application, and whole-family hazard limit.
No Lean execution or new checked theorem is claimed here.

Independent strategic-value verdict: **notes only, implemented-consumer
overlap**. The actual varying-period concentration branch already supplies
every hypothesis of the tracked deleted-Quit-limits compiler. Moreover,
the arbitrary actual singleton-law sequence in QCUT4 itself admits a
direct earliest-own-atom extraction into the tracked approximate-solo-cap
compiler. That extraction is proved below; it does not need a fixed period,
positive lower bound on an owner's rate, a tail equilibrium, or an exact
limiting root. Therefore the claimed new counterexample/source-branch
narrowing is not established as new. The quantile construction remains a
valid alternative repair preserving the original finite prefix, but that
is not presently an additional conjecture-facing deficit consumed.

I did not consult another review verdict. The author's later narrow
overlap suggestion named the two existing compiler declarations; I
independently read them and reconstructed their actual source adapters.

## 1. Reconstructed cutoff proof and all response cases

For a fixed owner h, let η=1−Pr(terminal={h}) and let |r_i(S)|≤M.
Choose η<ε<1 and the least integer T with Pr(N_h>T)≤ε, treating Never
as larger than every integer. Such T exists because Pr(N_h=Never)≤η.
Minimality gives Pr(N_h≥T)>ε, including T=0. The full date-T atom
belongs to the retained prefix; no clock atom is split.

Write o=Pr(min_{j≠h}N_j≤T). Independence and the literal coalition
event give

    η ≥ Pr(N_h≥T)·o > εo,
    o ≤ η/ε.

The event implication retains ties: if an opponent stops by T and h
has not stopped strictly before T, the terminal coalition cannot be
{h}. An earlier opponent can stop alone, or an opponent can tie h.

Graft an actual independent near-punishment after T, with the owner's
complete tail cap ≤s_h+ζ. Every prescribed payoff changes only on
original joint survival through T. Its probability is at most
Pr(N_h>T)≤ε, giving |U_i′−U_i|≤2Mε.

For an outsider j, a pure deadline t≤T selects the coalition before
the new tail and has exactly its old payoff. For every t>T, including
arbitrarily late moving deadlines, and for Never, its change is bounded
by 2M times deleted-j survival through T. Since prescribed h remains
among those opponents, that probability is at most ε. Hence

    B_j′≤B_j+2Mε,
    d_j′≤d_j+4Mε.

For h, every deadline t≤T pays s_h on the event that no opponent has
stopped by T; the exceptional probability is o. Its payoff is therefore
≤s_h+2Mo. Every later deadline and Never has exact decomposition
R_h(T)+(1−o)V_tail, with |R_h(T)|≤Mo and V_tail≤s_h+ζ. Thus

    R_h(T)+(1−o)V_tail−s_h
      ≤Mo−o s_h+(1−o)ζ
      ≤2Mo+ζ.

This calculation explicitly uses |s_h|≤M, not s_h≥0. It is valid for
negative owns and includes the actual Never tail response. Consequently
B_h′≤s_h+2Mo+ζ. The terminal-law hypothesis gives
|U_h−s_h|≤2Mη, so d_h′≤2M(η+ε+o)+ζ. Summing yields precisely

    D′≤∑[j≠h]d_j+2Mη+2Mη/ε+(4n−2)Mε+ζ.

For η>0, ε=√η gives the displayed QCUT.7. For η=0, arbitrary positive
ε→0 suffices, with o=0. Pure-time extremality passes these uniform
bounds to every behavioral deviation. There is no attaining response
assumption, private common randomization, or ordinal-time execution.

QCUT4 then delivers terminal approximate Nash profiles whose entire
prescribed payoff vector tends to the fixed r({h}). The target is fixed
before accuracy, and the tracked fixed-target terminal endpoint provides
the eventual uniform finite-horizon contract. It is stronger than merely
target-free compact payoff selection and does not require absorption of
the repaired profiles.

## 2. Direct implemented consumption of the varying-period branch

The source theorem
`exists_interiorCyclicFixedDebtor_and_ownerEscape_of_terminalGap`
in `UniformEquilibrium/Quitting/Cycles/InteriorCyclicTerminalDebtRatio.lean`
uses the literal period m+1, so set m_k=L_k−1 when QCUT uses L_k≥1.
It assumes nonnegative errors and L_k e_k→0, and returns one fixed
debtor plus the literal concentration-or-vanishing-hazard alternative.
The concentration record in
`UniformEquilibrium/Quitting/Cycles/InteriorCyclicDebtEscape.lean`
really stores terminal **outcome-law** convergence, not only a reward
moment, as well as outsider complete-debt convergence.

At each selected initial phase take the actual root x_k and its CURRENT
Bellman value v_k. The following inputs are already available on that
same selected family:

- x_{k,h}>0 by interiority; no rate lower bound is necessary.
- The initial root's opponent absorption is at most h's one-turn
  opponent absorption, which tends to zero.
- v_k→r({h}) by the concentration record and exact Bellman/terminal
  identification.
- For every outsider j, pure Quit is a permitted local deviation, so
  Q_j(x_k)≤v_{k,j}+e_k. This follows directly from `rootNash` and
  `bellman`, without dividing by a vanishing Continue probability.
- e_k→0 follows from 0≤e_k≤L_k e_k.
- Same-table no UE implies full normal core and P_h≤s_h.

These are exactly the hypotheses of
`isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits`
in `UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean`.
Use the initial-root opponent absorption for `hazardError`, the maximum
coordinate distance |v_k−r({h})| for `targetError`, and e_k for
`quitError`. All are nonnegative and vanish. That theorem constructs
approximate complete solo caps and calls the existing punishment
compiler. Its statement contains no fixed period or common phase-space
compactness premise. Therefore the varying-period owner-concentration
arm already contradicts no UE by an implemented consumer.

QCUT.8 is nonetheless mathematically correct: if the displayed TOTAL
hazard failed to vanish, select a subsequence with H_k≥a>0 and apply
the same fixed-gap alternative there. Concentration is impossible by
the existing compiler; the vanishing-hazard output contradicts the
uniform lower bound. This proves the limit for **every** supplied
low-period-error family, not just one favorable selector. It leaves
fully diffuse families unresolved and does not assert efficient-ratio
families exist.

## 3. Stronger overlap: earliest own atom consumes QCUT4 directly

This adapter applies to the whole arbitrary-profile statement of QCUT4,
not just cyclic local-Nash source data.

Fix one actual independent profile p with η<1. Its h-clock has positive
finite mass. Let T be the LEAST integer with α=Pr(N_h=T)>0. Then h has
no finite mass before T and α∈(0,1]. No survival normalization of α is
needed. Every event min_{j≠h}N_j≤T forces the original terminal
coalition to differ from {h}, because h is surely not earlier than T.
Hence

    Pr(min_{j≠h}N_j≤T)≤η.

Create the solo stationary root with h's Quit probability α and every
other owner Continue. For an outsider j, its pure-Quit endpoint is

    Q_j^solo=(1−α)s_j+α r_j({h,j}).

Compare this endpoint with j's ORIGINAL complete pure deadline T.
Couple the same h-clock draw and remove all other-than-h,j opponents.
On the event none of those opponents stops by T, the two terminal
rewards agree: h stops exactly at T or stays later, yielding respectively
{h,j} or {j}. The exceptional probability is ≤η, and its reward
difference has absolute value ≤2M. Thus

    Q_j^solo≤V_j(p,T)+2Mη
             ≤B_j(p)+2Mη
             ≤r_j({h})+d_j(p)+4Mη.

The last inequality uses |U_j(p)−r_j({h})|≤2Mη. It is sign-correct
for arbitrary signed rewards. When there are no other-than-h,j owners,
the coupling error is exactly zero; the uniform displayed bound remains
valid.

The tracked identity `quittingStationaryUnilateralCap_solo_other`
in `UniformEquilibrium/Quitting/Boundary/Exceptional/TailFallback.lean`
says, for ANY α>0,

    B_j^solo=max(Q_j^solo,r_j({h})).

It includes every finite deadline and Never. Therefore its full cap is
≤r_j({h})+d_j(p)+4Mη. Set

    E_k=max[j≠h]d_j(p_k)+4Mη_k

(empty outsider maximum0). Under QCUT4, E_k→0. The extracted owner
rates α_k may vanish arbitrarily fast or equal1, and the earliest
dates T_k may escape to infinity. Neither matters: the existing theorem
`isUniformEquilibriumPayoff_soloReward_of_approximate_caps`
in `UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean`
accepts any positive owner hazards, vanishing outsider full-cap errors,
and P_h≤s_h. It yields exactly r({h}) as a uniform payoff.

This is an alternative legal construction, not a claim that the original
profiles or tails were Nash. It regenerates solo profiles rather than
retaining the old prefix. It also shows why an empty initial date in a
general concentration sequence is not a missing consumer input: choose
the earliest positive OWN atom, not necessarily calendar date0.

The numerical cap error here is linear in η rather than √η, but no
constant improvement is being offered as new export value. Its role is
to resolve the actual-source overlap completely.

## 4. Exact boundary checks and attempted falsifiers

The C-row family test is correct. Interiority makes every deleted
opponent group absorb, so Never attains cap C+1. The welfare formulas
give D≥1 over the whole interior family. This does not contradict
punishment completion or QCUT4, since the family is not Nash and its
actual owner-concentration arm is repaired outside the interior class.

Independent exact rational recalculation at C=1 and
q=(1/2,1/10000,1/10000,1/10000) gives:

    η=599940002/1000299970001≈0.000599760092;
    D_periodic≈1.000899790087>1;
    D_100-prefix+AllNever≈0.030455712303<1/10.

The finite-prefix cap calculation took the maximum over deadlines0…99,
the first late solo deadline100, and Never. Every later finite deadline
has the same first-late value because the tail is AllNever. The exact
prefix caps are approximately (1.029555922216,2,2,2), and prescribed
payoffs are approximately (1,1.999700069971,1.999700069971,1.999700069971).
Only the displayed decimals are approximations; the comparison tests
were done with rational arithmetic, without a root solver.

The two-player negative-own countertest also checks: h's Never reply
always pays≥0, while all-Continue opponents attain cap0, so P_h=0>−1.
No near-Nash delivery approaching−1 is possible. Therefore normality
cannot be dropped or inferred solely from singleton concentration.

Attempted edge failures (T=0, cutoff atom larger than ε, η=0, vanished
initial owner rate, moving late tests, negative s_h, and punishment
infimum not attained) produce no objection to the cutoff proof. The
earliest-atom adapter additionally handles an arbitrarily long empty
initial calendar and arbitrarily small first owner atom.

## 5. Inspected declarations and exact remaining deficit

The declarations above were read in place under their imports. Additional
specific dependency checks:

- `nonempty_interiorApproximateNashCyclicBlock` and
  `InteriorApproximateNashCyclicBlock.quitProbability_odds_eq_exp`,
  `UniformEquilibrium/Quitting/Cycles/EndogenousInteriorCyclicBlock.lean`;
- `InteriorApproximateNashCyclicBlock.value_eq_cyclicTerminalValue` and
  `InteriorApproximateNashCyclicBlock.terminalDeviationDebt_le`,
  `UniformEquilibrium/Quitting/Cycles/InteriorApproximateNashCyclicProfile.lean`;
- `InteriorApproximateNashCyclicBlock.outsiderTerminalDeviationDebt_le`,
  `UniformEquilibrium/Quitting/Cycles/InteriorCyclicAbsorptionAlternatives.lean`;
- `tendsto_quittingTerminalOutcomeMass_cyclicBehaviorProfile_singleton_of_absorption`,
  `UniformEquilibrium/Quitting/Cycles/OwnerSingletonCyclicConcentration.lean`;
- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`,
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`;
- `all_punishmentNormal_of_normalCore_eq_univ`,
  `UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`;
- `quittingPunishmentValue` and
  `quittingPunishmentValue_eq_stationaryPunishmentValue`,
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`;
- `exists_quittingStationaryPunishmentRoot_lt_add`,
  `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`;
- `quittingRootSequenceHazardTerminalValue_le_sSup_pureTime`,
  `UniformEquilibrium/Quitting/Cycles/InfinitePureTimeExtremality.lean`;
- `quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_of_plan_add`,
  `UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean`;
- `false_of_periodOne_ownerConcentration_of_finFour_noUniformPayoff`,
  `UniformEquilibrium/Quitting/Cycles/PeriodOneOwnerConcentrationContradiction.lean`;
- `quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix`,
  `UniformEquilibrium/Quitting/Stationary/SingletonStationaryRoot.lean`;
- `IsεQuittingRootNash`,
  `UniformEquilibrium/Quitting/Root/FirstBranch.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`;
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`,
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

The isolated-coordinate premises of
`UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean` and the more
general deleted-Quit compiler were compared explicitly. The latter, not
only the period-one specialized contradiction, closes the actual branch.
This is a bounded declaration comparison, not a global Lean audit.

No mathematical objection remains in the reviewed ordinary proof. The
unresolved full-goal question is exactly the fully diffuse cyclic family
or some different all-errors producer: the reviewed argument neither
forces an efficient deleted-error ratio nor a nonvanishing compatible
charged return. No absorbing minimum, full minimum, or NP least-Never
source is identified with these cyclic profiles.
