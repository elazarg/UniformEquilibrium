# CODEX_HILBERT — punishment-normality check for the BRS class

## Status

Bounded source-connection check, ordinary mathematics. The proposed
punishment-abnormality subsumption fails because it reverses the project's
definition of a normal player. The new BRS proof remains frozen at
`notes/CODEX_HILBERT__GLOBAL_BETTER_REPLY_SECURITY_PAIR_CHAMBER.md`, SHA-256
`e6b536c166a8f0b60be86509350043f4dcf00d46981f421c6d5969f7776e6d6b`.
This note does not establish novelty against all other solved classes.

## Exact source definitions

In `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`:

    IsQuittingNormalPlayer r i    means P_i <= s_i,
    IsQuittingAbnormalPlayer r i  means s_i < P_i.

Here `quittingSoloSelfPayoff` is the own singleton reward s_i, and P_i is
`quittingPunishmentValue` from
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`: the infimum, over
independent opponent behavioral plans, of the unrestricted best-reply cap.
The latter file's `quittingPunishmentValue_le_max_solo` states

    P_i <= max(s_i,0).

Hence every player with s_i>=0 is already normal. Normality does not add a
reverse inequality P_i>=s_i and does not imply equality.

The same-table Fin4 no-UE consequence was also read directly:
`exists_quantitative_fullSupport_fullNormalCore_of_finFour_of_no_uniformPayoff`
in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalTerminalGapConstrainedStationary.lean`.
Its all-player field is exactly `IsQuittingNormalPlayer`, with the direction
above. The corresponding field `all_punishmentNormal` of
`FinFourQuantitativeFullSupportHardResidual` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
has the same meaning; it is not a punishment-equality assertion.

## The valid finite-menu consequence

For each N choose an exact mixed Nash profile p^N of the finite timing
game on F_N={0,...,N-1,Never}. Write m_i(N) for the corresponding finite
punishment value. Exact finite Nash and the definition of the minimum give

    U_i(p^N) = B_i^N(p^N) >= m_i(N).

The equality concerns the displayed finite cap, not the unrestricted cap.
The all-finite-player punishment convergence proved in
`exports/FINITE_MENU_PUNISHMENT_COMPLETION_AND_EARLY_ABSORPTION_CHARACTERIZATION.md`
gives m_i(N)->P_i. Choose one convergent subsequence of the bounded vectors
U(p^N); its limit v belongs to K_r, the closure of the ACTUAL independent
payoff image, and satisfies

    v_i >= P_i for every i.                                  (1)

This deduction is valid for arbitrary reward signs and does not claim that
p^N has small unrestricted regret. No product-law compactness or tightness
is needed: it uses only compactness of the finite-dimensional payoff cube.

If every P_i=s_i, (1) obstructs the BRS exclusion K_r intersect
(s+R_+^I)=empty. Therefore under nonnegative singleton rewards the BRS
exclusion implies that some player has P_i<s_i. This is **strict normality
slack**, not abnormality. The implication does not conflict with the checked
no-UE normality theorem.

## Explicit pair class

For the radius-1/100 ball in the frozen BRS note, consider i in {0,1} and
have opponents 2,3 Quit surely at date zero while the remaining opponent
uses Never. Every complete reply either Quits at zero, producing {i,2,3},
or Continues, producing {2,3}. Both of player i's base rewards are zero,
so in the perturbed table the full cap of this punishment plan is at most
1/100. The same construction using opponents 0,1 works for i in {2,3}.
Thus every player in the ball satisfies

    P_i <= 1/100 < 99/100 <= s_i.

This verifies the proposed numerical bound but reverses its classification:
all players are normal, with strict slack. No hidden late deviation is
available against opponents who absorb surely at date zero.

## Verdict

The punishment-vector compactness lemma (1) is sound. The attempted
subsumption into the already solved abnormal-player branch is not: it uses
the opposite of the actual definition. Root retracted that subsumption
after reading the same definition. The BRS characterization and pair class
remain mathematical candidates for the requested independent review; their
novelty relative to other sufficient classes remains a separate question.
