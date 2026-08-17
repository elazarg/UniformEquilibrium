import UniformEquilibrium.Certificates.Adaptive.WeightedSecurityWelfareAssembly
import UniformEquilibrium.Certificates.Adaptive.PhaseLiftedWelfareCap
import UniformEquilibrium.Quitting.Classification.PlayerReindexNaturality
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Equivariant security--welfare assembly for quitting games

A transitive group of player relabelings transports one one-sided security
certificate to every player when it preserves the terminal reward table and
target payoff.  A positive weighted welfare cap then assembles a
uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open QuittingSureSetOwnerRepair

variable {Player Gamma : Type}
  [Fintype Player] [DecidableEq Player]
  [Group Gamma] [MulAction Gamma Player]
  [MulAction.IsPretransitive Gamma Player]

omit [DecidableEq Player] in
/-- A uniform weighted welfare cap bounds the weighted terminal payoff of
every quitting-game behavior profile. -/
theorem weighted_terminalPayoff_le_of_hasUniformWeightedWelfareCap
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (weight : Player → ℝ) (target : Payoff Player)
    (profile : (quittingGame reward).BehaviorProfile)
    (welfareCap : HasUniformWeightedWelfareCap
      (quittingGame reward) none weight target) :
    (∑ player, weight player * quittingTerminalPayoff reward profile player) ≤
      ∑ player, weight player * target player := by
  let terminalWelfare :=
    ∑ player, weight player * quittingTerminalPayoff reward profile player
  let targetWelfare := ∑ player, weight player * target player
  have hlimit : Tendsto
      (fun horizon ↦ ∑ player, weight player *
        (quittingGame reward).finiteAveragePayoff none horizon profile player)
      atTop (nhds terminalWelfare) := by
    dsimp only [terminalWelfare]
    apply tendsto_finsetSum Finset.univ
    intro player _
    exact tendsto_const_nhds.mul
      (tendsto_finiteAveragePayoff_quittingGame reward profile player)
  by_contra hnot
  have hgap : 0 < terminalWelfare - targetWelfare :=
    sub_pos.mpr (lt_of_not_ge hnot)
  let error := (terminalWelfare - targetWelfare) / 2
  have herror : 0 < error := div_pos hgap (by norm_num)
  obtain ⟨horizon, hcap⟩ := welfareCap error herror
  have heventually : ∀ᶠ T in atTop,
      (∑ player, weight player *
        (quittingGame reward).finiteAveragePayoff none T profile player) ≤
        targetWelfare + error := by
    filter_upwards [eventually_ge_atTop horizon] with T hT
    simpa only [targetWelfare] using hcap profile T hT
  have hlimitCap : terminalWelfare ≤ targetWelfare + error :=
    le_of_tendsto hlimit heventually
  dsimp only [error] at hlimitCap
  linarith

/-- A single pure quitting coalition whose weighted terminal welfare exceeds
the weighted target rules out a policy-universal welfare cap. -/
theorem not_hasUniformWeightedWelfareCap_of_terminal_welfare_gt
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (weight : Player → ℝ) (target : Payoff Player)
    (terminal : {S : Finset Player // S.Nonempty})
    (hexcess :
      (∑ player, weight player * reward terminal player) >
        ∑ player, weight player * target player) :
    ¬ HasUniformWeightedWelfareCap
      (quittingGame reward) none weight target := by
  intro welfareCap
  have hbound := weighted_terminalPayoff_le_of_hasUniformWeightedWelfareCap
    weight target
      (quittingStationaryProfile reward (quittingPureSetRoot terminal.1))
      welfareCap
  simp_rw [quittingTerminalPayoff_pureSetRoot,
    quittingSetReward_of_nonempty reward terminal.2] at hbound
  exact (not_lt_of_ge hbound) hexcess

/-- A one-sided uniform security level cannot exceed the quitting punishment
value.  The certificate's finite-horizon floor passes to terminal payoff,
then lies below the best reply to each opponent plan. -/
theorem oneSidedGuaranteeValue_le_quittingPunishmentValue
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (who : Player) (value : ℝ)
    (hsecurity : (quittingGame reward).IsOneSidedGuaranteeCertificate
      none who value) :
    value ≤ quittingPunishmentValue reward who := by
  unfold quittingPunishmentValue
  apply le_ciInf
  intro opponentPlan
  by_contra hnot
  have hbestLt : quittingBestReplyValue reward opponentPlan who < value :=
    lt_of_not_ge hnot
  let error :=
    (value - quittingBestReplyValue reward opponentPlan who) / 2
  have herror : 0 < error := div_pos (sub_pos.mpr hbestLt) (by norm_num)
  obtain ⟨securityStrategy, horizon, _horizonTwo, hfloor⟩ :=
    hsecurity error herror
  let profile := Function.update opponentPlan who securityStrategy
  have hlimit := tendsto_finiteAveragePayoff_quittingGame reward profile who
  have heventually : ∀ᶠ T in atTop,
      value - error ≤
        (quittingGame reward).finiteAveragePayoff none T profile who := by
    filter_upwards [eventually_ge_atTop horizon] with T hT
    exact hfloor opponentPlan T hT
  have hterminal : value - error ≤
      quittingTerminalPayoff reward profile who :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlimit heventually
  have hbest := le_quittingBestReplyValue reward opponentPlan who securityStrategy
  dsimp only [profile] at hterminal
  dsimp only [error] at hterminal
  linarith

/-- For a transitive invariant target, one representative security
certificate bounds every target coordinate by the representative's
punishment value.  A terminal row above the resulting total bound therefore
refutes the unit-weight welfare cap. -/
theorem not_hasUniformWeightedWelfareCap_one_of_invariantTarget_of_rowExcess
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (target : Payoff Player)
    (target_invariant : ∀ (g : Gamma) (player : Player),
      target (g • player) = target player)
    (representative : Player)
    (representativeSecurity :
      (quittingGame reward).IsOneSidedGuaranteeCertificate none representative
        (target representative))
    (terminal : {S : Finset Player // S.Nonempty})
    (hexcess :
      (Fintype.card Player : ℝ) *
          quittingPunishmentValue reward representative <
        ∑ player, reward terminal player) :
    ¬ HasUniformWeightedWelfareCap
      (quittingGame reward) none (fun _ ↦ 1) target := by
  have hsecurity :=
    oneSidedGuaranteeValue_le_quittingPunishmentValue
      representative (target representative) representativeSecurity
  have hrepresentative : target representative ≤
      quittingPunishmentValue reward representative := hsecurity
  have htarget : ∀ player, target player ≤
      quittingPunishmentValue reward representative := by
    intro player
    obtain ⟨g, moved⟩ :=
      MulAction.IsPretransitive.exists_smul_eq (M := Gamma)
        representative player
    rw [← moved, target_invariant]
    exact hrepresentative
  have htargetSum : (∑ player, target player) ≤
      (Fintype.card Player : ℝ) *
        quittingPunishmentValue reward representative := by
    calc
      (∑ player, target player) ≤
          ∑ _player : Player,
            quittingPunishmentValue reward representative :=
        Finset.sum_le_sum fun player _ ↦ htarget player
      _ = (Fintype.card Player : ℝ) *
          quittingPunishmentValue reward representative := by
        simp [nsmul_eq_mul]
  apply not_hasUniformWeightedWelfareCap_of_terminal_welfare_gt
    (fun _ ↦ 1) target terminal
  simpa only [one_mul] using htargetSum.trans_lt hexcess

/-- One representative security certificate suffices for a transitive
quitting-table symmetry.  The hypotheses explicitly require invariance of the
reward table and target; an abstract player action alone is not enough. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_transitive_rewardSymmetry
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (weight : Player → ℝ) (target : Payoff Player)
    (weight_pos : ∀ player, 0 < weight player)
    (reward_invariant : ∀ g : Gamma,
      quittingRewardReindex (MulAction.toPerm g) reward = reward)
    (target_invariant : ∀ (g : Gamma) (player : Player),
      target (g • player) = target player)
    (representative : Player)
    (representativeSecurity :
      (quittingGame reward).IsOneSidedGuaranteeCertificate none representative
        (target representative))
    (welfareCap : HasUniformWeightedWelfareCap
      (quittingGame reward) none weight target) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply isUniformEquilibriumPayoff_of_transitiveSecurity_of_welfareCap
    (G := quittingGame reward) (Gamma := Gamma) (s₀ := none)
    (weight := weight) (v := target) weight_pos representative
  · intro g
    have htransport := isOneSidedGuaranteeCertificate_reindex
      (MulAction.toPerm g) reward representative (target representative)
        representativeSecurity
    rw [reward_invariant g] at htransport
    rw [target_invariant g representative]
    exact htransport
  · exact welfareCap

/-- A phase-dependent Bellman welfare bias supplies the welfare-cap input of
the equivariant quitting-game assembly theorem. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_transitive_rewardSymmetry_of_phaseBias
    {P : ℕ} [NeZero P]
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (weight : Player → ℝ) (target : Payoff Player)
    (weight_pos : ∀ player, 0 < weight player)
    (reward_invariant : ∀ g : Gamma,
      quittingRewardReindex (MulAction.toPerm g) reward = reward)
    (target_invariant : ∀ (g : Gamma) (player : Player),
      target (g • player) = target player)
    (representative : Player)
    (representativeSecurity :
      (quittingGame reward).IsOneSidedGuaranteeCertificate none representative
        (target representative))
    (phaseBias : HasPhaseWeightedWelfareBias (P := P)
      (quittingGame reward) weight target) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply quittingGame_isUniformEquilibriumPayoff_of_transitive_rewardSymmetry
    weight target weight_pos reward_invariant target_invariant representative
      representativeSecurity
  exact hasUniformWeightedWelfareCap_of_hasPhaseWeightedWelfareBias
    (P := P) (quittingGame reward) none weight target phaseBias

/-- Phase-equivariant representative security transports to every player at
every phase.  The source phase is shifted backwards before the player is
relabelled. -/
theorem quittingGame_oneSidedGuaranteeCertificate_of_transitive_phaseTargetSymmetry
    {P : ℕ} [NeZero P]
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (phaseShift : Gamma → ZMod P)
    (target : ZMod P → Payoff Player)
    (reward_invariant : ∀ g : Gamma,
      quittingRewardReindex (MulAction.toPerm g) reward = reward)
    (target_equivariant : ∀ (g : Gamma) (phase : ZMod P) (player : Player),
      target (phase + phaseShift g) (g • player) = target phase player)
    (representative : Player)
    (representativeSecurity : ∀ phase : ZMod P,
      (quittingGame reward).IsOneSidedGuaranteeCertificate none representative
        (target phase representative))
    (phase : ZMod P) (player : Player) :
    (quittingGame reward).IsOneSidedGuaranteeCertificate none player
      (target phase player) := by
  obtain ⟨g, moved⟩ :=
    MulAction.IsPretransitive.exists_smul_eq (M := Gamma)
      representative player
  rw [← moved]
  let sourcePhase : ZMod P := phase - phaseShift g
  have htransport := isOneSidedGuaranteeCertificate_reindex
    (MulAction.toPerm g) reward representative
      (target sourcePhase representative) (representativeSecurity sourcePhase)
  rw [reward_invariant g] at htransport
  have htarget := target_equivariant g sourcePhase representative
  have hphase : sourcePhase + phaseShift g = phase := by
    simp [sourcePhase]
  rw [hphase] at htarget
  rw [htarget]
  exact htransport

/-- Every coordinate of every equivariant target phase is bounded by that
player's punishment value. -/
theorem phaseTarget_le_quittingPunishmentValue_of_transitive_symmetry
    {P : ℕ} [NeZero P]
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (phaseShift : Gamma → ZMod P)
    (target : ZMod P → Payoff Player)
    (reward_invariant : ∀ g : Gamma,
      quittingRewardReindex (MulAction.toPerm g) reward = reward)
    (target_equivariant : ∀ (g : Gamma) (phase : ZMod P) (player : Player),
      target (phase + phaseShift g) (g • player) = target phase player)
    (representative : Player)
    (representativeSecurity : ∀ phase : ZMod P,
      (quittingGame reward).IsOneSidedGuaranteeCertificate none representative
        (target phase representative))
    (phase : ZMod P) (player : Player) :
    target phase player ≤ quittingPunishmentValue reward player :=
  oneSidedGuaranteeValue_le_quittingPunishmentValue player
    (target phase player)
    (quittingGame_oneSidedGuaranteeCertificate_of_transitive_phaseTargetSymmetry
      phaseShift target reward_invariant target_equivariant representative
        representativeSecurity phase player)

/-- Phase-rotated targets permit a nonconstant target at phase zero.  Security
for one player at every representative phase transports to phase-zero
security for every player, while a phase-lifted welfare bias supplies the
common all-profile welfare cap.  No homomorphism law on `phaseShift` is needed
for this conclusion. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_transitive_phaseTargetSymmetry
    {P : ℕ} [NeZero P]
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (phaseShift : Gamma → ZMod P)
    (weight : Player → ℝ) (target : ZMod P → Payoff Player)
    (weight_pos : ∀ player, 0 < weight player)
    (reward_invariant : ∀ g : Gamma,
      quittingRewardReindex (MulAction.toPerm g) reward = reward)
    (target_equivariant : ∀ (g : Gamma) (phase : ZMod P) (player : Player),
      target (phase + phaseShift g) (g • player) = target phase player)
    (representative : Player)
    (representativeSecurity : ∀ phase : ZMod P,
      (quittingGame reward).IsOneSidedGuaranteeCertificate none representative
        (target phase representative))
    (phaseBias : HasPhaseWeightedWelfareBias (P := P)
      (quittingGame reward) weight (target 0)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (target 0) := by
  letI : Nonempty Player := ⟨representative⟩
  have security : ∀ player,
      (quittingGame reward).IsOneSidedGuaranteeCertificate none player
        (target 0 player) := fun player ↦
    quittingGame_oneSidedGuaranteeCertificate_of_transitive_phaseTargetSymmetry
      phaseShift target reward_invariant target_equivariant representative
        representativeSecurity 0 player
  have welfareCap := hasUniformWeightedWelfareCap_of_hasPhaseWeightedWelfareBias
    (P := P) (quittingGame reward) none weight (target 0) phaseBias
  exact isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_positiveWeightedWelfareCap
    (quittingGame reward) none weight (target 0) weight_pos security welfareCap

end GameTheory
