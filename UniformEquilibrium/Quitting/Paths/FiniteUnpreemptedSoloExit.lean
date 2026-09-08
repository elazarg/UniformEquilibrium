import UniformEquilibrium.Quitting.Root.TerminalSemanticSoloCapThreshold
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryTailSemanticReduction

/-! # Finite solo exit with signs only on the designated owner

The outsider estimate is made relative to the finite word's prescribed
payoff.  Thus a negative payoff from the designated owner's singleton does
not require a nonnegativity hypothesis: its geometric tail is charged by the
same reward bound.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingSoloSemanticIterate_never_payoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner player : ι) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ steps,
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin t ht0 ht1)
        (quittingNeverBoundarySemanticPair reward) steps).1 player =
      (1 - (1 - t) ^ steps) *
        reward (quittingSingletonTerminal owner) player := by
  intro steps
  induction steps with
  | zero => simp [quittingSoloSemanticIterate, quittingNeverBoundarySemanticPair]
  | succ steps ih =>
      rw [quittingSoloSemanticIterate_succ]
      change quittingRootSuccessorPayoff reward _
          (quittingSoloStationaryRoot owner (quittingHazardCoin t ht0 ht1)) player = _
      rw [quittingRootSuccessorPayoff_solo]
      simp only [quittingHazardCoin_true_toReal,
        quittingHazardCoin_false_toReal, ih, pow_succ]
      change t * reward (quittingSingletonTerminal owner) player + _ = _
      ring

theorem quittingSoloSemanticIterate_never_owner_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsingleton : 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    ∀ steps,
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin t ht0 ht1)
        (quittingNeverBoundarySemanticPair reward) steps).2 owner =
      reward (quittingSingletonTerminal owner) owner := by
  intro steps
  induction steps with
  | zero => simp [quittingSoloSemanticIterate, quittingNeverBoundarySemanticPair,
      max_eq_right hsingleton]
  | succ steps ih =>
      rw [quittingSoloSemanticIterate_succ]
      unfold quittingTerminalSemanticPrefix
      dsimp only
      rw [quittingRootQuitPayoff_soloStationaryRoot_owner,
        quittingRootContinuePayoff_soloStationaryRoot_owner,
        Function.update_self, ih, quittingSoloReward_self, max_self]

/-- The absolute outsider-cap estimate under globally nonnegative
singleton rewards.  The signed theorem below instead estimates the cap
relative to the finite word's prescribed payoff. -/
theorem quittingSoloSemanticIterate_never_other_cap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {M t : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hunpreempted : ∀ player, player ≠ owner →
      reward (quittingSingletonTerminal player) player ≤
        reward (quittingSingletonTerminal owner) player)
    {player : ι} (hne : player ≠ owner) :
    ∀ steps,
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin t ht0 ht1)
        (quittingNeverBoundarySemanticPair reward) steps).2 player ≤
      reward (quittingSingletonTerminal owner) player + 2 * M * t := by
  have hM : 0 ≤ M :=
    quittingRewardCoordinateBound_nonneg_of_player reward owner hreward
  let a := reward (quittingSingletonTerminal owner) player
  let s := reward (quittingSingletonTerminal player) player
  have hs : 0 ≤ s := hsingleton player
  have hsa : s ≤ a := hunpreempted player hne
  have ha : 0 ≤ a := hs.trans hsa
  have haUpper : a ≤ M :=
    (le_abs_self _).trans (hreward (quittingSingletonTerminal owner) player)
  have hcollision : quittingSingletonCollisionReward reward owner player ≤ M := by
    unfold quittingSingletonCollisionReward
    exact le_of_abs_le (hreward ⟨{owner, player}, by simp⟩ player)
  intro steps
  induction steps with
  | zero =>
      simp only [quittingSoloSemanticIterate_zero, quittingNeverBoundarySemanticPair]
      exact (max_le ha hsa).trans (by nlinarith [mul_nonneg hM ht0])
  | succ steps ih =>
      rw [quittingSoloSemanticIterate_succ]
      unfold quittingTerminalSemanticPrefix
      dsimp only
      rw [quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
        quittingRootContinuePayoff_soloStationaryRoot_other reward hne,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal,
        Function.update_self]
      change max ((1 - t) * s + t * quittingSingletonCollisionReward
          reward owner player)
          (t * a + (1 - t) *
            (quittingSoloSemanticIterate reward owner
              (quittingHazardCoin t ht0 ht1)
              (quittingNeverBoundarySemanticPair reward) steps).2 player) ≤
        a + 2 * M * t
      apply max_le
      · have hfirst := mul_le_mul_of_nonneg_left hsa (sub_nonneg.mpr ht1)
        have hsecond := mul_le_mul_of_nonneg_left hcollision ht0
        dsimp only [a, s] at ha hfirst hsecond ⊢
        nlinarith [mul_nonneg hM ht0]
      · have hscaled := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr ht1)
        dsimp only [a] at ha hscaled ⊢
        nlinarith [mul_nonneg hM ht0,
          mul_nonneg (sub_nonneg.mpr ht1) (mul_nonneg hM ht0)]

/-- Against an unpreempted solo owner, an outsider's finite-word cap is at
most its prescribed payoff plus the one-row surcharge and geometric tail.
No singleton sign is required for the outsider. -/
theorem quittingSoloSemanticIterate_never_other_cap_le_payoff_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {M t : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hunpreempted : ∀ player, player ≠ owner →
      reward (quittingSingletonTerminal player) player ≤
        reward (quittingSingletonTerminal owner) player)
    {player : ι} (hne : player ≠ owner) :
    ∀ steps,
      (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin t ht0 ht1)
          (quittingNeverBoundarySemanticPair reward) steps).2 player ≤
        (1 - (1 - t) ^ steps) *
            reward (quittingSingletonTerminal owner) player +
          2 * M * t + M * (1 - t) ^ steps := by
  have hM : 0 ≤ M :=
    quittingRewardCoordinateBound_nonneg_of_player reward owner hreward
  let a := reward (quittingSingletonTerminal owner) player
  let s := reward (quittingSingletonTerminal player) player
  have hsa : s ≤ a := hunpreempted player hne
  have haLower : -M ≤ a :=
    (neg_le_of_abs_le (hreward (quittingSingletonTerminal owner) player))
  have haUpper : a ≤ M :=
    le_of_abs_le (hreward (quittingSingletonTerminal owner) player)
  have hsUpper : s ≤ M := hsa.trans haUpper
  have hcollision : quittingSingletonCollisionReward reward owner player ≤ M := by
    unfold quittingSingletonCollisionReward
    exact le_of_abs_le (hreward ⟨{owner, player}, by simp⟩ player)
  intro steps
  induction steps with
  | zero =>
      simp only [quittingSoloSemanticIterate_zero,
        quittingNeverBoundarySemanticPair, pow_zero, sub_self, zero_mul]
      exact max_le (by positivity) (hsUpper.trans (by nlinarith [mul_nonneg hM ht0]))
  | succ steps ih =>
      rw [quittingSoloSemanticIterate_succ]
      unfold quittingTerminalSemanticPrefix
      dsimp only
      rw [quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
        quittingRootContinuePayoff_soloStationaryRoot_other reward hne,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal,
        Function.update_self, pow_succ]
      change max ((1 - t) * s + t * quittingSingletonCollisionReward
          reward owner player)
          (t * a + (1 - t) *
            (quittingSoloSemanticIterate reward owner
              (quittingHazardCoin t ht0 ht1)
              (quittingNeverBoundarySemanticPair reward) steps).2 player) ≤
        (1 - (1 - t) ^ steps * (1 - t)) * a +
          2 * M * t + M * ((1 - t) ^ steps * (1 - t))
      have hpow0 : 0 ≤ (1 - t) ^ steps :=
        pow_nonneg (sub_nonneg.mpr ht1) _
      apply max_le
      · have hquit : (1 - t) * s + t * quittingSingletonCollisionReward
            reward owner player ≤ (1 - t) * a + t * M := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hsa (sub_nonneg.mpr ht1))
            (mul_le_mul_of_nonneg_left hcollision ht0)
        have haPlus : 0 ≤ a + M := by linarith
        have hfirstNonnegative : 0 ≤ t * (a + M) :=
          mul_nonneg ht0 haPlus
        have hsecondNonnegative :
            0 ≤ (1 - t) ^ steps * (1 - t) * (M - a) := by positivity
        nlinarith
      · have hscaled := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr ht1)
        dsimp only [a] at hscaled ⊢
        have hextra : 0 ≤ t * (2 * M * t) := by positivity
        nlinarith

/-- A repeated solo word followed by Never has the standard coordinate debt
bound when only the designated owner's singleton is known nonnegative. -/
theorem quittingTerminalSemanticDebt_replicate_solo_never_le_of_owner_nonnegative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner player : ι) {M t : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hunpreempted : ∀ who, who ≠ owner →
      reward (quittingSingletonTerminal who) who ≤
        reward (quittingSingletonTerminal owner) who)
    (steps : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward
            (List.replicate steps (quittingSoloStationaryRoot owner
              (quittingHazardCoin t ht0 ht1)))
            (quittingAlwaysContinueProfile reward))) player ≤
      2 * M * t + M * (1 - t) ^ steps := by
  have hM : 0 ≤ M :=
    quittingRewardCoordinateBound_nonneg_of_player reward owner hreward
  rw [quittingTerminalSemanticPair_replicate_solo_word]
  have hnever : quittingTerminalSemanticPair reward
      (quittingAlwaysContinueProfile reward) =
        quittingNeverBoundarySemanticPair reward := by
    apply Prod.ext
    · funext who
      exact quittingTerminalPayoff_quittingAlwaysContinue reward who
    · funext who
      exact quittingContinuationBestResponseValue_quittingAlwaysContinueProfile
        reward who
  rw [hnever]
  unfold quittingTerminalSemanticDebt
  rw [quittingSoloSemanticIterate_never_payoff reward owner player ht0 ht1]
  have hpow : 0 ≤ (1 - t) ^ steps := pow_nonneg (sub_nonneg.mpr ht1) _
  by_cases hplayer : player = owner
  · subst player
    rw [quittingSoloSemanticIterate_never_owner_cap
      reward owner ht0 ht1 howner]
    have hselfUpper : reward (quittingSingletonTerminal owner) owner ≤ M :=
      le_of_abs_le (hreward (quittingSingletonTerminal owner) owner)
    nlinarith [mul_nonneg hM ht0,
      mul_nonneg hpow (sub_nonneg.mpr hselfUpper)]
  · have hcap :=
      quittingSoloSemanticIterate_never_other_cap_le_payoff_add
        reward owner hreward ht0 ht1 hunpreempted hplayer steps
    linarith

/-- The coordinate estimate with all singleton rewards nonnegative. -/
theorem quittingTerminalSemanticDebt_replicate_solo_never_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner player : ι) {M t : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsingleton : ∀ who,
      0 ≤ reward (quittingSingletonTerminal who) who)
    (hunpreempted : ∀ who, who ≠ owner →
      reward (quittingSingletonTerminal who) who ≤
        reward (quittingSingletonTerminal owner) who)
    (steps : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward
            (List.replicate steps (quittingSoloStationaryRoot owner
              (quittingHazardCoin t ht0 ht1)))
            (quittingAlwaysContinueProfile reward))) player ≤
      2 * M * t + M * (1 - t) ^ steps := by
  exact
    quittingTerminalSemanticDebt_replicate_solo_never_le_of_owner_nonnegative
      reward owner player hreward ht0 ht1 (hsingleton owner)
        hunpreempted steps

/-- Summing the signed coordinate estimates retains the same total-debt
bound as the globally nonnegative version. -/
theorem quittingTerminalSemanticDebtSum_replicate_solo_never_le_of_owner_nonnegative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {M t : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hunpreempted : ∀ player, player ≠ owner →
      reward (quittingSingletonTerminal player) player ≤
        reward (quittingSingletonTerminal owner) player)
    (steps : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward
            (List.replicate steps (quittingSoloStationaryRoot owner
              (quittingHazardCoin t ht0 ht1)))
            (quittingAlwaysContinueProfile reward))) ≤
      Fintype.card ι * (2 * M * t + M * (1 - t) ^ steps) := by
  unfold quittingTerminalSemanticDebtSum
  calc
    ∑ player, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward
            (List.replicate steps (quittingSoloStationaryRoot owner
              (quittingHazardCoin t ht0 ht1)))
            (quittingAlwaysContinueProfile reward))) player ≤
      ∑ _player : ι, (2 * M * t + M * (1 - t) ^ steps) :=
        Finset.sum_le_sum fun player _ =>
          quittingTerminalSemanticDebt_replicate_solo_never_le_of_owner_nonnegative
            reward owner player hreward ht0 ht1 howner hunpreempted steps
    _ = Fintype.card ι * (2 * M * t + M * (1 - t) ^ steps) := by
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]

/-- The total-debt estimate with all singleton rewards nonnegative. -/
theorem quittingTerminalSemanticDebtSum_replicate_solo_never_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {M t : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hunpreempted : ∀ player, player ≠ owner →
      reward (quittingSingletonTerminal player) player ≤
        reward (quittingSingletonTerminal owner) player)
    (steps : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward
            (List.replicate steps (quittingSoloStationaryRoot owner
              (quittingHazardCoin t ht0 ht1)))
            (quittingAlwaysContinueProfile reward))) ≤
      Fintype.card ι * (2 * M * t + M * (1 - t) ^ steps) := by
  exact
    quittingTerminalSemanticDebtSum_replicate_solo_never_le_of_owner_nonnegative
      reward owner hreward ht0 ht1 (hsingleton owner) hunpreempted steps

/-- One unpreempted owner with nonnegative own singleton reward admits an
actual finite repeated-solo word of arbitrarily small total debt.  No sign
condition is imposed on outsider singleton rewards. -/
theorem exists_finiteWord_debtSum_le_of_nonnegative_unpreemptedDesignatedOwner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {M epsilon : ℝ} (hM : 0 < M) (hepsilon : 0 < epsilon)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hunpreempted : ∀ player, player ≠ owner →
      reward (quittingSingletonTerminal player) player ≤
        reward (quittingSingletonTerminal owner) player) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) ≤ epsilon := by
  let playerCount : ℝ := Fintype.card ι
  have hplayerCount : 0 < playerCount := by
    dsimp only [playerCount]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨owner⟩ : 0 < Fintype.card ι)
  let t := min (1 / 2 : ℝ) (epsilon / (4 * playerCount * M))
  have hfraction : 0 < epsilon / (4 * playerCount * M) := by positivity
  have ht : 0 < t := by
    dsimp only [t]
    exact lt_min (by norm_num) hfraction
  have htHalf : t ≤ 1 / 2 := by
    dsimp only [t]
    exact min_le_left _ _
  have htOne : t ≤ 1 := htHalf.trans (by norm_num)
  have honeSubNonnegative : 0 ≤ 1 - t := by linarith
  have honeSubOne : 1 - t < 1 := by linarith
  have hlimit : Tendsto (fun steps : ℕ => M * (1 - t) ^ steps)
      atTop (nhds 0) := by
    simpa only [mul_comm, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        honeSubNonnegative honeSubOne).mul_const M
  have htarget : 0 < epsilon / (2 * playerCount) := by positivity
  have heventually : ∀ᶠ steps in atTop,
      M * (1 - t) ^ steps < epsilon / (2 * playerCount) :=
    (tendsto_order.1 hlimit).2 _ htarget
  obtain ⟨steps, hsteps⟩ := heventually.exists
  let roots := List.replicate steps (quittingSoloStationaryRoot owner
    (quittingHazardCoin t ht.le htOne))
  refine ⟨roots, ?_⟩
  have hraw :=
    quittingTerminalSemanticDebtSum_replicate_solo_never_le_of_owner_nonnegative
      reward owner hreward ht.le htOne howner hunpreempted steps
  have htUpper : t ≤ epsilon / (4 * playerCount * M) := by
    dsimp only [t]
    exact min_le_right _ _
  have hfirst : playerCount * (2 * M * t) ≤ epsilon / 2 := by
    have hscaled := mul_le_mul_of_nonneg_left htUpper
      (by positivity : 0 ≤ playerCount * (2 * M))
    field_simp [hplayerCount.ne', hM.ne'] at hscaled ⊢
    nlinarith
  have hsecond : playerCount * (M * (1 - t) ^ steps) ≤ epsilon / 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hsteps.le hplayerCount.le
    field_simp [hplayerCount.ne'] at hscaled ⊢
    nlinarith
  change quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward))) ≤ epsilon
  dsimp only [roots]
  calc
    _ ≤ playerCount * (2 * M * t + M * (1 - t) ^ steps) := by
      simpa only [playerCount] using hraw
    _ = playerCount * (2 * M * t) +
        playerCount * (M * (1 - t) ^ steps) := by ring
    _ ≤ epsilon := by linarith

/-- The finite exit with all singleton rewards nonnegative. -/
theorem exists_finiteWord_debtSum_le_of_nonnegative_unpreemptedOwner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hunpreempted : ∀ player, player ≠ owner →
      reward (quittingSingletonTerminal player) player ≤
        reward (quittingSingletonTerminal owner) player) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) ≤ ε := by
  exact
    exists_finiteWord_debtSum_le_of_nonnegative_unpreemptedDesignatedOwner
      reward owner hM hε hreward (hsingleton owner) hunpreempted

end GameTheory
