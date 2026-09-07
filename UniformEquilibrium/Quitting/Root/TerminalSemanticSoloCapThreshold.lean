import MathUE.Probability.AnalyticRegenerationCalendar
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium
import UniformEquilibrium.Quitting.Root.FiniteWordSemanticSplice
import UniformEquilibrium.Quitting.Root.TerminalSemanticDebt

/-! # First cap-threshold crossings of literal finite solo words -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The logarithmic horizon used for the finite solo threshold block. -/
def quittingSoloCapThresholdHorizon (M θ ell : ℝ) : ℕ :=
  Nat.ceil (θ⁻¹ * Real.log (4 * M / ell))

omit [Fintype ι] [DecidableEq ι] in
theorem two_mul_pow_quittingSoloCapThresholdHorizon_le_half
    {M θ ell : ℝ} (hM : 0 < M) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hell : 0 < ell) :
    2 * M * (1 - θ) ^ quittingSoloCapThresholdHorizon M θ ell ≤ ell / 2 := by
  let horizon := quittingSoloCapThresholdHorizon M θ ell
  have hratio : 0 < 4 * M / ell := div_pos (by positivity) hell
  have hceil : θ⁻¹ * Real.log (4 * M / ell) ≤ (horizon : ℝ) := by
    exact Nat.le_ceil _
  have hcharge : Real.log (4 * M / ell) ≤ (horizon : ℝ) * θ := by
    have hscaled := mul_le_mul_of_nonneg_right hceil hθ0.le
    calc
      Real.log (4 * M / ell) =
          θ⁻¹ * Real.log (4 * M / ell) * θ := by
        field_simp
      _ ≤ (horizon : ℝ) * θ := hscaled
  have hexp : Real.exp (-((horizon : ℝ) * θ)) ≤ ell / (4 * M) := by
    calc
      Real.exp (-((horizon : ℝ) * θ)) ≤
          Real.exp (-Real.log (4 * M / ell)) := by
        rw [Real.exp_le_exp]
        linarith
      _ = ell / (4 * M) := by
        rw [Real.exp_neg, Real.exp_log hratio]
        field_simp
  have hgeometric := one_sub_pow_le_exp_neg_nat_mul θ horizon hθ1.le
  have htwoM : 0 ≤ 2 * M := by positivity
  calc
    2 * M * (1 - θ) ^ quittingSoloCapThresholdHorizon M θ ell =
        2 * M * (1 - θ) ^ horizon := by rfl
    _ ≤ 2 * M * Real.exp (-((horizon : ℝ) * θ)) :=
      mul_le_mul_of_nonneg_left hgeometric htwoM
    _ ≤ 2 * M * (ell / (4 * M)) :=
      mul_le_mul_of_nonneg_left hexp htwoM
    _ = ell / 2 := by field_simp; ring

/-- Repeated semantic prefixing by the solo row of `owner`. -/
def quittingSoloSemanticIterate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (coin : PMF Bool)
    (source : QuittingTerminalSemanticPair ι) (steps : ℕ) :
    QuittingTerminalSemanticPair ι :=
  (quittingTerminalSemanticPrefix reward
    (quittingSoloStationaryRoot owner coin))^[steps] source

@[simp] theorem quittingSoloSemanticIterate_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (coin : PMF Bool)
    (source : QuittingTerminalSemanticPair ι) :
    quittingSoloSemanticIterate reward owner coin source 0 = source := by
  simp [quittingSoloSemanticIterate]

theorem quittingSoloSemanticIterate_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (coin : PMF Bool)
    (source : QuittingTerminalSemanticPair ι) (steps : ℕ) :
    quittingSoloSemanticIterate reward owner coin source (steps + 1) =
      quittingTerminalSemanticPrefix reward
        (quittingSoloStationaryRoot owner coin)
        (quittingSoloSemanticIterate reward owner coin source steps) := by
  simp [quittingSoloSemanticIterate, Function.iterate_succ_apply']

/-- The semantic iterate is realized by the literal finite word containing
exactly `steps` copies of the solo product row. -/
theorem quittingTerminalSemanticPair_replicate_solo_word
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (coin : PMF Bool)
    (source : (quittingGame reward).BehaviorProfile) (steps : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward
          (List.replicate steps (quittingSoloStationaryRoot owner coin)) source) =
      quittingSoloSemanticIterate reward owner coin
        (quittingTerminalSemanticPair reward source) steps := by
  rw [quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix,
    quittingFiniteRootWordSemanticPrefix_eq_foldr]
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [List.replicate_succ, List.foldr_cons,
        quittingSoloSemanticIterate_succ, ih]

/-- While every cap remains more than `4 M θ` above its singleton, the solo
row selects Continue in every envelope coordinate and has a literal affine
semantic update. -/
theorem quittingTerminalSemanticPrefix_solo_eq_of_above_threshold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (owner : ι) {M θ : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticBox ι M)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (habove : ∀ player,
      4 * M * θ < source.2 player -
        reward (quittingSingletonTerminal player) player) :
    let coin := quittingHazardCoin θ hθ0.le hθ1.le
    quittingTerminalSemanticPrefix reward
        (quittingSoloStationaryRoot owner coin) source =
      (fun player =>
        θ * reward (quittingSingletonTerminal owner) player +
          (1 - θ) * source.1 player,
       fun player =>
        if player = owner then source.2 owner
        else
          θ * reward (quittingSingletonTerminal owner) player +
            (1 - θ) * source.2 player) := by
  dsimp only
  let coin := quittingHazardCoin θ hθ0.le hθ1.le
  let root := quittingSoloStationaryRoot owner coin
  have hcoinTrue : (coin true).toReal = θ := by
    simp [coin]
  have hcoinFalse : (coin false).toReal = 1 - θ := by
    simp [coin]
  apply Prod.ext
  · funext player
    change quittingRootSuccessorPayoff reward source.1 root player = _
    dsimp only [root]
    rw [quittingRootSuccessorPayoff_solo]
    simp only [hcoinTrue, hcoinFalse]
    rfl
  · funext player
    change max
      (quittingRootQuitPayoff reward source.1 root player)
      (quittingRootContinuePayoff reward
        (Function.update source.1 player (source.2 player)) root player) = _
    by_cases hplayer : player = owner
    · subst player
      dsimp only [root]
      rw [quittingRootQuitPayoff_soloStationaryRoot_owner,
        quittingRootContinuePayoff_soloStationaryRoot_owner]
      simp only [Function.update_self]
      apply max_eq_right
      rw [quittingSoloReward_self]
      exact sub_nonneg.mp (le_of_lt
        (lt_of_le_of_lt (by positivity : 0 ≤ 4 * M * θ) (habove owner)))
    · dsimp only [root]
      rw [quittingRootQuitPayoff_soloStationaryRoot_other reward hplayer,
        quittingRootContinuePayoff_soloStationaryRoot_other reward hplayer]
      simp only [hcoinTrue, hcoinFalse, Function.update_self, if_neg hplayer]
      apply max_eq_right
      have hsingleton := hreward (quittingSingletonTerminal player) player
      have hcollision := hreward
        ⟨{owner, player}, by simp⟩ player
      have hpassive := hreward (quittingSingletonTerminal owner) player
      have hboxCap : source.2 player ≤ M := hsource.2.2 player
      have hsingletonLower : -M ≤
          reward (quittingSingletonTerminal player) player :=
        neg_le_of_abs_le hsingleton
      have hcollisionUpper :
          quittingSingletonCollisionReward reward owner player ≤ M := by
        unfold quittingSingletonCollisionReward
        exact le_of_abs_le hcollision
      have hpassiveLower : -M ≤
          reward (quittingSingletonTerminal owner) player :=
        neg_le_of_abs_le hpassive
      change
        (1 - θ) * reward (quittingSingletonTerminal player) player +
            θ * quittingSingletonCollisionReward reward owner player ≤
          θ * reward (quittingSingletonTerminal owner) player +
            (1 - θ) * source.2 player
      have hquitUpper :
          (1 - θ) * reward (quittingSingletonTerminal player) player +
              θ * quittingSingletonCollisionReward reward owner player ≤
            reward (quittingSingletonTerminal player) player + 2 * M * θ := by
        have hgap : quittingSingletonCollisionReward reward owner player -
            reward (quittingSingletonTerminal player) player ≤ 2 * M := by
          linarith
        have hscaled := mul_le_mul_of_nonneg_left hgap hθ0.le
        nlinarith
      have hcontinueLower :
          source.2 player - 2 * M * θ ≤
            θ * reward (quittingSingletonTerminal owner) player +
              (1 - θ) * source.2 player := by
        have hgap : source.2 player -
            reward (quittingSingletonTerminal owner) player ≤ 2 * M := by
          linarith
        have hscaled := mul_le_mul_of_nonneg_left hgap hθ0.le
        nlinarith
      exact hquitUpper.trans (le_of_lt (by
        calc
          reward (quittingSingletonTerminal player) player + 2 * M * θ <
              source.2 player - 2 * M * θ := by
            linarith [habove player]
          _ ≤ _ := hcontinueLower))

/-- Every spectator's complete-response cap strictly selects Continue while
its source cap is above the threshold. -/
theorem quittingRootQuitPayoff_lt_capContinue_solo_of_above_threshold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    {owner player : ι} (hne : player ≠ owner)
    {M θ : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticBox ι M)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (habove : 4 * M * θ < source.2 player -
      reward (quittingSingletonTerminal player) player) :
    quittingRootQuitPayoff reward source.1
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin θ hθ0.le hθ1.le)) player <
      quittingRootContinuePayoff reward
        (Function.update source.1 player (source.2 player))
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin θ hθ0.le hθ1.le)) player := by
  rw [quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
    quittingRootContinuePayoff_soloStationaryRoot_other reward hne]
  simp only [quittingHazardCoin_true_toReal,
    quittingHazardCoin_false_toReal, Function.update_self]
  have hsingleton := hreward (quittingSingletonTerminal player) player
  have hcollision := hreward ⟨{owner, player}, by simp⟩ player
  have hpassive := hreward (quittingSingletonTerminal owner) player
  have hcapUpper : source.2 player ≤ M := hsource.2.2 player
  have hsingletonLower : -M ≤
      reward (quittingSingletonTerminal player) player :=
    neg_le_of_abs_le hsingleton
  have hcollisionUpper :
      quittingSingletonCollisionReward reward owner player ≤ M := by
    unfold quittingSingletonCollisionReward
    exact le_of_abs_le hcollision
  have hpassiveLower : -M ≤
      reward (quittingSingletonTerminal owner) player :=
    neg_le_of_abs_le hpassive
  change
    (1 - θ) * reward (quittingSingletonTerminal player) player +
        θ * quittingSingletonCollisionReward reward owner player <
      θ * reward (quittingSingletonTerminal owner) player +
        (1 - θ) * source.2 player
  have hquitUpper :
      (1 - θ) * reward (quittingSingletonTerminal player) player +
          θ * quittingSingletonCollisionReward reward owner player ≤
        reward (quittingSingletonTerminal player) player + 2 * M * θ := by
    have hgap : quittingSingletonCollisionReward reward owner player -
        reward (quittingSingletonTerminal player) player ≤ 2 * M := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hgap hθ0.le]
  have hcontinueLower :
      source.2 player - 2 * M * θ ≤
        θ * reward (quittingSingletonTerminal owner) player +
          (1 - θ) * source.2 player := by
    have hgap : source.2 player -
        reward (quittingSingletonTerminal owner) player ≤ 2 * M := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hgap hθ0.le]
  exact hquitUpper.trans_lt <| lt_of_lt_of_le (by linarith) hcontinueLower

theorem quittingSoloSemanticIterate_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (coin : PMF Bool)
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) :
    ∀ steps, quittingSoloSemanticIterate reward owner coin source steps ∈
      quittingTerminalSemanticCarrier reward := by
  intro steps
  induction steps with
  | zero => simpa
  | succ steps ih =>
      rw [show steps + 1 = Nat.succ steps by omega,
        quittingSoloSemanticIterate_succ]
      exact quittingTerminalSemanticPrefix_mem_carrier reward _ _ ih

/-- Before the first threshold crossing, every coordinate of the repeated
solo block has the explicit affine form. The assertion stops exactly at the
requested number of steps; it does not continue across a threshold hit. -/
theorem quittingSoloSemanticIterate_eq_affine_of_before_threshold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (owner : ι) {M θ : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (steps : ℕ)
    (hbefore : ∀ k, k < steps → ∀ player,
      4 * M * θ <
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source k).2 player -
          reward (quittingSingletonTerminal player) player) :
    quittingSoloSemanticIterate reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source steps =
      (fun player =>
        reward (quittingSingletonTerminal owner) player +
          (1 - θ) ^ steps *
            (source.1 player -
              reward (quittingSingletonTerminal owner) player),
       fun player =>
        if player = owner then source.2 owner
        else
          reward (quittingSingletonTerminal owner) player +
            (1 - θ) ^ steps *
              (source.2 player -
                reward (quittingSingletonTerminal owner) player)) := by
  induction steps with
  | zero =>
      rw [quittingSoloSemanticIterate_zero]
      apply Prod.ext
      · funext player
        simp
      · funext player
        by_cases hplayer : player = owner <;> simp [hplayer]
  | succ steps ih =>
      have hbeforeSteps : ∀ k, k < steps → ∀ player,
          4 * M * θ <
            (quittingSoloSemanticIterate reward owner
              (quittingHazardCoin θ hθ0.le hθ1.le) source k).2 player -
              reward (quittingSingletonTerminal player) player := by
        intro k hk
        exact hbefore k (Nat.lt_succ_of_lt hk)
      have hstate := ih hbeforeSteps
      have hcurrentAbove := hbefore steps (Nat.lt_succ_self steps)
      rw [quittingSoloSemanticIterate_succ]
      rw [quittingTerminalSemanticPrefix_solo_eq_of_above_threshold
        reward _ owner hM hreward
        (quittingTerminalSemanticCarrier_mem_box reward _ hreward
          (quittingSoloSemanticIterate_mem_carrier
            reward owner _ source hsource steps))
        hθ0 hθ1 hcurrentAbove]
      rw [hstate]
      apply Prod.ext <;> funext player
      · dsimp only
        rw [pow_succ]
        ring
      · dsimp only
        by_cases hplayer : player = owner
        · simp [hplayer]
        · simp only [hplayer, if_false]
          rw [pow_succ]
          ring

/-- The complete-deviation debt of the solo block is the convex combination
of the source debt and the owner's source singleton margin. -/
theorem quittingSoloSemanticIterate_debtSum_eq_of_before_threshold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (owner : ι) {M θ : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (steps : ℕ)
    (hbefore : ∀ k, k < steps → ∀ player,
      4 * M * θ <
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source k).2 player -
          reward (quittingSingletonTerminal player) player) :
    quittingTerminalSemanticDebtSum
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source steps) =
      (1 - θ) ^ steps * quittingTerminalSemanticDebtSum source +
        (1 - (1 - θ) ^ steps) *
          (source.2 owner -
            reward (quittingSingletonTerminal owner) owner) := by
  rw [quittingSoloSemanticIterate_eq_affine_of_before_threshold
    reward source owner hM hreward hsource hθ0 hθ1 steps hbefore]
  unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebt
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ owner)]
  have hsourceSplit := Finset.sum_erase_add
    (s := Finset.univ)
    (f := fun player => source.2 player - source.1 player)
    (Finset.mem_univ owner)
  dsimp only
  have hother : ∀ player ∈ Finset.univ.erase owner,
      (if player = owner then source.2 owner
        else reward (quittingSingletonTerminal owner) player +
          (1 - θ) ^ steps *
            (source.2 player -
              reward (quittingSingletonTerminal owner) player)) -
        (reward (quittingSingletonTerminal owner) player +
          (1 - θ) ^ steps *
            (source.1 player -
              reward (quittingSingletonTerminal owner) player)) =
      (1 - θ) ^ steps * (source.2 player - source.1 player) := by
    intro player hplayer
    rw [if_neg (Finset.ne_of_mem_erase hplayer)]
    ring
  rw [Finset.sum_congr rfl hother, ← Finset.mul_sum]
  rw [← hsourceSplit]
  simp only [if_true]
  ring

theorem quittingSoloSemanticIterate_debtSum_le_max_of_before_threshold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (owner : ι) {M θ : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (steps : ℕ)
    (hbefore : ∀ k, k < steps → ∀ player,
      4 * M * θ <
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source k).2 player -
          reward (quittingSingletonTerminal player) player) :
    quittingTerminalSemanticDebtSum
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source steps) ≤
      max (quittingTerminalSemanticDebtSum source)
        (source.2 owner -
          reward (quittingSingletonTerminal owner) owner) := by
  rw [quittingSoloSemanticIterate_debtSum_eq_of_before_threshold
    reward source owner hM hreward hsource hθ0 hθ1 steps hbefore]
  have hweight0 : 0 ≤ (1 - θ) ^ steps :=
    pow_nonneg (by linarith : 0 ≤ 1 - θ) steps
  have hweight1 : (1 - θ) ^ steps ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  calc
    (1 - θ) ^ steps * quittingTerminalSemanticDebtSum source +
        (1 - (1 - θ) ^ steps) *
          (source.2 owner - reward (quittingSingletonTerminal owner) owner) ≤
      (1 - θ) ^ steps *
          max (quittingTerminalSemanticDebtSum source)
            (source.2 owner - reward (quittingSingletonTerminal owner) owner) +
        (1 - (1 - θ) ^ steps) *
          max (quittingTerminalSemanticDebtSum source)
            (source.2 owner - reward (quittingSingletonTerminal owner) owner) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hweight0)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))
    _ = _ := by ring

/-- One Continue-selected solo step cannot overshoot the threshold by more
than `2 M θ`; therefore its first crossing lands in the stated open-closed
cap interval. -/
theorem two_mul_bound_mul_lt_singletonMargin_semanticPrefix_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    {owner player : ι} (hne : player ≠ owner)
    {M θ : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticBox ι M)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (habove : ∀ who,
      4 * M * θ < source.2 who -
        reward (quittingSingletonTerminal who) who) :
    2 * M * θ <
      (quittingTerminalSemanticPrefix reward
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin θ hθ0.le hθ1.le)) source).2 player -
        reward (quittingSingletonTerminal player) player := by
  rw [quittingTerminalSemanticPrefix_solo_eq_of_above_threshold
    reward source owner hM hreward hsource hθ0 hθ1 habove]
  simp only [hne, if_false]
  have hpassive := hreward (quittingSingletonTerminal owner) player
  have hcap := hsource.2.2 player
  have hpassiveLower : -M ≤
      reward (quittingSingletonTerminal owner) player :=
    neg_le_of_abs_le hpassive
  have hgap : source.2 player -
      reward (quittingSingletonTerminal owner) player ≤ 2 * M := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hgap hθ0.le
  nlinarith [habove player]

/-- A geometric horizon producing sufficient contraction gives a literal
first threshold hit no later than that horizon. All affine and debt formulas
are asserted only through this first hit. -/
theorem exists_first_solo_capThreshold_hit_of_power_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    {owner blocker : ι} (hne : blocker ≠ owner)
    {M θ : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hinitial : ∀ player,
      4 * M * θ < source.2 player -
        reward (quittingSingletonTerminal player) player)
    (hell : 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker)
    (horizon : ℕ)
    (hpower : 2 * M * (1 - θ) ^ horizon ≤
      (reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker) / 2) :
    ∃ (steps : ℕ) (crossing : ι),
      0 < steps ∧ steps ≤ horizon ∧
      crossing ≠ owner ∧
      (∀ k, k < steps → ∀ player,
        4 * M * θ <
          (quittingSoloSemanticIterate reward owner
            (quittingHazardCoin θ hθ0.le hθ1.le) source k).2 player -
            reward (quittingSingletonTerminal player) player) ∧
      (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source steps).2 crossing -
            reward (quittingSingletonTerminal crossing) crossing ∈
        Set.Ioc (2 * M * θ) (4 * M * θ) ∧
      quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source steps =
        (fun player =>
          reward (quittingSingletonTerminal owner) player +
            (1 - θ) ^ steps *
              (source.1 player -
                reward (quittingSingletonTerminal owner) player),
         fun player =>
          if player = owner then source.2 owner
          else
            reward (quittingSingletonTerminal owner) player +
              (1 - θ) ^ steps *
                (source.2 player -
                  reward (quittingSingletonTerminal owner) player)) ∧
      quittingTerminalSemanticDebtSum
          (quittingSoloSemanticIterate reward owner
            (quittingHazardCoin θ hθ0.le hθ1.le) source steps) =
        (1 - θ) ^ steps * quittingTerminalSemanticDebtSum source +
          (1 - (1 - θ) ^ steps) *
            (source.2 owner -
              reward (quittingSingletonTerminal owner) owner) ∧
      quittingTerminalSemanticDebtSum
          (quittingSoloSemanticIterate reward owner
            (quittingHazardCoin θ hθ0.le hθ1.le) source steps) ≤
        max (quittingTerminalSemanticDebtSum source)
          (source.2 owner -
            reward (quittingSingletonTerminal owner) owner) := by
  let coin := quittingHazardCoin θ hθ0.le hθ1.le
  let state := quittingSoloSemanticIterate reward owner coin source
  let threshold := 4 * M * θ
  let hit : ℕ → Prop := fun steps => ∃ player,
    (state steps).2 player -
      reward (quittingSingletonTerminal player) player ≤ threshold
  have hexistsBound : ∃ steps, steps ≤ horizon ∧ hit steps := by
    by_contra hnone
    push Not at hnone
    have haboveThrough : ∀ steps, steps ≤ horizon → ∀ player,
        threshold < (state steps).2 player -
          reward (quittingSingletonTerminal player) player := by
      intro steps hsteps player
      exact lt_of_not_ge fun hle => hnone steps hsteps ⟨player, hle⟩
    have hbefore : ∀ k, k < horizon → ∀ player,
        4 * M * θ <
          (quittingSoloSemanticIterate reward owner coin source k).2 player -
            reward (quittingSingletonTerminal player) player := by
      intro k hk
      exact haboveThrough k hk.le
    have haffine := quittingSoloSemanticIterate_eq_affine_of_before_threshold
      reward source owner hM.le hreward hsource hθ0 hθ1 horizon hbefore
    have hcap := congrArg
      (fun pair : QuittingTerminalSemanticPair ι => pair.2 blocker) haffine
    simp only [hne, if_false] at hcap
    have hsourceBox :=
      quittingTerminalSemanticCarrier_mem_box reward source hreward hsource
    have hcapUpper : source.2 blocker ≤ M := hsourceBox.2.2 blocker
    have hpassive := hreward (quittingSingletonTerminal owner) blocker
    have hpassiveLower : -M ≤
        reward (quittingSingletonTerminal owner) blocker :=
      neg_le_of_abs_le hpassive
    have hbaseGap : source.2 blocker -
        reward (quittingSingletonTerminal owner) blocker ≤ 2 * M := by
      linarith
    have hweight : 0 ≤ (1 - θ) ^ horizon :=
      pow_nonneg (by linarith : 0 ≤ 1 - θ) horizon
    have hscaled := mul_le_mul_of_nonneg_left hbaseGap hweight
    have hfinal : (state horizon).2 blocker -
        reward (quittingSingletonTerminal blocker) blocker < 0 := by
      dsimp only [state, coin]
      rw [hcap]
      nlinarith
    have hthresholdPositive : 0 < threshold := by
      dsimp only [threshold]
      positivity
    linarith [haboveThrough horizon le_rfl blocker,
      hthresholdPositive, hfinal]
  obtain ⟨witnessSteps, hwitnessLe, hwitnessHit⟩ := hexistsBound
  have hexists : ∃ steps, hit steps := ⟨witnessSteps, hwitnessHit⟩
  let steps := Nat.find hexists
  obtain ⟨crossing, hcrossing⟩ := Nat.find_spec hexists
  have hstepsLe : steps ≤ horizon :=
    (Nat.find_min' hexists hwitnessHit).trans hwitnessLe
  have hbefore : ∀ k, k < steps → ∀ player,
      4 * M * θ <
        (quittingSoloSemanticIterate reward owner coin source k).2 player -
          reward (quittingSingletonTerminal player) player := by
    intro k hk player
    have hnothit := Nat.find_min hexists hk
    exact lt_of_not_ge fun hle => hnothit ⟨player, hle⟩
  have hstepsPos : 0 < steps := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hcrossingZero := hcrossing
    change (state steps).2 crossing -
      reward (quittingSingletonTerminal crossing) crossing ≤ threshold at hcrossingZero
    rw [hzero] at hcrossingZero
    simp [state, coin, threshold] at hcrossingZero
    linarith [hinitial crossing]
  have hcrossingNe : crossing ≠ owner := by
    intro heq
    subst crossing
    have haffine := quittingSoloSemanticIterate_eq_affine_of_before_threshold
      reward source owner hM.le hreward hsource hθ0 hθ1 steps hbefore
    have hownerCap := congrArg
      (fun pair : QuittingTerminalSemanticPair ι => pair.2 owner) haffine
    simp only [if_true] at hownerCap
    have hcrossingOwner := hcrossing
    change (state steps).2 owner -
      reward (quittingSingletonTerminal owner) owner ≤ threshold at hcrossingOwner
    dsimp only [state, coin] at hcrossingOwner
    rw [hownerCap] at hcrossingOwner
    dsimp only [threshold] at hcrossingOwner
    exact (not_lt_of_ge hcrossingOwner) (hinitial owner)
  have hlower : 2 * M * θ < (state steps).2 crossing -
      reward (quittingSingletonTerminal crossing) crossing := by
    obtain ⟨prior, hsteps⟩ := Nat.exists_eq_succ_of_ne_zero hstepsPos.ne'
    rw [hsteps]
    rw [show Nat.succ prior = prior + 1 by omega]
    dsimp only [state]
    rw [quittingSoloSemanticIterate_succ]
    apply two_mul_bound_mul_lt_singletonMargin_semanticPrefix_solo
      reward _ (owner := owner) (player := crossing) hcrossingNe hM.le hreward
      (quittingTerminalSemanticCarrier_mem_box reward _ hreward
        (quittingSoloSemanticIterate_mem_carrier
          reward owner coin source hsource prior))
      hθ0 hθ1
    intro player
    exact hbefore prior (by omega) player
  refine ⟨steps, crossing, hstepsPos, hstepsLe, hcrossingNe, hbefore,
    ⟨hlower, ?_⟩, ?_, ?_, ?_⟩
  · simpa only [coin, state, threshold] using hcrossing
  · exact quittingSoloSemanticIterate_eq_affine_of_before_threshold
      reward source owner hM.le hreward hsource hθ0 hθ1 steps hbefore
  · exact quittingSoloSemanticIterate_debtSum_eq_of_before_threshold
      reward source owner hM.le hreward hsource hθ0 hθ1 steps hbefore
  · exact quittingSoloSemanticIterate_debtSum_le_max_of_before_threshold
      reward source owner hM.le hreward hsource hθ0 hθ1 steps hbefore

/-- A strictly preempted owner has a produced finite solo block whose first
threshold hit occurs within the explicit logarithmic horizon. -/
theorem exists_first_solo_capThreshold_hit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    {owner blocker : ι} (hne : blocker ≠ owner)
    {M θ : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hinitial : ∀ player,
      4 * M * θ < source.2 player -
        reward (quittingSingletonTerminal player) player)
    (hpreempted : 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker) :
    let ell := reward (quittingSingletonTerminal blocker) blocker -
      reward (quittingSingletonTerminal owner) blocker
    ∃ (steps : ℕ) (crossing : ι),
      0 < steps ∧
      steps ≤ quittingSoloCapThresholdHorizon M θ ell ∧
      crossing ≠ owner ∧
      (∀ k, k < steps → ∀ player,
        4 * M * θ <
          (quittingSoloSemanticIterate reward owner
            (quittingHazardCoin θ hθ0.le hθ1.le) source k).2 player -
            reward (quittingSingletonTerminal player) player) ∧
      (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source steps).2 crossing -
            reward (quittingSingletonTerminal crossing) crossing ∈
        Set.Ioc (2 * M * θ) (4 * M * θ) ∧
      quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source steps =
        (fun player =>
          reward (quittingSingletonTerminal owner) player +
            (1 - θ) ^ steps *
              (source.1 player -
                reward (quittingSingletonTerminal owner) player),
         fun player =>
          if player = owner then source.2 owner
          else
            reward (quittingSingletonTerminal owner) player +
              (1 - θ) ^ steps *
                (source.2 player -
                  reward (quittingSingletonTerminal owner) player)) ∧
      quittingTerminalSemanticDebtSum
          (quittingSoloSemanticIterate reward owner
            (quittingHazardCoin θ hθ0.le hθ1.le) source steps) =
        (1 - θ) ^ steps * quittingTerminalSemanticDebtSum source +
          (1 - (1 - θ) ^ steps) *
            (source.2 owner -
              reward (quittingSingletonTerminal owner) owner) ∧
      quittingTerminalSemanticDebtSum
          (quittingSoloSemanticIterate reward owner
            (quittingHazardCoin θ hθ0.le hθ1.le) source steps) ≤
        max (quittingTerminalSemanticDebtSum source)
          (source.2 owner -
            reward (quittingSingletonTerminal owner) owner) := by
  dsimp only
  apply exists_first_solo_capThreshold_hit_of_power_bound
    reward source hne hM hreward hsource hθ0 hθ1 hinitial hpreempted
  exact two_mul_pow_quittingSoloCapThresholdHorizon_le_half
    hM hθ0 hθ1 hpreempted

end GameTheory
