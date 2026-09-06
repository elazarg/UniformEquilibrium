import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremium
import UniformEquilibrium.Quitting.Root.PlayerwiseUnitNormalization

/-! # Normalization and sufficient conditions for supportwise premium balance -/

noncomputable section
namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Supportwise balance survives playerwise normalization when the witness
weights are reweighted by the positive coordinate scales. -/
theorem supportwiseBalance_playerwiseUnitNormalization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {shift : ℝ} (hshift : 0 < shift)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hbalanced : IsSupportwiseBalancedQuittingPremiumTable reward) :
    IsSupportwiseBalancedQuittingPremiumTable
      (quittingPlayerwiseUnitNormalization reward shift) := by
  intro active hactive
  obtain ⟨weight, hweight, hsupport, hsum, hpremium⟩ :=
    hbalanced active hactive
  let scale : ι → ℝ := fun player =>
    reward (quittingSingletonTerminal player) player + shift
  let total : ℝ := ∑ player ∈ active, weight player * scale player
  have hscale : ∀ player, 0 < scale player := fun player =>
    add_pos_of_nonneg_of_pos (hsingleton player) hshift
  have htotal : 0 < total := by
    have hlower : shift ≤ total := by
      calc
        shift = ∑ player ∈ active, weight player * shift := by
          rw [← Finset.sum_mul, hsum, one_mul]
        _ ≤ ∑ player ∈ active, weight player * scale player := by
          apply Finset.sum_le_sum
          intro player _
          exact mul_le_mul_of_nonneg_left
            (by simp [scale, hsingleton player]) (hweight player)
        _ = total := rfl
    exact hshift.trans_le hlower
  let normalizedWeight : ι → ℝ := fun player =>
    weight player * scale player / total
  refine ⟨normalizedWeight, ?_, ?_, ?_, ?_⟩
  · intro player
    exact div_nonneg (mul_nonneg (hweight player) (hscale player).le)
      htotal.le
  · intro player hout
    simp [normalizedWeight, hsupport player hout]
  · simp only [normalizedWeight, ← Finset.sum_div, total]
    exact div_self htotal.ne'
  · intro terminal hterminal hsubset
    have hold := hpremium terminal hterminal hsubset
    have hidentity : (∑ player ∈ terminal, normalizedWeight player *
        (quittingPlayerwiseUnitNormalization reward shift
            ⟨terminal, hterminal⟩ player -
          quittingPlayerwiseUnitNormalization reward shift
            (quittingSingletonTerminal player) player)) =
        (∑ player ∈ terminal, weight player *
          (reward ⟨terminal, hterminal⟩ player -
            reward (quittingSingletonTerminal player) player)) / total := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro player _
      rw [quittingPlayerwiseUnitNormalization_singleton
        reward hshift hsingleton]
      simp only [normalizedWeight, quittingPlayerwiseUnitNormalization,
        scale]
      have hden : reward (quittingSingletonTerminal player) player + shift ≠ 0 :=
        (add_pos_of_nonneg_of_pos (hsingleton player) hshift).ne'
      field_simp [hden]
      ring
    rw [hidentity]
    exact div_nonpos_of_nonpos_of_nonneg hold htotal.le

omit [Fintype ι] in
/-- Weak support peeling supplies point-mass weights and hence supportwise
balance. -/
theorem supportwiseBalance_of_weakPremiumPeeling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hordered : ∀ (active : Finset ι), active.Nonempty →
      ∃ chosen ∈ active, ∀ (terminal : Finset ι)
        (hterminal : terminal.Nonempty),
        terminal ⊆ active → chosen ∈ terminal →
          reward ⟨terminal, hterminal⟩ chosen ≤
            reward (quittingSingletonTerminal chosen) chosen) :
    IsSupportwiseBalancedQuittingPremiumTable reward := by
  intro active hactive
  obtain ⟨chosen, hchosen, hpremium⟩ := hordered active hactive
  let weight : ι → ℝ := fun player => if player = chosen then 1 else 0
  refine ⟨weight, ?_, ?_, ?_, ?_⟩
  · intro player
    dsimp only [weight]
    positivity
  · intro player hout
    simp only [weight]
    split
    · rename_i heq
      subst player
      exact (hout hchosen).elim
    · rfl
  · simp [weight, hchosen]
  · intro terminal hterminal hsubset
    by_cases hmem : chosen ∈ terminal
    · simp [weight, hmem]
      exact hpremium terminal hterminal hsubset hmem
    · have hzero : (∑ player ∈ terminal, weight player *
          (reward ⟨terminal, hterminal⟩ player -
            reward (quittingSingletonTerminal player) player)) = 0 := by
        apply Finset.sum_eq_zero
        intro player hplayer
        have hne : player ≠ chosen := fun heq => hmem (heq ▸ hplayer)
        simp [weight, hne]
      exact hzero.le

omit [Fintype ι] in
/-- One strictly positive global participant weighting yields normalized
supportwise witnesses on every nonempty support. -/
theorem supportwiseBalance_of_globalPositiveWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (globalWeight : ι → ℝ)
    (hpositive : ∀ player, 0 < globalWeight player)
    (hpremium : ∀ (terminal : Finset ι) (hterminal : terminal.Nonempty),
      (∑ player ∈ terminal, globalWeight player *
        (reward ⟨terminal, hterminal⟩ player -
          reward (quittingSingletonTerminal player) player)) ≤ 0) :
    IsSupportwiseBalancedQuittingPremiumTable reward := by
  intro active hactive
  let total : ℝ := ∑ player ∈ active, globalWeight player
  have htotal : 0 < total := Finset.sum_pos' (fun player _ =>
    (hpositive player).le) ⟨hactive.choose, hactive.choose_spec,
      hpositive hactive.choose⟩
  let weight : ι → ℝ := fun player =>
    if player ∈ active then globalWeight player / total else 0
  refine ⟨weight, ?_, ?_, ?_, ?_⟩
  · intro player
    simp only [weight]
    split
    · exact div_nonneg (hpositive player).le htotal.le
    · exact le_rfl
  · intro player hout
    simp [weight, hout]
  · calc
      (∑ player ∈ active, weight player) =
          ∑ player ∈ active, globalWeight player / total := by
        apply Finset.sum_congr rfl
        intro player hplayer
        simp [weight, hplayer]
      _ = total / total := by rw [Finset.sum_div]
      _ = 1 := div_self htotal.ne'
  · intro terminal hterminal hsubset
    have hsum : (∑ player ∈ terminal, weight player *
        (reward ⟨terminal, hterminal⟩ player -
          reward (quittingSingletonTerminal player) player)) =
        (∑ player ∈ terminal, globalWeight player *
          (reward ⟨terminal, hterminal⟩ player -
            reward (quittingSingletonTerminal player) player)) / total := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro player hplayer
      simp [weight, hsubset hplayer]
      ring
    rw [hsum]
    exact div_nonpos_of_nonpos_of_nonneg (hpremium terminal hterminal) htotal.le

end GameTheory
