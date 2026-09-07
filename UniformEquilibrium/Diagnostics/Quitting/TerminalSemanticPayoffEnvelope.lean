import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPreemptedOwnerQuadraticMargin

/-! # Payoff-envelope consequences of quadratic semantic minimum margins -/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An ownerwise upper payoff-margin witness on every actual profile passes
to every point of the closed semantic carrier. Finite-label subsequence
selection avoids introducing a separate minimum-coordinate functional. -/
theorem exists_owner_payoffMargin_le_of_mem_terminalSemanticCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    {ρ : ℝ}
    (hactual : ∀ profile : (quittingGame reward).BehaviorProfile, ∃ owner,
      quittingTerminalPayoff reward profile owner -
        reward (quittingSingletonTerminal owner) owner ≤ ρ) :
    ∃ owner, pair.1 owner -
      reward (quittingSingletonTerminal owner) owner ≤ ρ := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  choose owner howner using fun n => hactual (profiles n)
  obtain ⟨fixed, select, hselect, hfixed⟩ :=
    Math.exists_fixed_label_on_strictMono_subsequence owner
  refine ⟨fixed, ?_⟩
  have hselected : Tendsto (fun n =>
      quittingTerminalSemanticPair reward (profiles (select n))) atTop (nhds pair) :=
    hprofiles.comp hselect.tendsto_atTop
  have hcoordinate : Tendsto (fun n =>
      (quittingTerminalSemanticPair reward (profiles (select n))).1 fixed -
        reward (quittingSingletonTerminal fixed) fixed) atTop
      (nhds (pair.1 fixed -
        reward (quittingSingletonTerminal fixed) fixed)) :=
    ((((continuous_apply fixed).comp continuous_fst).tendsto pair).sub
      tendsto_const_nhds).comp hselected
  apply le_of_tendsto' hcoordinate
  intro n
  rw [← hfixed n]
  exact howner (select n)

/-- If every coordinate of a semantic pair has the quadratic prescribed
margin and actual profiles have payoff-margin envelope `ρ`, then its debt is
at most the square-root envelope. -/
theorem terminalSemanticDebtSum_le_sqrt_of_all_quadraticMargins
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    {M ρ : ℝ} (hM : 0 < M) (hρ : 0 ≤ ρ)
    (hquadratic : ∀ owner,
      quittingTerminalSemanticDebtSum pair ^ 2 / (8 * M) ≤
        pair.1 owner - reward (quittingSingletonTerminal owner) owner)
    (hactual : ∀ profile : (quittingGame reward).BehaviorProfile, ∃ owner,
      quittingTerminalPayoff reward profile owner -
        reward (quittingSingletonTerminal owner) owner ≤ ρ) :
    quittingTerminalSemanticDebtSum pair ≤ Real.sqrt (8 * M * ρ) := by
  obtain ⟨owner, hupper⟩ :=
    exists_owner_payoffMargin_le_of_mem_terminalSemanticCarrier
      reward pair hpair hactual
  have hdebtNonnegative : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun player _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair player
  have hproduct : 0 ≤ 8 * M * ρ := by positivity
  have hsqrt := Real.sq_sqrt hproduct
  have hscaled := (div_le_iff₀ (show 0 < 8 * M by positivity)).mp
    ((hquadratic owner).trans hupper)
  nlinarith [Real.sqrt_nonneg (8 * M * ρ)]

/-- For nonnegative singleton rewards, the attained global debt minimum obeys
the payoff-envelope square-root bound. -/
theorem exists_minimumTerminalSemanticDebt_le_sqrt_of_nonnegativeSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M ρ : ℝ} (hM : 0 < M) (hρ : 0 ≤ ρ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsingleton : ∀ owner,
      0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hactual : ∀ profile : (quittingGame reward).BehaviorProfile, ∃ owner,
      quittingTerminalPayoff reward profile owner -
        reward (quittingSingletonTerminal owner) owner ≤ ρ) :
    ∃ pair : QuittingTerminalSemanticPair ι,
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      quittingTerminalSemanticDebtSum pair ≤ Real.sqrt (8 * M * ρ) := by
  obtain ⟨pair, hpair, hminimum⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward
  refine ⟨pair, hpair, hminimum, ?_⟩
  have hdebtNonnegative : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun player _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair player
  by_cases hpositive : 0 < quittingTerminalSemanticDebtSum pair
  · apply terminalSemanticDebtSum_le_sqrt_of_all_quadraticMargins
      reward pair hpair hM hρ _ hactual
    intro owner
    obtain ⟨blocker, hpreempted⟩ :=
      exists_strict_preemptor_of_positive_minimum_nonnegative_singleton
        reward pair hminimum hpositive owner (hsingleton owner)
    exact positive_minimum_preemptedOwner_prescribedMargin
      reward pair hpair hminimum owner blocker hM hreward hpositive hpreempted
  · have hzero : quittingTerminalSemanticDebtSum pair = 0 :=
      le_antisymm (le_of_not_gt hpositive) hdebtNonnegative
    rw [hzero]
    exact Real.sqrt_nonneg _

/-- For four players, the signed-table all-owner quadratic margin gives the
same payoff-envelope bound without singleton sign assumptions. -/
theorem exists_minimumTerminalSemanticDebt_le_sqrt_of_fourPlayer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    {M ρ : ℝ} (hM : 0 < M) (hρ : 0 ≤ ρ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hactual : ∀ profile : (quittingGame reward).BehaviorProfile, ∃ owner,
      quittingTerminalPayoff reward profile owner -
        reward (quittingSingletonTerminal owner) owner ≤ ρ) :
    ∃ pair : QuittingTerminalSemanticPair ι,
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      quittingTerminalSemanticDebtSum pair ≤ Real.sqrt (8 * M * ρ) := by
  obtain ⟨pair, hpair, hminimum⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward
  refine ⟨pair, hpair, hminimum, ?_⟩
  have hdebtNonnegative : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun player _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair player
  by_cases hpositive : 0 < quittingTerminalSemanticDebtSum pair
  · have hmargins := positive_minimum_fourPlayer_allOwner_quadraticMargins
      reward pair hpair hminimum hplayers hM hreward hpositive
    apply terminalSemanticDebtSum_le_sqrt_of_all_quadraticMargins
      reward pair hpair hM hρ _ hactual
    intro owner
    have hownerDebt : quittingTerminalSemanticDebt pair owner ≤
        quittingTerminalSemanticDebtSum pair := by
      unfold quittingTerminalSemanticDebtSum
      exact Finset.single_le_sum
        (fun player _ => quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward hpair player) (Finset.mem_univ owner)
    linarith [(hmargins owner).2]
  · have hzero : quittingTerminalSemanticDebtSum pair = 0 :=
      le_antisymm (le_of_not_gt hpositive) hdebtNonnegative
    rw [hzero]
    exact Real.sqrt_nonneg _

end GameTheory
