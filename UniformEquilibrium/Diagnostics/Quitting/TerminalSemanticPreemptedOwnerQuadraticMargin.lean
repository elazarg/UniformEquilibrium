import MathUE.Topology.FiniteLabelSubsequence
import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Root.TerminalSemanticSoloCapThreshold
import UniformEquilibrium.Quitting.Terminal.AuxiliaryNashDefectBudget
import UniformEquilibrium.Quitting.Root.BelowSingletonRootAbsorption
import UniformEquilibrium.Quitting.Root.ProductRootProbabilityBridge
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt
import UniformEquilibrium.Quitting.Classification.Existence.SoloPreemptionUniformPayoff
import UniformEquilibrium.Quitting.Classification.LCP.FourPlayerSingletonColumnBlockers
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget

/-! # Quadratic singleton margins at a positive minimum of total response debt -/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A preempted owner at a positive global debt minimum has a
quadratic cap margin and prescribed-payoff margin. The proof uses vanishing
solo hazards and a first-threshold compact limit. -/
theorem positive_minimum_preemptedOwner_quadraticMargins
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (owner blocker : ι) {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hpreempted : 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker) :
    let d := quittingTerminalSemanticDebtSum pair
    pair.2 owner - reward (quittingSingletonTerminal owner) owner ≥
        d + d ^ 2 / (8 * M) ∧
      pair.1 owner - reward (quittingSingletonTerminal owner) owner ≥
        d - quittingTerminalSemanticDebt pair owner + d ^ 2 / (8 * M) := by
  dsimp only
  let d := quittingTerminalSemanticDebtSum pair
  let L := pair.2 owner - reward (quittingSingletonTerminal owner) owner
  have hd : 0 < d := by simpa only [d] using hpositive
  have hne : blocker ≠ owner := by
    intro heq
    subst blocker
    simp at hpreempted
  have hmargin : ∀ player, d ≤
      pair.2 player - reward (quittingSingletonTerminal player) player := by
    intro player
    exact minimumTerminalSemantic_singletonMargin
      (reward := reward) pair hpair hminimum hpositive player
  have hL : d ≤ L := hmargin owner
  let p := d / (8 * (M + d))
  let θ : ℕ → ℝ := fun n => p / ((n : ℝ) + 1)
  have hp0 : 0 < p := by
    dsimp only [p]
    positivity
  have hp1 : p < 1 := by
    dsimp only [p]
    apply (div_lt_one (by positivity : 0 < 8 * (M + d))).2
    nlinarith
  have hθ0 : ∀ n, 0 < θ n := by
    intro n
    dsimp only [θ]
    positivity
  have hθ1 : ∀ n, θ n < 1 := by
    intro n
    have hθle : θ n ≤ p := by
      dsimp only [θ]
      exact (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
        (by nlinarith [hp0])
    exact hθle.trans_lt hp1
  have hθTendsto : Tendsto θ atTop (nhds 0) := by
    have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hscaled := hbase.const_mul p
    simpa only [θ, div_eq_mul_inv, one_mul, zero_mul, mul_comm] using hscaled
  have hthreshold : ∀ n, 4 * M * θ n < d := by
    intro n
    have hθle : θ n ≤ p := by
      dsimp only [θ]
      exact (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
        (by nlinarith [hp0])
    have hscaled := mul_le_mul_of_nonneg_left hθle (by positivity : 0 ≤ 4 * M)
    have hMp : 4 * M * p < d := by
      dsimp only [p]
      have hdenom : 0 < 8 * (M + d) := by positivity
      calc
        4 * M * (d / (8 * (M + d))) =
            (4 * M * d) / (8 * (M + d)) := by ring
        _ < d := (div_lt_iff₀ hdenom).2 (by nlinarith [mul_pos hM hd])
    exact hscaled.trans_lt hMp
  let reachedAt (n : ℕ) (data : ℕ × ι) :=
    quittingSoloSemanticIterate reward owner
      (quittingHazardCoin (θ n) (hθ0 n).le (hθ1 n).le) pair data.1
  let Good (n : ℕ) (data : ℕ × ι) : Prop :=
    (reachedAt n data).2 data.2 -
          reward (quittingSingletonTerminal data.2) data.2 ∈
        Set.Ioc (2 * M * θ n) (4 * M * θ n) ∧
      quittingTerminalSemanticDebtSum (reachedAt n data) ≤ L
  have hgoodExists : ∀ n, ∃ data, Good n data := by
    intro n
    have hinitial : ∀ player, 4 * M * θ n <
        pair.2 player - reward (quittingSingletonTerminal player) player := by
      intro player
      exact (hthreshold n).trans_le (hmargin player)
    obtain ⟨steps, crossing, hstepsPos, hstepsLe, hcrossingNe,
        hbefore, hcrossing, haffine, hdebtEq, hdebtUpper⟩ :=
      exists_first_solo_capThreshold_hit reward pair hne hM hreward hpair
        (hθ0 n) (hθ1 n) hinitial hpreempted
    refine ⟨(steps, crossing), hcrossing, ?_⟩
    exact hdebtUpper.trans_eq (max_eq_right hL)
  let data : ℕ → ℕ × ι := fun n => Classical.choose (hgoodExists n)
  have hdata : ∀ n, Good n (data n) := fun n =>
    Classical.choose_spec (hgoodExists n)
  let reached : ℕ → QuittingTerminalSemanticPair ι := fun n => reachedAt n (data n)
  let crossing : ℕ → ι := fun n => (data n).2
  have hreachedCarrier : ∀ n, reached n ∈ quittingTerminalSemanticCarrier reward := by
    intro n
    exact quittingSoloSemanticIterate_mem_carrier reward owner _ pair hpair (data n).1
  obtain ⟨fixed, select₁, hselect₁, hfixed⟩ :=
    Math.exists_fixed_label_on_strictMono_subsequence crossing
  obtain ⟨limit, hlimitCarrier, select₂, hselect₂, hlimit⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq
      (fun n => hreachedCarrier (select₁ n))
  have hselectTendsto : Tendsto (fun n => select₁ (select₂ n)) atTop atTop :=
    hselect₁.tendsto_atTop.comp hselect₂.tendsto_atTop
  have hθSelected : Tendsto (fun n => θ (select₁ (select₂ n))) atTop (nhds 0) :=
    hθTendsto.comp hselectTendsto
  have hcrossingMarginZero : Tendsto (fun n =>
      (reached (select₁ (select₂ n))).2 fixed -
        reward (quittingSingletonTerminal fixed) fixed) atTop (nhds 0) := by
    apply squeeze_zero
      (g := fun n => 4 * M * θ (select₁ (select₂ n)))
    · intro n
      have hf := hfixed (select₂ n)
      dsimp only [crossing] at hf
      rw [← hf]
      dsimp only [reached]
      have hlower := (hdata (select₁ (select₂ n))).1.1
      exact (by positivity : 0 < 2 * M * θ (select₁ (select₂ n))).trans hlower |>.le
    · intro n
      have hf := hfixed (select₂ n)
      dsimp only [crossing] at hf
      rw [← hf]
      exact (hdata (select₁ (select₂ n))).1.2
    · simpa using (hθSelected.const_mul (4 * M))
  have hcapLimit : Tendsto (fun n =>
      (reached (select₁ (select₂ n))).2 fixed -
        reward (quittingSingletonTerminal fixed) fixed) atTop
      (nhds (limit.2 fixed -
        reward (quittingSingletonTerminal fixed) fixed)) := by
    exact (((continuous_apply fixed).comp continuous_snd).tendsto limit |>.sub
      tendsto_const_nhds).comp hlimit
  have hlimitCap : limit.2 fixed =
      reward (quittingSingletonTerminal fixed) fixed := by
    have hzero := tendsto_nhds_unique hcapLimit hcrossingMarginZero
    linarith
  have hdebtLimit : Tendsto (fun n => quittingTerminalSemanticDebtSum
      (reached (select₁ (select₂ n)))) atTop
      (nhds (quittingTerminalSemanticDebtSum limit)) :=
    continuous_quittingTerminalSemanticDebtSum.tendsto limit |>.comp hlimit
  have hdLimit : d ≤ quittingTerminalSemanticDebtSum limit := by
    apply ge_of_tendsto' hdebtLimit
    intro n
    exact hminimum _ (hreachedCarrier (select₁ (select₂ n)))
  have hlimitL : quittingTerminalSemanticDebtSum limit ≤ L := by
    apply le_of_tendsto' hdebtLimit
    intro n
    exact (hdata (select₁ (select₂ n))).2
  let shift : Payoff ι := fun _ => d / 2
  obtain ⟨root, hnash⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) (limit.2 - shift)
  have hgap : (limit.2 - shift) fixed ≤
      reward (quittingSingletonTerminal fixed) fixed - d / 2 := by
    dsimp only [shift, Pi.sub_apply]
    rw [hlimitCap]
  have habsorptionRaw := belowSingleton_exactRoot_absorptionMass_lowerBound
    reward (limit.2 - shift) root fixed (show 0 < d / 2 by positivity)
      hreward hgap hnash
  have habsorption : d / (4 * M + d) ≤ quittingRootAbsorptionMass root := by
    convert habsorptionRaw using 1
    field_simp
    ring
  let prefixed := quittingTerminalSemanticPrefix reward root limit
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier reward root limit hlimitCarrier
  have hbudget := quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (reward := reward) limit (d / 2) root (by positivity)
  have hdefect :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward (limit.2 - shift) root).mp hnash
  dsimp only [shift] at hdefect
  rw [hdefect, add_zero] at hbudget
  have hminPrefix := hminimum prefixed hprefixed
  dsimp only [prefixed] at hminPrefix
  have habsorptionNonnegative : 0 ≤ quittingRootAbsorptionMass root :=
    quittingRootAbsorptionMass_nonneg root
  have hdebtGap : 0 < quittingTerminalSemanticDebtSum limit - d / 2 := by
    linarith
  have hsubstitute :
      quittingTerminalSemanticDebtSum limit -
          quittingRootAbsorptionMass root *
            (quittingTerminalSemanticDebtSum limit - d / 2) ≤
        quittingTerminalSemanticDebtSum limit -
          (d / (4 * M + d)) *
            (quittingTerminalSemanticDebtSum limit - d / 2) := by
    exact sub_le_sub_left
      (mul_le_mul_of_nonneg_right habsorption hdebtGap.le) _
  have hquadratic : d + d ^ 2 / (8 * M) ≤
      quittingTerminalSemanticDebtSum limit := by
    have hdenom : 0 < 4 * M + d := by positivity
    have hcore := hminPrefix.trans (hbudget.trans hsubstitute)
    field_simp at hcore ⊢
    nlinarith [mul_pos hM hd]
  have hcapQuadratic : d + d ^ 2 / (8 * M) ≤ L :=
    hquadratic.trans hlimitL
  refine ⟨hcapQuadratic, ?_⟩
  dsimp only [L, quittingTerminalSemanticDebt]
  linarith

/-- In particular, the prescribed payoff of a preempted owner lies a
strictly positive quadratic distance above its singleton reward. -/
theorem positive_minimum_preemptedOwner_prescribedMargin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (owner blocker : ι) {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hpreempted : 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker) :
    quittingTerminalSemanticDebtSum pair ^ 2 / (8 * M) ≤
      pair.1 owner - reward (quittingSingletonTerminal owner) owner := by
  have hmargins := positive_minimum_preemptedOwner_quadraticMargins
    reward pair hpair hminimum owner blocker hM hreward hpositive hpreempted
  have hnonnegative :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have hownerDebt : quittingTerminalSemanticDebt pair owner ≤
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hnonnegative player) (Finset.mem_univ owner)
  linarith [hmargins.2]

/-- At a positive semantic minimum, every owner with nonnegative singleton
reward has a strict solo preemptor. -/
theorem exists_strict_preemptor_of_positive_minimum_nonnegative_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (owner : ι)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker := by
  letI : Nonempty ι := ⟨owner⟩
  by_contra hnone
  push Not at hnone
  have huniform := isUniformEquilibriumPayoff_soloReward_of_nonnegative_noPreemptor
    reward owner howner fun other hother => by linarith [hnone other]
  obtain ⟨zeroPair, hzeroPair, hzeroMinimum, hzero⟩ :=
    hasZeroMinimumTerminalSemanticDebt_of_exists_uniformEquilibriumPayoff
      reward ⟨_, huniform⟩
  have hle := hminimum zeroPair hzeroPair
  rw [hzero] at hle
  linarith

/-- The preempted-owner quadratic margins therefore hold for every owner
whose singleton reward is nonnegative. -/
theorem positive_minimum_nonnegativeOwner_quadraticMargins
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (owner : ι) {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    let d := quittingTerminalSemanticDebtSum pair
    pair.2 owner - reward (quittingSingletonTerminal owner) owner ≥
        d + d ^ 2 / (8 * M) ∧
      pair.1 owner - reward (quittingSingletonTerminal owner) owner ≥
        d - quittingTerminalSemanticDebt pair owner + d ^ 2 / (8 * M) := by
  obtain ⟨blocker, hpreempted⟩ :=
    exists_strict_preemptor_of_positive_minimum_nonnegative_singleton
      reward pair hminimum hpositive owner howner
  exact positive_minimum_preemptedOwner_quadraticMargins
    reward pair hpair hminimum owner blocker hM hreward hpositive hpreempted

/-- For four players, the existing singleton-column blocker certificate
upgrades the preempted-owner result to every owner without singleton signs. -/
theorem positive_minimum_fourPlayer_allOwner_quadraticMargins
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hplayers : Fintype.card ι = 4)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    ∀ owner,
      let d := quittingTerminalSemanticDebtSum pair
      pair.2 owner - reward (quittingSingletonTerminal owner) owner ≥
          d + d ^ 2 / (8 * M) ∧
        pair.1 owner - reward (quittingSingletonTerminal owner) owner ≥
          d - quittingTerminalSemanticDebt pair owner + d ^ 2 / (8 * M) := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
    intro hexists
    obtain ⟨zeroPair, hzeroPair, hzeroMinimum, hzero⟩ :=
      hasZeroMinimumTerminalSemanticDebt_of_exists_uniformEquilibriumPayoff
        reward hexists
    have hle := hminimum zeroPair hzeroPair
    rw [hzero] at hle
    linarith
  obtain ⟨hnoHomogeneous, certificate⟩ :=
    exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform
      reward hplayers hno
  obtain ⟨certificate⟩ := certificate
  intro owner
  apply positive_minimum_preemptedOwner_quadraticMargins
    reward pair hpair hminimum owner (certificate.blocker owner)
      hM hreward hpositive
  exact certificate.gap_pos.trans_le (certificate.gap_le owner)

end GameTheory
