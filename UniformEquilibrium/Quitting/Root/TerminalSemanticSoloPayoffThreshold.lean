import UniformEquilibrium.Quitting.Root.TerminalSemanticSoloCapThreshold

/-! # Actual payoff/debt stopping for a concentrated solo block

This stopping predicate is not the cap-threshold predicate. A failed positive
singleton-column test need not give a strict preemptor. All Continue-branch
hypotheses used below are derived from the actual payoff thresholds.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The owner-solo block stops at small TOTAL debt or at an outsider payoff
crossing. Neither endpoint discards the old actual source. -/
def quittingSoloPayoffDebtThresholdHit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι) (coin : PMF Bool)
    (working : ℝ) (steps : ℕ) : Prop :=
  quittingTerminalSemanticDebtSum
      (quittingSoloSemanticIterate reward owner coin source steps) < working ∨
    ∃ who, who ≠ owner ∧
      (quittingSoloSemanticIterate reward owner coin source steps).1 who ≤
        reward (quittingSingletonTerminal who) who + working / 2

/-- The weak-exclusion owner and failure of the charged-margin test force
concentration of the ACTUAL source debt, not an auxiliary continuation debt. -/
theorem terminalSemantic_concentrated_source_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι)
    {working : ℝ} (hworking : 0 < working)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hdebt : working ≤ quittingTerminalSemanticDebtSum source)
    (hmargins : ∀ who, quittingTerminalSemanticDebtSum source - working / 8 <
      source.2 who - reward (quittingSingletonTerminal who) who)
    (howner : source.1 owner ≤ reward (quittingSingletonTerminal owner) owner) :
    (∑ who ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt source who) <
        working / 8 ∧
    (∀ who, who ≠ owner →
      reward (quittingSingletonTerminal who) who + 3 * working / 4 < source.1 who) ∧
    working / 4 < source.2 owner - reward (quittingSingletonTerminal owner) owner ∧
    source.2 owner - reward (quittingSingletonTerminal owner) owner ≤
      quittingTerminalSemanticDebtSum source := by
  have hnonnegative := quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hsource
  have hsplit := Finset.sum_erase_add
    (s := Finset.univ) (f := quittingTerminalSemanticDebt source) (Finset.mem_univ owner)
  change (∑ who ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt source who) +
    quittingTerminalSemanticDebt source owner = quittingTerminalSemanticDebtSum source at hsplit
  have hownerDebt : quittingTerminalSemanticDebtSum source - working / 8 <
      quittingTerminalSemanticDebt source owner := by
    have hm := hmargins owner
    unfold quittingTerminalSemanticDebt
    linarith
  have houtside : (∑ who ∈ Finset.univ.erase owner,
      quittingTerminalSemanticDebt source who) < working / 8 := by linarith
  have hownerDebtLe : quittingTerminalSemanticDebt source owner ≤
      quittingTerminalSemanticDebtSum source :=
    Finset.single_le_sum (fun who _ => hnonnegative who) (Finset.mem_univ owner)
  refine ⟨houtside, ?_, ?_, ?_⟩
  · intro who hne
    have hcoordinate : quittingTerminalSemanticDebt source who ≤
        ∑ player ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt source player :=
      Finset.single_le_sum (fun player _ => hnonnegative player)
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ who⟩)
    have hm := hmargins who
    have hsmall := hcoordinate.trans_lt houtside
    unfold quittingTerminalSemanticDebt at hsmall
    linarith
  · have hm := hmargins owner
    linarith
  · unfold quittingTerminalSemanticDebt at hownerDebtLe
    linarith

/-- The concentrated owner's prescribed source payoff is within the actual
one-eighth collar BELOW its singleton, as well as weakly below it. -/
theorem terminalSemantic_concentrated_owner_payoff_lower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι) (working : ℝ)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hmargin : quittingTerminalSemanticDebtSum source - working / 8 <
      source.2 owner - reward (quittingSingletonTerminal owner) owner) :
    reward (quittingSingletonTerminal owner) owner - working / 8 < source.1 owner := by
  have hownerDebtLe : quittingTerminalSemanticDebt source owner ≤
      quittingTerminalSemanticDebtSum source :=
    Finset.single_le_sum (fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hsource who)
      (Finset.mem_univ owner)
  unfold quittingTerminalSemanticDebt at hownerDebtLe
  linarith

/-- An actual source cap above the owner's singleton stays exactly constant
under its solo prefixes. The source concentration test supplies this inequality. -/
theorem quittingSoloSemanticIterate_owner_cap_eq_of_singleton_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι) (coin : PMF Bool)
    (hcap : reward (quittingSingletonTerminal owner) owner ≤ source.2 owner) :
    ∀ steps, (quittingSoloSemanticIterate reward owner coin source steps).2 owner =
      source.2 owner := by
  intro steps
  induction steps with
  | zero => simp only [quittingSoloSemanticIterate_zero]
  | succ steps ih =>
      rw [quittingSoloSemanticIterate_succ]
      unfold quittingTerminalSemanticPrefix
      dsimp only
      rw [quittingRootQuitPayoff_soloStationaryRoot_owner,
        quittingRootContinuePayoff_soloStationaryRoot_owner,
        Function.update_self, quittingSoloReward_self, ih, max_eq_right hcap]

/-- Before the actual payoff/debt hit, the entire cap-threshold premise
follows from actual cap domination and the constant owner cap. -/
theorem quittingSoloPayoffDebtThreshold_not_hit_cap_above
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι)
    {M working θ : ℝ}
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hworking : 0 < working) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcharge : 4 * M * θ = working / 4)
    (howner : working / 4 <
      source.2 owner - reward (quittingSingletonTerminal owner) owner)
    (steps : ℕ)
    (hnothit : ¬quittingSoloPayoffDebtThresholdHit reward source owner
      (quittingHazardCoin θ hθ0.le hθ1.le) working steps) :
    ∀ who, 4 * M * θ <
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source steps).2 who -
        reward (quittingSingletonTerminal who) who := by
  intro who
  rw [hcharge]
  by_cases hwho : who = owner
  · subst who
    rw [quittingSoloSemanticIterate_owner_cap_eq_of_singleton_le
      reward source owner _ (by linarith) steps]
    exact howner
  · have hpayoff : reward (quittingSingletonTerminal who) who + working / 2 <
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source steps).1 who := by
      apply lt_of_not_ge
      intro hle
      exact hnothit (Or.inr ⟨who, hwho, hle⟩)
    have hnonnegative := quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (quittingSoloSemanticIterate_mem_carrier reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source hsource steps) who
    unfold quittingTerminalSemanticDebt at hnonnegative
    linarith

/-- A geometric cutoff forces a genuine payoff/debt hit even when the
failed column remains above the blocker singleton. No preemption is assumed. -/
theorem exists_soloPayoffDebtThreshold_hit_le_horizon
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner blocker : ι)
    {M working θ : ℝ} (hM : 0 < M) (hworking : 0 < working)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcharge : 4 * M * θ = working / 4)
    (howner : working / 4 <
      source.2 owner - reward (quittingSingletonTerminal owner) owner)
    (hne : blocker ≠ owner)
    (hcolumn : reward (quittingSingletonTerminal owner) blocker <
      reward (quittingSingletonTerminal blocker) blocker + working / 4) :
    ∃ steps ≤ quittingSoloCapThresholdHorizon M θ (working / 2),
      quittingSoloPayoffDebtThresholdHit reward source owner
        (quittingHazardCoin θ hθ0.le hθ1.le) working steps := by
  classical
  let horizon := quittingSoloCapThresholdHorizon M θ (working / 2)
  by_contra hnot
  have hbefore : ∀ steps, steps ≤ horizon →
      ¬quittingSoloPayoffDebtThresholdHit reward source owner
        (quittingHazardCoin θ hθ0.le hθ1.le) working steps := by
    intro steps hsteps hhit
    exact hnot ⟨steps, hsteps, hhit⟩
  have habove : ∀ steps, steps < horizon → ∀ who, 4 * M * θ <
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source steps).2 who -
      reward (quittingSingletonTerminal who) who := by
    intro steps hsteps
    exact quittingSoloPayoffDebtThreshold_not_hit_cap_above reward source owner
      hsource hworking hθ0 hθ1 hcharge howner steps (hbefore steps hsteps.le)
  have haffine := quittingSoloSemanticIterate_eq_affine_of_before_threshold
    reward source owner hreward hsource hθ0 hθ1 horizon habove
  have hpayoff := congrArg (fun pair => pair.1 blocker) haffine
  have hpower := two_mul_pow_quittingSoloCapThresholdHorizon_le_half hM hθ0 hθ1
    (show 0 < working / 2 by positivity)
  have hbox := quittingTerminalSemanticCarrier_mem_box reward source hreward hsource
  have hupper := hbox.1.2 blocker
  have hlower := (abs_le.mp (hreward (quittingSingletonTerminal owner) blocker)).1
  have hgap : source.1 blocker - reward (quittingSingletonTerminal owner) blocker ≤
      2 * M := by linarith
  have hρ : 0 ≤ (1 - θ) ^ horizon := pow_nonneg (by linarith) _
  have hscaled := mul_le_mul_of_nonneg_left hgap hρ
  have hcrossing :
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source horizon).1 blocker ≤
        reward (quittingSingletonTerminal blocker) blocker + working / 2 := by
    dsimp only at hpayoff
    change 2 * M * (1 - θ) ^ horizon ≤ (working / 2) / 2 at hpower
    nlinarith
  exact hbefore horizon le_rfl (Or.inr ⟨blocker, hne, hcrossing⟩)

/-- The same actual first-hit ledger retains signed payoffs/full caps and
does not increase total debt. The outsider debt remains concentrated. -/
theorem quittingSoloPayoffDebtThreshold_before_ledger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι)
    {M working θ : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hworking : 0 < working) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcharge : 4 * M * θ = working / 4)
    (hdebt : working ≤ quittingTerminalSemanticDebtSum source)
    (hmargins : ∀ who, quittingTerminalSemanticDebtSum source - working / 8 <
      source.2 who - reward (quittingSingletonTerminal who) who)
    (howner : source.1 owner ≤ reward (quittingSingletonTerminal owner) owner)
    (steps : ℕ)
    (hbefore : ∀ k, k < steps →
      ¬quittingSoloPayoffDebtThresholdHit reward source owner
        (quittingHazardCoin θ hθ0.le hθ1.le) working k) :
    let reached := quittingSoloSemanticIterate reward owner
      (quittingHazardCoin θ hθ0.le hθ1.le) source steps
    reached =
      (fun who => reward (quittingSingletonTerminal owner) who +
          (1 - θ) ^ steps * (source.1 who - reward (quittingSingletonTerminal owner) who),
       fun who => if who = owner then source.2 owner else
         reward (quittingSingletonTerminal owner) who +
           (1 - θ) ^ steps * (source.2 who - reward (quittingSingletonTerminal owner) who)) ∧
    quittingTerminalSemanticDebtSum reached =
      (1 - θ) ^ steps * quittingTerminalSemanticDebtSum source +
        (1 - (1 - θ) ^ steps) *
          (source.2 owner - reward (quittingSingletonTerminal owner) owner) ∧
    quittingTerminalSemanticDebtSum reached ≤ quittingTerminalSemanticDebtSum source ∧
    (∑ who ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt reached who) <
      working / 8 := by
  dsimp only
  obtain ⟨houtside, _, hownerAbove, hownerMargin⟩ :=
    terminalSemantic_concentrated_source_bounds
      reward source owner hworking hsource hdebt hmargins howner
  have habove : ∀ k, k < steps → ∀ who, 4 * M * θ <
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source k).2 who -
        reward (quittingSingletonTerminal who) who := by
    intro k hk
    exact quittingSoloPayoffDebtThreshold_not_hit_cap_above reward source owner
      hsource hworking hθ0 hθ1 hcharge hownerAbove k (hbefore k hk)
  have haffine := quittingSoloSemanticIterate_eq_affine_of_before_threshold
    reward source owner hreward hsource hθ0 hθ1 steps habove
  have hledger := quittingSoloSemanticIterate_debtSum_eq_of_before_threshold
    reward source owner hreward hsource hθ0 hθ1 steps habove
  have hbound := quittingSoloSemanticIterate_debtSum_le_max_of_before_threshold
    reward source owner hreward hsource hθ0 hθ1 steps habove
  have hρ1 : (1 - θ) ^ steps ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have houtsideNonnegative :
      0 ≤ ∑ who ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt source who :=
    Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hsource who
  refine ⟨haffine, hledger, ?_, ?_⟩
  · exact hbound.trans (max_le le_rfl hownerMargin)
  · have hother : ∀ who ∈ Finset.univ.erase owner,
        quittingTerminalSemanticDebt
          (quittingSoloSemanticIterate reward owner
            (quittingHazardCoin θ hθ0.le hθ1.le) source steps) who =
          (1 - θ) ^ steps * quittingTerminalSemanticDebt source who := by
      intro who hwho
      rw [haffine]
      simp only [quittingTerminalSemanticDebt, ite_eq_right (Finset.ne_of_mem_erase hwho)]
      ring
    rw [Finset.sum_congr rfl hother, ← Finset.mul_sum]
    exact (mul_le_of_le_one_left houtsideNonnegative hρ1).trans_lt houtside

/-- The packet's literal one-row debt subtraction, using the SAME current
actual payoff and outside debts. The owner's mixture need not be optimal. -/
theorem quittingSoloPayoffDebtThreshold_debtSum_step_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι)
    {M working θ : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hworking : 0 < working) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcharge : 4 * M * θ = working / 4)
    (hdebt : working ≤ quittingTerminalSemanticDebtSum source)
    (hmargins : ∀ who, quittingTerminalSemanticDebtSum source - working / 8 <
      source.2 who - reward (quittingSingletonTerminal who) who)
    (howner : source.1 owner ≤ reward (quittingSingletonTerminal owner) owner)
    (steps : ℕ)
    (hbefore : ∀ k, k < steps + 1 →
      ¬quittingSoloPayoffDebtThresholdHit reward source owner
        (quittingHazardCoin θ hθ0.le hθ1.le) working k) :
    let current := quittingSoloSemanticIterate reward owner
      (quittingHazardCoin θ hθ0.le hθ1.le) source steps
    quittingTerminalSemanticDebtSum
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source (steps + 1)) =
      quittingTerminalSemanticDebtSum current - θ *
        ((reward (quittingSingletonTerminal owner) owner - current.1 owner) +
          ∑ who ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt current who) := by
  dsimp only
  have hledgerNext := (quittingSoloPayoffDebtThreshold_before_ledger
    reward source owner hreward hsource hworking hθ0 hθ1 hcharge hdebt hmargins howner
    (steps + 1) hbefore).2.1
  have hledgerCurrent := (quittingSoloPayoffDebtThreshold_before_ledger
    reward source owner hreward hsource hworking hθ0 hθ1 hcharge hdebt hmargins howner
    steps (fun k hk => hbefore k (Nat.lt_succ_of_lt hk))).2.1
  have hcap := quittingSoloSemanticIterate_owner_cap_eq_of_singleton_le
    reward source owner (quittingHazardCoin θ hθ0.le hθ1.le)
    (by
      have hmargin := (terminalSemantic_concentrated_source_bounds
        reward source owner hworking hsource hdebt hmargins howner).2.2.1
      linarith) steps
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (f := quittingTerminalSemanticDebt
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source steps)) (Finset.mem_univ owner)
  change (∑ who ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source steps) who) +
    ((quittingSoloSemanticIterate reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source steps).2 owner -
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source steps).1 owner) =
    quittingTerminalSemanticDebtSum
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin θ hθ0.le hθ1.le) source steps) at hsplit
  rw [hcap] at hsplit
  have hrecurrence : quittingTerminalSemanticDebtSum
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source (steps + 1)) =
      (1 - θ) * quittingTerminalSemanticDebtSum
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source steps) +
        θ * (source.2 owner - reward (quittingSingletonTerminal owner) owner) := by
    rw [hledgerNext, hledgerCurrent, pow_succ]
    ring
  rw [hrecurrence]
  have hbracket : quittingTerminalSemanticDebtSum
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source steps) -
        (source.2 owner - reward (quittingSingletonTerminal owner) owner) =
      (reward (quittingSingletonTerminal owner) owner -
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source steps).1 owner) +
        ∑ who ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt
          (quittingSoloSemanticIterate reward owner
            (quittingHazardCoin θ hθ0.le hθ1.le) source steps) who := by linarith
  rw [← hbracket]
  ring

/-- Concentration and the exact ledger give nonincrease between ANY two
actual prefixes before and including the payoff/debt endpoint. -/
theorem quittingSoloPayoffDebtThreshold_debtSum_antitone_until_hit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι)
    {M working θ : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hworking : 0 < working) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcharge : 4 * M * θ = working / 4)
    (hdebt : working ≤ quittingTerminalSemanticDebtSum source)
    (hmargins : ∀ who, quittingTerminalSemanticDebtSum source - working / 8 <
      source.2 who - reward (quittingSingletonTerminal who) who)
    (howner : source.1 owner ≤ reward (quittingSingletonTerminal owner) owner)
    {earlier later : ℕ} (horder : earlier ≤ later)
    (hbefore : ∀ k, k < later →
      ¬quittingSoloPayoffDebtThresholdHit reward source owner
        (quittingHazardCoin θ hθ0.le hθ1.le) working k) :
    quittingTerminalSemanticDebtSum
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source later) ≤
      quittingTerminalSemanticDebtSum
        (quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source earlier) := by
  have hledgerLater := (quittingSoloPayoffDebtThreshold_before_ledger
    reward source owner hreward hsource hworking hθ0 hθ1 hcharge hdebt hmargins howner
    later hbefore).2.1
  have hledgerEarlier := (quittingSoloPayoffDebtThreshold_before_ledger
    reward source owner hreward hsource hworking hθ0 hθ1 hcharge hdebt hmargins howner
    earlier (fun k hk => hbefore k (hk.trans_le horder))).2.1
  have hmargin := (terminalSemantic_concentrated_source_bounds
    reward source owner hworking hsource hdebt hmargins howner).2.2.2
  have hpower : (1 - θ) ^ later ≤ (1 - θ) ^ earlier :=
    pow_le_pow_of_le_one (by linarith) (by linarith) horder
  have hscaled := mul_le_mul_of_nonneg_right hpower
    (sub_nonneg.mpr hmargin)
  rw [hledgerLater, hledgerEarlier]
  nlinarith

/-- A nonterminal hit returns an ACTUAL charged-margin witness for the next
auxiliary step; no root/cap annotation is selected here. -/
theorem quittingSoloPayoffDebtThreshold_charged_margin_of_nonterminal_hit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι) (coin : PMF Bool)
    {working : ℝ} (hworking : 0 < working)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (steps : ℕ)
    (hhit : quittingSoloPayoffDebtThresholdHit reward source owner coin working steps)
    (hdebt : working ≤ quittingTerminalSemanticDebtSum
      (quittingSoloSemanticIterate reward owner coin source steps))
    (houtside : (∑ who ∈ Finset.univ.erase owner,
      quittingTerminalSemanticDebt (quittingSoloSemanticIterate reward owner coin source steps)
        who) < working / 8) :
    ∃ who, who ≠ owner ∧
      (quittingSoloSemanticIterate reward owner coin source steps).2 who -
          reward (quittingSingletonTerminal who) who < 5 * working / 8 ∧
      (quittingSoloSemanticIterate reward owner coin source steps).2 who -
          reward (quittingSingletonTerminal who) who <
        quittingTerminalSemanticDebtSum
          (quittingSoloSemanticIterate reward owner coin source steps) - working / 8 := by
  rcases hhit with hearly | ⟨who, hne, hpayoff⟩
  · exact False.elim (not_lt_of_ge hdebt hearly)
  · have hcoordinate : quittingTerminalSemanticDebt
        (quittingSoloSemanticIterate reward owner coin source steps) who ≤
        ∑ player ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt
          (quittingSoloSemanticIterate reward owner coin source steps) player :=
      Finset.single_le_sum (fun player _ =>
        quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
          (quittingSoloSemanticIterate_mem_carrier reward owner coin source hsource steps) player)
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ who⟩)
    have hsmall := hcoordinate.trans_lt houtside
    unfold quittingTerminalSemanticDebt at hsmall
    exact ⟨who, hne, by linarith, by linarith⟩

end GameTheory
