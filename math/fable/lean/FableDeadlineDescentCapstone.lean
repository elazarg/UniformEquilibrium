/-
Anchored erasure and finite deadline descent at a canonical pure-time global
minimum.

Fix a canonical pure-time date vector whose terminal-semantic pair attains a
strictly positive global minimum of total debt over the whole semantic
carrier.  Two nested finite operations leave that minimum fibre.

The inner operation is anchored erasure.  At the earliest quitting date,
retain one anchor and send every other quitter of that date to Never, one
player at a time.  Every intermediate date vector is again canonical, so its
pair is a carrier point and its total debt is at least the minimum.  Either
one erased sibling already carries strictly more debt - and the run stops
there - or the last sibling is a canonical global minimum whose earliest
quitting coalition is the anchor alone.

The outer operation is deadline descent.  At such a singleton minimum the
owner's exact pure-time response either leaves the minimum fibre, or ties it
while deleting the earliest date from the finite date support without adding
anything.  The finite date support is therefore a strictly decreasing natural
rank along the ties, and the all-Never vector is not a positive minimum, so
the run terminates.

The common exit is one actual off-minimum canonical profile.  There a
maximum-debt player carries at least the average debt, and against pure-time
opponents its behavioral cap is attained by a literal pure time or Never, so
its exact response is a paid pure-time port whose gain is at least that
average - which strictly exceeds the average of the original minimum.

Nothing here selects an equilibrium, bounds the number of players, or claims
that the exit profile is itself a minimum, a Nash point, or an equilibrium
payoff.
-/
import FableDeadlineDescentStep

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Reading the cap coordinate of a semantic pair -/

private theorem fable_capstone_semanticPair_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingTerminalSemanticPair reward profile).2 who =
      quittingContinuationBestResponseValue reward profile who := rfl

/-! ## P1: an average-debt paid pure-time response -/

/-- Some coordinate of a strictly positive total debt carries at least the
average debt. -/
private theorem fable_exists_averageDebt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    ∃ responder : ι,
      quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) /
          (Fintype.card ι : ℝ) ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) responder := by
  classical
  have hsumEq : ∑ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := rfl
  have hne : (Finset.univ : Finset ι).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset ι) with
      hempty | hne
    · exfalso
      rw [← hsumEq, hempty, Finset.sum_empty] at hpositive
      exact lt_irrefl _ hpositive
    · exact hne
  have hcardPos : 0 < Fintype.card ι := by
    rw [← Finset.card_univ]
    exact Finset.card_pos.mpr hne
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hcardPos
  by_contra hcontra
  have hlt : ∀ who ∈ (Finset.univ : Finset ι),
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who <
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) /
          (Fintype.card ι : ℝ) := by
    intro who _
    exact not_le.mp fun hle => hcontra ⟨who, hle⟩
  have hstrict := Finset.sum_lt_sum_of_nonempty hne hlt
  rw [hsumEq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstrict
  have hfix : (Fintype.card ι : ℝ) *
      (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) /
        (Fintype.card ι : ℝ)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := by
    rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hcard),
      mul_one]
  rw [hfix] at hstrict
  exact lt_irrefl _ hstrict

omit [DecidableEq ι] in
/-- A canonical pure-time profile is deadline bounded at the largest finite
date its date vector uses. -/
private theorem fable_canonicalProfile_deadlineBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tau : ι → Option ℕ) :
    FableDeadlineBounded reward (fableCanonicalProfile reward tau)
      ((fableDateFinset tau).sup id) :=
  fableDeadlineBounded_canonicalProfile reward tau
    (fun who _date hdate =>
      Finset.le_sup (f := id) (mem_fableDateFinset.mpr ⟨who, hdate⟩))

/-- **P1.**  At any canonical pure-time profile with strictly positive total
debt, some player has a literal pure-time or Never response whose gain is at
least the average debt. -/
theorem fable_positiveDebt_canonicalProfile_averagePaidResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (sigma : ι → Option ℕ)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward sigma))) :
    ∃ (responder : ι) (choice : Option ℕ),
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward sigma)) /
          (Fintype.card ι : ℝ) ≤
        quittingPureTimeDeviationPayoff reward
            (fableCanonicalProfile reward sigma) responder choice -
          quittingTerminalPayoff reward (fableCanonicalProfile reward sigma)
            responder := by
  obtain ⟨responder, hresponder⟩ := fable_exists_averageDebt_le reward
    (fableCanonicalProfile reward sigma) hpositive
  obtain ⟨choice, hvalue, -⟩ := fable_exists_deadlineBounded_pureTime_eq_cap
    reward (fableCanonicalProfile reward sigma) responder
    (fable_canonicalProfile_deadlineBounded reward sigma)
  refine ⟨responder, choice, ?_⟩
  have hdebt := fable_semanticDebt_profile_eq reward
    (fableCanonicalProfile reward sigma) responder
  rw [hvalue]
  linarith

/-! ## P2: a positive minimum uses at least one finite date -/

/-- **P2.**  A canonical pure-time profile whose semantic pair is a strictly
positive global minimum cannot be the all-Never vector. -/
theorem fable_canonicalMinimum_dateFinset_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tau : ι → Option ℕ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau))) :
    (fableDateFinset tau).Nonempty := by
  classical
  rcases Finset.eq_empty_or_nonempty (fableDateFinset tau) with hempty | hne
  · exfalso
    have hnever : ∀ who, tau who = none := by
      intro who
      cases hcase : tau who with
      | none => rfl
      | some date =>
          exfalso
          have hmem : date ∈ fableDateFinset tau :=
            mem_fableDateFinset.mpr ⟨who, hcase⟩
          rw [hempty] at hmem
          exact absurd hmem (by simp)
    have hcap : ∀ player, quittingContinuationBestResponseValue reward
        (fableCanonicalProfile reward tau) player =
        max (reward (quittingSingletonTerminal player) player) 0 :=
      fun player => fable_canonicalPureTime_never_cap reward tau player
        (fun other _ => hnever other)
    have hpayoff : ∀ player, quittingTerminalPayoff reward
        (fableCanonicalProfile reward tau) player = 0 := by
      intro player
      rw [← fable_canonicalPureTime_deviationPayoff_self reward tau player,
        hnever player]
      exact fable_canonicalPureTime_never_value_of_none reward tau player
        (fun other _ => hnever other)
    have hmem := quittingTerminalSemanticPair_mem_carrier reward
      (fableCanonicalProfile reward tau)
    by_cases hsign : ∀ player,
        reward (quittingSingletonTerminal player) player < 0
    · have hzero : quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward tau)) = 0 := by
        unfold quittingTerminalSemanticDebtSum
        refine Finset.sum_eq_zero fun player _ => ?_
        rw [fable_semanticDebt_profile_eq, hcap player, hpayoff player,
          max_eq_right (hsign player).le, sub_zero]
      linarith
    · have hexists : ∃ player,
          0 ≤ reward (quittingSingletonTerminal player) player := by
        by_contra hcontra
        exact hsign fun player => not_le.mp fun hle => hcontra ⟨player, hle⟩
      obtain ⟨player, hplayer⟩ := hexists
      have hmargin := minimumTerminalSemantic_singletonMargin
        (reward := reward) _ hmem hminimum hpositive player
      rw [fable_capstone_semanticPair_cap, hcap player,
        max_eq_left hplayer] at hmargin
      linarith
  · exact hne

/-! ## Erasing one coordinate to Never -/

/-- Erasing one coordinate to `Never` deletes exactly that player from every
canonical quitting coalition. -/
private theorem fable_canonicalQuitSet_update_never
    (tau : ι → Option ℕ) (player : ι) (time : ℕ) :
    fableCanonicalQuitSet (Function.update tau player none) time =
      (fableCanonicalQuitSet tau time).erase player := by
  ext who
  simp only [fableCanonicalQuitSet_mem, Finset.mem_erase]
  constructor
  · intro hwho
    by_cases hcase : who = player
    · subst who
      rw [Function.update_self] at hwho
      exact absurd hwho (by simp)
    · rw [Function.update_of_ne hcase] at hwho
      exact ⟨hcase, hwho⟩
  · rintro ⟨hcase, hwho⟩
    rw [Function.update_of_ne hcase]
    exact hwho

/-- Erasing one coordinate to `Never` never adds a finite date. -/
private theorem fable_dateFinset_update_never_subset
    (tau : ι → Option ℕ) (player : ι) :
    fableDateFinset (Function.update tau player none) ⊆
      fableDateFinset tau := by
  intro date hdate
  obtain ⟨who, hwho⟩ := mem_fableDateFinset.mp hdate
  by_cases hcase : who = player
  · subst who
    rw [Function.update_self] at hwho
    exact absurd hwho (by simp)
  · rw [Function.update_of_ne hcase] at hwho
    exact mem_fableDateFinset.mpr ⟨who, hwho⟩

/-- Once the anchor is the only quitter left at the earliest date, every
other finite date is strictly later. -/
private theorem fable_singletonEarliest_of_erase_empty
    {tau : ι → Option ℕ} {anchor : ι} {start : ℕ}
    (hempty : (fableCanonicalQuitSet tau start).erase anchor = ∅)
    (hlower : ∀ other, other ≠ anchor →
      ∀ date, tau other = some date → start ≤ date) :
    ∀ other, other ≠ anchor →
      ∀ date, tau other = some date → start < date := by
  intro other hother date hdate
  rcases lt_or_eq_of_le (hlower other hother date hdate) with hlt | heq
  · exact hlt
  · exfalso
    subst heq
    have hmem : other ∈ (fableCanonicalQuitSet tau start).erase anchor :=
      Finset.mem_erase.mpr ⟨hother, fableCanonicalQuitSet_mem.mpr hdate⟩
    rw [hempty] at hmem
    exact absurd hmem (by simp)

/-! ## P3, inner induction: anchored erasure -/

/-- **Anchored erasure.**  Send the anchor's date-`start` siblings to Never
one at a time.  Either some sibling already carries strictly more total debt
than the source, or the run ends at a canonical date vector with the same
total debt whose only date-`start` quitter is the anchor.  No step adds a
finite date. -/
theorem fable_anchoredErasure_offMinimum_or_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (anchor : ι)
    (start : ℕ) :
    ∀ (steps : ℕ) (tau : ι → Option ℕ),
      ((fableCanonicalQuitSet tau start).erase anchor).card ≤ steps →
      tau anchor = some start →
      (∀ other, other ≠ anchor →
        ∀ date, tau other = some date → start ≤ date) →
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward tau)) ≤
          quittingTerminalSemanticDebtSum candidate) →
      ∃ sigma : ι → Option ℕ,
        fableDateFinset sigma ⊆ fableDateFinset tau ∧
        (quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
              (fableCanonicalProfile reward tau)) <
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (fableCanonicalProfile reward sigma)) ∨
          (quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (fableCanonicalProfile reward sigma)) =
              quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (fableCanonicalProfile reward tau)) ∧
            sigma anchor = some start ∧
            ∀ other, other ≠ anchor →
              ∀ date, sigma other = some date → start < date)) := by
  classical
  intro steps
  induction steps with
  | zero =>
      intro tau hcard hanchor hlower _
      have hempty : (fableCanonicalQuitSet tau start).erase anchor = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      exact ⟨tau, Finset.Subset.refl _, Or.inr ⟨rfl, hanchor,
        fable_singletonEarliest_of_erase_empty hempty hlower⟩⟩
  | succ steps ih =>
      intro tau hcard hanchor hlower hminimum
      by_cases hstep : ((fableCanonicalQuitSet tau start).erase anchor).Nonempty
      · obtain ⟨player, hplayer⟩ := hstep
        obtain ⟨hplayerNe, hplayerMem⟩ := Finset.mem_erase.mp hplayer
        have hplayerDate : tau player = some start :=
          fableCanonicalQuitSet_mem.mp hplayerMem
        have hcard' : ((fableCanonicalQuitSet
            (Function.update tau player none) start).erase anchor).card ≤
            steps := by
          rw [fable_canonicalQuitSet_update_never, Finset.erase_right_comm,
            Finset.card_erase_of_mem hplayer]
          omega
        have hanchor' :
            Function.update tau player none anchor = some start := by
          rw [Function.update_of_ne (Ne.symm hplayerNe)]
          exact hanchor
        have hlower' : ∀ other, other ≠ anchor → ∀ date,
            Function.update tau player none other = some date →
            start ≤ date := by
          intro other hother date hdate
          by_cases hcase : other = player
          · subst other
            rw [Function.update_self] at hdate
            exact absurd hdate (by simp)
          · rw [Function.update_of_ne hcase] at hdate
            exact hlower other hother date hdate
        have hmemTarget := quittingTerminalSemanticPair_mem_carrier reward
          (fableCanonicalProfile reward (Function.update tau player none))
        rcases lt_or_eq_of_le (hminimum _ hmemTarget) with hstrict | heq
        · exact ⟨Function.update tau player none,
            fable_dateFinset_update_never_subset tau player, Or.inl hstrict⟩
        · have hminimum' : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
              quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair
                  reward (fableCanonicalProfile reward
                    (Function.update tau player none))) ≤
                quittingTerminalSemanticDebtSum candidate := by
            intro candidate hcandidate
            rw [← heq]
            exact hminimum candidate hcandidate
          obtain ⟨sigma, hsub, hcase⟩ := ih (Function.update tau player none)
            hcard' hanchor' hlower' hminimum'
          refine ⟨sigma, hsub.trans
            (fable_dateFinset_update_never_subset tau player), ?_⟩
          rcases hcase with hstrict | ⟨hequal, hsigmaAnchor, hsigmaLower⟩
          · refine Or.inl ?_
            rw [heq]
            exact hstrict
          · exact Or.inr ⟨hequal.trans heq.symm, hsigmaAnchor, hsigmaLower⟩
      · have hempty : (fableCanonicalQuitSet tau start).erase anchor = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hstep
        exact ⟨tau, Finset.Subset.refl _, Or.inr ⟨rfl, hanchor,
          fable_singletonEarliest_of_erase_empty hempty hlower⟩⟩

/-! ## P3, outer induction: deadline descent -/

/-- The descent carried by the finite date support, as a natural rank. -/
private theorem fable_descent_aux
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∀ (rank : ℕ) (tau : ι → Option ℕ),
      (fableDateFinset tau).card ≤ rank →
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward tau)) ≤
          quittingTerminalSemanticDebtSum candidate) →
      0 < quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau)) →
      ∃ sigma : ι → Option ℕ,
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward tau)) <
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward sigma)) ∧
        ∃ (responder : ι) (choice : Option ℕ),
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
                (fableCanonicalProfile reward sigma)) /
              (Fintype.card ι : ℝ) ≤
            quittingPureTimeDeviationPayoff reward
                (fableCanonicalProfile reward sigma) responder choice -
              quittingTerminalPayoff reward
                (fableCanonicalProfile reward sigma) responder := by
  classical
  intro rank
  induction rank with
  | zero =>
      intro tau hcard hminimum hpositive
      exfalso
      have hne := fable_canonicalMinimum_dateFinset_nonempty reward tau
        hminimum hpositive
      have hpos := Finset.card_pos.mpr hne
      omega
  | succ rank ih =>
      intro tau hcard hminimum hpositive
      have hne := fable_canonicalMinimum_dateFinset_nonempty reward tau
        hminimum hpositive
      obtain ⟨anchor, hanchor⟩ := mem_fableDateFinset.mp
        (Finset.min'_mem (fableDateFinset tau) hne)
      have hlower : ∀ other, other ≠ anchor → ∀ date,
          tau other = some date → (fableDateFinset tau).min' hne ≤ date := by
        intro other _ date hdate
        exact Finset.min'_le _ _ (mem_fableDateFinset.mpr ⟨other, hdate⟩)
      obtain ⟨sigma, hsub, hcase⟩ :=
        fable_anchoredErasure_offMinimum_or_singleton reward anchor
          ((fableDateFinset tau).min' hne)
          ((fableCanonicalQuitSet tau
            ((fableDateFinset tau).min' hne)).erase anchor).card tau le_rfl
          hanchor hlower hminimum
      rcases hcase with hstrict | ⟨hequal, hsigmaAnchor, hsigmaLower⟩
      · exact ⟨sigma, hstrict,
          fable_positiveDebt_canonicalProfile_averagePaidResponse reward sigma
            (by linarith)⟩
      · have hpositiveSigma : 0 < quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (fableCanonicalProfile reward sigma)) := by
          rw [hequal]
          exact hpositive
        have hminimumSigma : ∀ candidate ∈
            quittingTerminalSemanticCarrier reward,
            quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair
                reward (fableCanonicalProfile reward sigma)) ≤
              quittingTerminalSemanticDebtSum candidate := by
          intro candidate hcandidate
          rw [hequal]
          exact hminimum candidate hcandidate
        by_cases hopponent :
            ∃ other, other ≠ anchor ∧ ∃ date, sigma other = some date
        · obtain ⟨choice, hgain, hkill, hstrictArm, herase, hssub⟩ :=
            fable_singletonMinimum_response reward sigma anchor hsigmaAnchor
              hsigmaLower hminimumSigma hpositiveSigma hopponent
          by_cases hdiff : quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward (fableCanonicalProfile
                reward (Function.update sigma anchor choice))) =
              quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (fableCanonicalProfile reward sigma))
          · have hminimumTarget : ∀ candidate ∈
                quittingTerminalSemanticCarrier reward,
                quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair
                    reward (fableCanonicalProfile reward
                      (Function.update sigma anchor choice))) ≤
                  quittingTerminalSemanticDebtSum candidate := by
              intro candidate hcandidate
              rw [hdiff]
              exact hminimumSigma candidate hcandidate
            have hpositiveTarget : 0 < quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward (fableCanonicalProfile
                  reward (Function.update sigma anchor choice))) := by
              rw [hdiff]
              exact hpositiveSigma
            have hcardTarget :
                (fableDateFinset
                  (Function.update sigma anchor choice)).card ≤ rank := by
              have hdrop := Finset.card_lt_card hssub
              have hkeep := Finset.card_le_card hsub
              omega
            obtain ⟨target, htarget, hport⟩ := ih
              (Function.update sigma anchor choice) hcardTarget hminimumTarget
              hpositiveTarget
            refine ⟨target, ?_, hport⟩
            rw [← hequal, ← hdiff]
            exact htarget
          · have hstrictTarget := hstrictArm hdiff
            refine ⟨Function.update sigma anchor choice, ?_, ?_⟩
            · rw [← hequal]
              exact hstrictTarget
            · exact fable_positiveDebt_canonicalProfile_averagePaidResponse
                reward (Function.update sigma anchor choice) (by linarith)
        · have hnever : ∀ other, other ≠ anchor → sigma other = none := by
            intro other hother
            cases hcase : sigma other with
            | none => rfl
            | some date => exact absurd ⟨other, hother, date, hcase⟩ hopponent
          obtain ⟨hgain, hkill, hemptyDates, hstrictTarget⟩ :=
            fable_singletonMinimum_neverResponse reward sigma anchor
              hsigmaAnchor hnever hminimumSigma hpositiveSigma
          refine ⟨Function.update sigma anchor none, ?_, ?_⟩
          · rw [← hequal]
            exact hstrictTarget
          · exact fable_positiveDebt_canonicalProfile_averagePaidResponse
              reward (Function.update sigma anchor none) (by linarith)

/-! ## The capstone -/

/-- **Anchored erasure plus deadline descent.**  A canonical pure-time date
vector whose terminal-semantic pair is a strictly positive global minimum of
total debt yields an actual off-minimum canonical pure-time profile carrying a
literal pure-time or Never response whose gain is at least that profile's
average debt - hence strictly more than the minimum's average debt. -/
theorem fable_canonicalMinimum_offMinimum_paidPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tau : ι → Option ℕ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau))) :
    ∃ sigma : ι → Option ℕ,
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) <
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward sigma)) ∧
      ∃ (responder : ι) (choice : Option ℕ),
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
              (fableCanonicalProfile reward sigma)) /
            (Fintype.card ι : ℝ) ≤
          quittingPureTimeDeviationPayoff reward
              (fableCanonicalProfile reward sigma) responder choice -
            quittingTerminalPayoff reward (fableCanonicalProfile reward sigma)
              responder :=
  fable_descent_aux reward (fableDateFinset tau).card tau le_rfl hminimum
    hpositive

end GameTheory
