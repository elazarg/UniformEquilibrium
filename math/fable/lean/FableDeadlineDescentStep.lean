/-
The exact owner response at a canonical pure-time singleton minimum.

Fix a canonical pure-time profile whose terminal-semantic pair attains a
strictly positive global minimum of total debt over the whole semantic
carrier, and suppose the earliest quitting coalition is the singleton `{b}`
at date `t`: every other player's finite date is strictly later.

Then `b`'s prescribed payoff is its solo terminal reward, `b` carries the
entire total debt, and every other coordinate carries none.  This is the
singleton margin of the minimum together with the coordinatewise
nonnegativity of debt, and nothing else.

From there the owner's exact pure-time response is transparent.  When some
opponent still has a finite date, the earliest one is `u > t`, and the margin
collapse of the canonical value table leaves exactly two candidate responses,
quit at `u` or never quit.  Either one gains exactly the total debt, kills
`b`'s own debt, and - because `u` was already an opponent date and `t` was
`b`'s alone - erases `t` from the finite date support without adding anything.
Carrier minimality then leaves only two possibilities for the target's total
debt: an exact tie, or a strict excess.

When every opponent is Never, the cap collapses to the maximum of the solo
reward and zero, so positive debt forces a negative solo reward and a zero
cap.  The response is Never and its target is the all-Continue profile, whose
total debt is the sum of the positive parts of the solo rewards.  There the
off-minimum exit is unconditional: a tie would make the all-Continue pair a
positive global minimum, and its own singleton margins then force every solo
reward negative, hence zero total debt.

Nothing here iterates the step, selects an equilibrium, or claims that the
response preserves the other coordinates' debts.
-/
import FableCanonicalPureTime
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The finite date support of a canonical date vector -/

/-- The finite set of dates a canonical date vector actually uses. -/
def fableDateFinset (tau : ι → Option ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun who => (tau who).toFinset

omit [DecidableEq ι] in
theorem mem_fableDateFinset {tau : ι → Option ℕ} {date : ℕ} :
    date ∈ fableDateFinset tau ↔ ∃ who, tau who = some date := by
  constructor
  · intro hmem
    obtain ⟨who, _, hwho⟩ := Finset.mem_biUnion.mp hmem
    exact ⟨who, Option.mem_def.mp (Option.mem_toFinset.mp hwho)⟩
  · rintro ⟨who, hwho⟩
    exact Finset.mem_biUnion.mpr ⟨who, Finset.mem_univ who,
      Option.mem_toFinset.mpr (Option.mem_def.mpr hwho)⟩

/-- The finite set of dates the observer's opponents use. -/
private def fableOpponentDateFinset (observer : ι) (tau : ι → Option ℕ) :
    Finset ℕ :=
  (Finset.univ.erase observer).biUnion fun who => (tau who).toFinset

private theorem mem_fableOpponentDateFinset
    {observer : ι} {tau : ι → Option ℕ} {date : ℕ} :
    date ∈ fableOpponentDateFinset observer tau ↔
      ∃ who, who ≠ observer ∧ tau who = some date := by
  constructor
  · intro hmem
    obtain ⟨who, hwho, hdate⟩ := Finset.mem_biUnion.mp hmem
    exact ⟨who, (Finset.mem_erase.mp hwho).1,
      Option.mem_def.mp (Option.mem_toFinset.mp hdate)⟩
  · rintro ⟨who, hne, hdate⟩
    exact Finset.mem_biUnion.mpr
      ⟨who, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ who⟩,
        Option.mem_toFinset.mpr (Option.mem_def.mpr hdate)⟩

/-! ## Two definitional readings -/

private theorem fable_semanticPair_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingTerminalSemanticPair reward profile).2 who =
      quittingContinuationBestResponseValue reward profile who := rfl

omit [DecidableEq ι] in
private theorem fable_canonicalProfile_allNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    fableCanonicalProfile reward (fun _ => none) =
      quittingAlwaysContinueProfile reward := rfl

/-- **The owner's own date is not a deviation.**  The pure-time deviation
payoff overwrites the observer's coordinate by the value it already carries,
so at the observer's own canonical date it is the prescribed payoff. -/
theorem fable_canonicalPureTime_deviationPayoff_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) :
    quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
        observer (tau observer) =
      quittingTerminalPayoff reward (fableCanonicalProfile reward tau)
        observer := by
  have hself : Function.update (fableCanonicalProfile reward tau) observer
      (quittingPureTimeBehaviorStrategy reward observer (tau observer)) =
      fableCanonicalProfile reward tau := by
    funext who
    by_cases hwho : who = observer
    · subst who
      simp [fableCanonicalProfile]
    · rw [Function.update_of_ne hwho]
  unfold quittingPureTimeDeviationPayoff
  rw [hself]

/-! ## D1: the profile facts at a singleton minimum -/

/-- **Prescribed payoff at a singleton earliest coalition.**  Every opponent
date is strictly later than the observer's own, so the observer's prescribed
payoff is its solo terminal reward. -/
theorem fable_singletonMinimum_prescribed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {deadline : ℕ}
    (hobserver : tau observer = some deadline)
    (hsingleton : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → deadline < date) :
    quittingTerminalPayoff reward (fableCanonicalProfile reward tau) observer =
      reward (quittingSingletonTerminal observer) observer := by
  have hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → deadline + 1 ≤ date := by
    intro other hother date hdate
    have hlt := hsingleton other hother date hdate
    omega
  have hvalue := fable_canonicalPureTime_value_of_lt reward tau observer
    hearliest (by omega : deadline < deadline + 1)
  rw [← fable_canonicalPureTime_deviationPayoff_self reward tau observer,
    hobserver]
  exact hvalue

/-- **The singleton owner carries the whole total debt.**  The global-minimum
singleton margin bounds the total debt below by the owner's own debt, and
coordinatewise nonnegativity bounds it above. -/
theorem fable_singletonMinimum_ownerDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {deadline : ℕ}
    (hobserver : tau observer = some deadline)
    (hsingleton : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → deadline < date)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau))) :
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau)) observer =
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau)) := by
  have hmem := quittingTerminalSemanticPair_mem_carrier reward
    (fableCanonicalProfile reward tau)
  have hmargin := minimumTerminalSemantic_singletonMargin
    (reward := reward) _ hmem hminimum hpositive observer
  rw [fable_semanticPair_cap] at hmargin
  have hprescribed := fable_singletonMinimum_prescribed reward tau observer
    hobserver hsingleton
  have hdebt := fable_semanticDebt_profile_eq reward
    (fableCanonicalProfile reward tau) observer
  have hle : quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
      (fableCanonicalProfile reward tau)) observer ≤
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau)) := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum (fun player _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hmem player)
      (Finset.mem_univ observer)
  linarith

/-- **Every other coordinate is debt free at a singleton minimum.** -/
theorem fable_singletonMinimum_otherDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {deadline : ℕ}
    (hobserver : tau observer = some deadline)
    (hsingleton : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → deadline < date)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau)))
    (other : ι) (hother : other ≠ observer) :
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
      (fableCanonicalProfile reward tau)) other = 0 := by
  have hmem := quittingTerminalSemanticPair_mem_carrier reward
    (fableCanonicalProfile reward tau)
  have hnonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hmem
  have howner := fable_singletonMinimum_ownerDebt reward tau observer hobserver
    hsingleton hminimum hpositive
  have hsplit : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau)) =
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) observer +
        ∑ j ∈ Finset.univ.erase observer,
          quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward tau)) j := by
    unfold quittingTerminalSemanticDebtSum
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ observer)).symm
  rw [howner] at hsplit
  have hzero : ∑ j ∈ Finset.univ.erase observer,
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau)) j = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hzero other
    (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)

/-! ## D2: the exact response against a later opponent deadline -/

/-- **The singleton-minimum response with a surviving opponent deadline.**
The owner has one canonical pure-time response - quit at the earliest opponent
date, or never quit - that gains exactly the total debt, kills its own debt,
deletes the owner's date from the finite date support without introducing any
new date, and either ties the carrier minimum or strictly exceeds it. -/
theorem fable_singletonMinimum_response
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {deadline : ℕ}
    (hobserver : tau observer = some deadline)
    (hsingleton : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → deadline < date)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau)))
    (hopponent : ∃ other, other ≠ observer ∧ ∃ date, tau other = some date) :
    ∃ choice : Option ℕ,
      quittingTerminalPayoff reward (fableCanonicalProfile reward
            (Function.update tau observer choice)) observer -
          quittingTerminalPayoff reward (fableCanonicalProfile reward tau)
            observer =
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) ∧
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward
            (Function.update tau observer choice))) observer = 0 ∧
      (quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward
              (Function.update tau observer choice))) ≠
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward tau)) →
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward tau)) <
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward
              (Function.update tau observer choice)))) ∧
      fableDateFinset (Function.update tau observer choice) ⊆
        (fableDateFinset tau).erase deadline ∧
      fableDateFinset (Function.update tau observer choice) ⊂
        fableDateFinset tau := by
  obtain ⟨witness, hwitness, seed, hseed⟩ := hopponent
  have hne : (fableOpponentDateFinset observer tau).Nonempty :=
    ⟨seed, mem_fableOpponentDateFinset.mpr ⟨witness, hwitness, hseed⟩⟩
  obtain ⟨member, hmember, hmemberDate⟩ :=
    mem_fableOpponentDateFinset.mp
      (Finset.min'_mem (fableOpponentDateFinset observer tau) hne)
  have hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date →
        (fableOpponentDateFinset observer tau).min' hne ≤ date := by
    intro other hother date hdate
    exact Finset.min'_le _ _
      (mem_fableOpponentDateFinset.mpr ⟨other, hother, hdate⟩)
  have hlate : deadline < (fableOpponentDateFinset observer tau).min' hne :=
    hsingleton member hmember _ hmemberDate
  have hcoalition : ∀ other,
      other ∈ fableCanonicalOpponentQuitSet observer tau
          ((fableOpponentDateFinset observer tau).min' hne) ↔
        (other ≠ observer ∧
          tau other = some ((fableOpponentDateFinset observer tau).min' hne)) :=
    fun _ => fableCanonicalOpponentQuitSet_mem
  have hcoalitionNe : (fableCanonicalOpponentQuitSet observer tau
      ((fableOpponentDateFinset observer tau).min' hne)).Nonempty :=
    ⟨member, (hcoalition member).mpr ⟨hmember, hmemberDate⟩⟩
  have hprescribed := fable_singletonMinimum_prescribed reward tau observer
    hobserver hsingleton
  have howner := fable_singletonMinimum_ownerDebt reward tau observer hobserver
    hsingleton hminimum hpositive
  have hdebt := fable_semanticDebt_profile_eq reward
    (fableCanonicalProfile reward tau) observer
  have hmargin : reward (quittingSingletonTerminal observer) observer <
      quittingContinuationBestResponseValue reward
        (fableCanonicalProfile reward tau) observer := by linarith
  obtain ⟨choice, hchoiceMem, hchoiceValue⟩ :=
    fable_exists_canonicalPureTime_deadlineResponse_eq_cap reward tau observer
      hearliest hcoalition hcoalitionNe (by omega) hmargin
  have hchoiceCases : choice =
      some ((fableOpponentDateFinset observer tau).min' hne) ∨
      choice = none := by simpa using hchoiceMem
  have htargetPayoff : quittingTerminalPayoff reward
      (fableCanonicalProfile reward (Function.update tau observer choice))
        observer =
      quittingContinuationBestResponseValue reward
        (fableCanonicalProfile reward tau) observer := by
    rw [← hchoiceValue]
    unfold quittingPureTimeDeviationPayoff
    rw [fableCanonicalProfile_update]
  have htargetCap : quittingContinuationBestResponseValue reward
      (fableCanonicalProfile reward (Function.update tau observer choice))
        observer =
      quittingContinuationBestResponseValue reward
        (fableCanonicalProfile reward tau) observer := by
    rw [fableCanonicalProfile_update]
    exact fable_continuationBestResponseValue_update_self reward
      (fableCanonicalProfile reward tau) observer _
  have herase : fableDateFinset (Function.update tau observer choice) ⊆
      (fableDateFinset tau).erase deadline := by
    intro date hdate
    obtain ⟨who, hwho⟩ := mem_fableDateFinset.mp hdate
    rw [Finset.mem_erase]
    by_cases hcase : who = observer
    · subst who
      rw [Function.update_self] at hwho
      rcases hchoiceCases with hchoice | hchoice
      · rw [hchoice] at hwho
        have hvalue : date = (fableOpponentDateFinset observer tau).min' hne :=
          (Option.some.inj hwho).symm
        subst hvalue
        exact ⟨by omega, mem_fableDateFinset.mpr ⟨member, hmemberDate⟩⟩
      · rw [hchoice] at hwho
        exact absurd hwho (by simp)
    · rw [Function.update_of_ne hcase] at hwho
      have hgap := hsingleton who hcase date hwho
      exact ⟨by omega, mem_fableDateFinset.mpr ⟨who, hwho⟩⟩
  refine ⟨choice, ?_, ?_, ?_, herase, ?_⟩
  · rw [htargetPayoff, hprescribed]
    linarith
  · rw [fable_semanticDebt_profile_eq, htargetCap, htargetPayoff, sub_self]
  · intro hdiff
    rcases lt_or_eq_of_le (hminimum _ (quittingTerminalSemanticPair_mem_carrier
      reward (fableCanonicalProfile reward
        (Function.update tau observer choice)))) with hstrict | heq
    · exact hstrict
    · exact absurd heq.symm hdiff
  · refine (Finset.ssubset_iff_of_subset
      (herase.trans (Finset.erase_subset _ _))).mpr ⟨deadline, ?_, ?_⟩
    · exact mem_fableDateFinset.mpr ⟨observer, hobserver⟩
    · exact fun hcontra => Finset.notMem_erase deadline (fableDateFinset tau)
        (herase hcontra)

/-! ## D3: the exact response against all-Never opponents -/

/-- **The singleton-minimum response against all-Never opponents.**  Positive
debt forces a negative solo reward and a zero cap, so the exact response is
Never; its target is the all-Continue profile, its date support is empty, and
it leaves the positive global minimum unconditionally. -/
theorem fable_singletonMinimum_neverResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {deadline : ℕ}
    (hobserver : tau observer = some deadline)
    (hnever : ∀ other, other ≠ observer → tau other = none)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau))) :
    quittingTerminalPayoff reward (fableCanonicalProfile reward
          (Function.update tau observer none)) observer -
        quittingTerminalPayoff reward (fableCanonicalProfile reward tau)
          observer =
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau)) ∧
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward
          (Function.update tau observer none))) observer = 0 ∧
    fableDateFinset (Function.update tau observer none) = ∅ ∧
    quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward tau)) <
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (fableCanonicalProfile reward
          (Function.update tau observer none))) := by
  have hsingleton : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → deadline < date := by
    intro other hother date hdate
    rw [hnever other hother] at hdate
    exact absurd hdate (by simp)
  have hprescribed := fable_singletonMinimum_prescribed reward tau observer
    hobserver hsingleton
  have howner := fable_singletonMinimum_ownerDebt reward tau observer hobserver
    hsingleton hminimum hpositive
  have hdebt := fable_semanticDebt_profile_eq reward
    (fableCanonicalProfile reward tau) observer
  have hcap := fable_canonicalPureTime_never_cap reward tau observer hnever
  have hmaxZero :
      max (reward (quittingSingletonTerminal observer) observer) 0 = 0 := by
    rcases max_choice (reward (quittingSingletonTerminal observer) observer) 0
      with hchoice | hchoice
    · exfalso
      rw [hchoice] at hcap
      linarith
    · exact hchoice
  have htarget : fableCanonicalProfile reward
      (Function.update tau observer none) =
      quittingAlwaysContinueProfile reward :=
    fable_canonicalProfile_update_never_eq_allContinue reward tau observer hnever
  have hcapAll : ∀ player, quittingContinuationBestResponseValue reward
      (quittingAlwaysContinueProfile reward) player =
      max (reward (quittingSingletonTerminal player) player) 0 := by
    intro player
    rw [← fable_canonicalProfile_allNever reward]
    exact fable_canonicalPureTime_never_cap reward (fun _ => none) player
      (fun _ _ => rfl)
  have hcapTarget : ∀ player, quittingContinuationBestResponseValue reward
      (fableCanonicalProfile reward (Function.update tau observer none))
        player = max (reward (quittingSingletonTerminal player) player) 0 := by
    intro player
    rw [htarget]
    exact hcapAll player
  have hpayoffTarget : ∀ player, quittingTerminalPayoff reward
      (fableCanonicalProfile reward (Function.update tau observer none))
        player = 0 := by
    intro player
    rw [htarget, quittingTerminalPayoff_quittingAlwaysContinue]
  have htargetPayoff := hpayoffTarget observer
  have htargetCap : quittingContinuationBestResponseValue reward
      (fableCanonicalProfile reward (Function.update tau observer none))
        observer = 0 := by
    rw [hcapTarget observer, hmaxZero]
  rw [hcap, hmaxZero] at hdebt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htargetPayoff, hprescribed]
    linarith
  · rw [fable_semanticDebt_profile_eq, htargetCap, htargetPayoff, sub_zero]
  · refine Finset.eq_empty_of_forall_notMem fun date hdate => ?_
    obtain ⟨who, hwho⟩ := mem_fableDateFinset.mp hdate
    by_cases hcase : who = observer
    · subst who
      rw [Function.update_self] at hwho
      exact absurd hwho (by simp)
    · rw [Function.update_of_ne hcase, hnever who hcase] at hwho
      exact absurd hwho (by simp)
  · have hmemTarget := quittingTerminalSemanticPair_mem_carrier reward
      (fableCanonicalProfile reward (Function.update tau observer none))
    rcases lt_or_eq_of_le (hminimum _ hmemTarget) with hstrict | heq
    · exact hstrict
    · exfalso
      have hpositiveTarget : 0 < quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (fableCanonicalProfile reward
            (Function.update tau observer none))) := by linarith
      have hminimumTarget : ∀ candidate ∈
          quittingTerminalSemanticCarrier reward,
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
              (fableCanonicalProfile reward
                (Function.update tau observer none))) ≤
            quittingTerminalSemanticDebtSum candidate := by
        intro candidate hcandidate
        have hle := hminimum candidate hcandidate
        linarith
      have hnegative : ∀ player,
          reward (quittingSingletonTerminal player) player < 0 := by
        intro player
        rcases lt_or_ge (reward (quittingSingletonTerminal player) player) 0
          with hlt | hge
        · exact hlt
        · exfalso
          have hplayer := minimumTerminalSemantic_singletonMargin
            (reward := reward) _ hmemTarget hminimumTarget hpositiveTarget
            player
          rw [fable_semanticPair_cap, hcapTarget player,
            max_eq_left hge] at hplayer
          linarith
      have hzero : quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (fableCanonicalProfile reward
            (Function.update tau observer none))) = 0 := by
        unfold quittingTerminalSemanticDebtSum
        refine Finset.sum_eq_zero fun player _ => ?_
        rw [fable_semanticDebt_profile_eq, hcapTarget player,
          hpayoffTarget player, max_eq_right (hnegative player).le, sub_zero]
      linarith

end GameTheory
