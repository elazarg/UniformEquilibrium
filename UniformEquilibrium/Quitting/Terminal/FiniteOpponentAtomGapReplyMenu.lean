import UniformEquilibrium.Quitting.Terminal.FiniteOpponentLateResponse
import UniformEquilibrium.Quitting.Terminal.StoppingLawCanonicalization

/-!
# Finite opponent atom-gap reply menus

Against finitely supported opponent clocks, only the position of a reply
relative to the opponents' finite atoms matters.  The finite menu containing
`Never`, date zero, every atom, and every successor of an atom therefore
contains an outcome-equivalent reply to every deterministic stopping time.
Pure-time extremality then makes the unrestricted behavioral cap attain its
value on this menu.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A representative of the gap containing `time`: zero before the first
atom, the atom itself on the calendar, and one after the last earlier atom
otherwise. -/
def quittingAtomGapRepresentative (calendar : Finset ℕ) (time : ℕ) : ℕ :=
  if time ∈ calendar then time
  else if hbefore : (calendar.filter fun atom => atom < time).Nonempty then
    (calendar.filter fun atom => atom < time).max' hbefore + 1
  else 0

/-- `Never`, zero, the opponent atoms, and their immediate successors. -/
def quittingFiniteOpponentAtomGapReplyMenu
    (calendar : Finset ℕ) : Finset (Option ℕ) :=
  insert none <| insert (some 0) <|
    calendar.image some ∪ calendar.image (fun time => some (time + 1))

theorem quittingAtomGapRepresentative_mem_replyMenu
    (calendar : Finset ℕ) (time : ℕ) :
    some (quittingAtomGapRepresentative calendar time) ∈
      quittingFiniteOpponentAtomGapReplyMenu calendar := by
  unfold quittingAtomGapRepresentative quittingFiniteOpponentAtomGapReplyMenu
  split_ifs with htime hbefore
  · simp [htime]
  · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    right
    right
    right
    exact ⟨(calendar.filter fun atom => atom < time).max' hbefore,
      (Finset.mem_filter.mp (Finset.max'_mem _ hbefore)).1, rfl⟩
  · simp

private theorem atom_le_atomGapRepresentative_iff
    (calendar : Finset ℕ) {atom time : ℕ} (hatom : atom ∈ calendar) :
    atom ≤ quittingAtomGapRepresentative calendar time ↔ atom ≤ time := by
  unfold quittingAtomGapRepresentative
  split_ifs with htime hbefore
  · rfl
  · have hne : atom ≠ time := fun heq => htime (heq ▸ hatom)
    constructor
    · intro hle
      have hmaxLt := Finset.max'_lt_iff _ hbefore |>.2 fun entry hentry =>
        (Finset.mem_filter.mp hentry).2
      omega
    · intro hle
      have hlt : atom < time := lt_of_le_of_ne hle hne
      exact (Finset.le_max' _ atom (Finset.mem_filter.mpr ⟨hatom, hlt⟩)).trans
        (Nat.le_succ _)
  · constructor
    · omega
    · intro hle
      have : atom < time := lt_of_le_of_ne hle fun heq => htime (heq ▸ hatom)
      exact (hbefore ⟨atom, Finset.mem_filter.mpr ⟨hatom, this⟩⟩).elim

private theorem atomGapRepresentative_le_atom_iff
    (calendar : Finset ℕ) {atom time : ℕ} (hatom : atom ∈ calendar) :
    quittingAtomGapRepresentative calendar time ≤ atom ↔ time ≤ atom := by
  unfold quittingAtomGapRepresentative
  split_ifs with htime hbefore
  · rfl
  · have hne : time ≠ atom := fun heq => htime (heq ▸ hatom)
    constructor
    · intro hle
      by_contra hnot
      have hatomLt : atom < time := Nat.lt_of_not_ge hnot
      have hatomMax := Finset.le_max'
        (calendar.filter fun entry => entry < time) atom
        (Finset.mem_filter.mpr ⟨hatom, hatomLt⟩)
      omega
    · intro hle
      have hmaxLt := (Finset.mem_filter.mp (Finset.max'_mem _ hbefore)).2
      omega
  · constructor
    · intro _
      by_contra hnot
      have hatomLt : atom < time := Nat.lt_of_not_ge hnot
      exact hbefore ⟨atom, Finset.mem_filter.mpr ⟨hatom, hatomLt⟩⟩
    · exact fun _ => Nat.zero_le atom

private theorem quittingFirstStoppingOutcome_update_atomGapRepresentative
    (calendar : Finset ℕ) (times : ι → Option ℕ) (who : ι) (time : ℕ)
    (hcalendar : ∀ player, player ≠ who → ∀ atom,
      times player = some atom → atom ∈ calendar) :
    let : Nonempty ι := ⟨who⟩
    quittingFirstStoppingOutcome (Function.update times who (some time)) =
      quittingFirstStoppingOutcome (Function.update times who
        (some (quittingAtomGapRepresentative calendar time))) := by
  let : Nonempty ι := ⟨who⟩
  apply quittingFirstStoppingOutcome_eq_of_order_and_never
  · intro first second
    by_cases hfirst : first = who
    · subst first
      by_cases hsecond : second = who
      · subst second
        simp
      · simp only [Function.update_self, Function.update_of_ne hsecond]
        cases hchoice : times second with
        | none => simp [quittingStoppingTimeValue]
        | some atom =>
            simp only [quittingStoppingTimeValue]
            exact WithTop.coe_le_coe.trans
              ((atomGapRepresentative_le_atom_iff calendar
                (hcalendar second hsecond atom hchoice)).symm.trans
                  WithTop.coe_le_coe.symm)
    · by_cases hsecond : second = who
      · subst second
        simp only [Function.update_self, Function.update_of_ne hfirst]
        cases hchoice : times first with
        | none => simp [quittingStoppingTimeValue]
        | some atom =>
            simp only [quittingStoppingTimeValue]
            exact WithTop.coe_le_coe.trans
              ((atom_le_atomGapRepresentative_iff calendar
                (hcalendar first hfirst atom hchoice)).symm.trans
                  WithTop.coe_le_coe.symm)
      · simp [Function.update_of_ne hfirst, Function.update_of_ne hsecond]
  · intro player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Function.update_of_ne hplayer]

/-- Every deterministic reply has an outcome-equivalent reply in the finite
atom-gap menu.  Only opponents are required to use finite calendar atoms. -/
theorem exists_mem_quittingFiniteOpponentAtomGapReplyMenu_payoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (who : ι) (calendar : Finset ℕ)
    (hcalendar : ∀ player, player ≠ who → ∀ time,
      laws player (some time) ≠ 0 → time ∈ calendar)
    (choice : Option ℕ) :
    ∃ representative ∈ quittingFiniteOpponentAtomGapReplyMenu calendar,
      quittingTerminalPayoff reward
          (Function.update (quittingStoppingLawProfile reward laws) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who =
        quittingTerminalPayoff reward
          (Function.update (quittingStoppingLawProfile reward laws) who
            (quittingPureTimeBehaviorStrategy reward who representative)) who := by
  let : Nonempty ι := ⟨who⟩
  cases choice with
  | none =>
      exact ⟨none, by simp [quittingFiniteOpponentAtomGapReplyMenu], rfl⟩
  | some time =>
      let representative := quittingAtomGapRepresentative calendar time
      refine ⟨some representative,
        quittingAtomGapRepresentative_mem_replyMenu calendar time, ?_⟩
      rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq,
        ← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq]
      simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
        quittingStoppingLawExpectedPayoff]
      congr 1
      unfold quittingIndependentTerminalOutcomeLaw
      rw [← Math.PMFProduct.pmfPi_bind_update_pure,
        ← Math.PMFProduct.pmfPi_bind_update_pure]
      simp only [PMF.map_bind, PMF.pure_map]
      apply Math.ProbabilityMassFunction.bind_congr_on_support
      intro times htimes
      congr 1
      apply quittingFirstStoppingOutcome_update_atomGapRepresentative
      intro player hplayer atom hatom
      apply hcalendar player hplayer atom
      intro hzero
      apply htimes
      rw [Math.PMFProduct.pmfPi_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ player) (hatom ▸ hzero)

/-- The unrestricted behavioral deviation cap is attained on the concrete
finite atom-gap reply menu. -/
theorem exists_mem_quittingFiniteOpponentAtomGapReplyMenu_payoff_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (who : ι) (calendar : Finset ℕ)
    (hcalendar : ∀ player, player ≠ who → ∀ time,
      laws player (some time) ≠ 0 → time ∈ calendar) :
    ∃ representative ∈ quittingFiniteOpponentAtomGapReplyMenu calendar,
      quittingTerminalPayoff reward
          (Function.update (quittingStoppingLawProfile reward laws) who
            (quittingPureTimeBehaviorStrategy reward who representative)) who =
        quittingBehaviorDeviationPayoffCap reward
          (quittingStoppingLawProfile reward laws) who := by
  let profile := quittingStoppingLawProfile reward laws
  let value := fun choice : Option ℕ => quittingTerminalPayoff reward
    (Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who choice)) who
  let menu := quittingFiniteOpponentAtomGapReplyMenu calendar
  have hmenu : menu.Nonempty := by
    exact ⟨none, by simp [menu, quittingFiniteOpponentAtomGapReplyMenu]⟩
  obtain ⟨representative, hrepresentative, hmax⟩ :=
    Finset.exists_max_image menu value hmenu
  refine ⟨representative, hrepresentative, ?_⟩
  rw [quittingBehaviorDeviationPayoffCap_eq_pureTime]
  unfold quittingBehaviorPureTimePayoffCap quittingBehaviorPureTimePayoff
  change value representative = sSup (Set.range value)
  apply le_antisymm
  · apply le_csSup
    · refine (bddAbove_range_quittingTerminalPayoff_update
        reward profile who).mono ?_
      rintro _ ⟨choice, rfl⟩
      exact ⟨quittingPureTimeBehaviorStrategy reward who choice, rfl⟩
    · exact ⟨representative, rfl⟩
  · apply csSup_le (Set.range_nonempty value)
    rintro _ ⟨choice, rfl⟩
    obtain ⟨candidate, hcandidate, heq⟩ :=
      exists_mem_quittingFiniteOpponentAtomGapReplyMenu_payoff_eq
        reward laws who calendar hcalendar choice
    change value choice = value candidate at heq
    rw [heq]
    exact hmax candidate hcandidate

/-- For an arbitrary actual behavior profile, finite opponent clock atoms
make the complete behavioral cap attainable by a pure reply in the same
concrete atom-gap menu. -/
theorem exists_mem_quittingFiniteOpponentAtomGapReplyMenu_actual_payoff_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (calendar : Finset ℕ)
    (hcalendar : ∀ player, player ≠ who → ∀ time,
      quittingBehaviorStoppingLaw reward (profile player) (some time) ≠ 0 →
        time ∈ calendar) :
    ∃ representative ∈ quittingFiniteOpponentAtomGapReplyMenu calendar,
      quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who representative)) who =
        quittingBehaviorDeviationPayoffCap reward profile who := by
  let laws := quittingBehaviorStoppingLaws reward profile
  obtain ⟨representative, hrepresentative, hattains⟩ :=
    exists_mem_quittingFiniteOpponentAtomGapReplyMenu_payoff_eq_cap
      reward laws who calendar (by
        intro player hplayer time htime
        exact hcalendar player hplayer time htime)
  refine ⟨representative, hrepresentative, ?_⟩
  let compactProfile := quittingCompactStoppingLawProfile reward
    (quittingCompactStoppingLawsOfProfile reward profile)
  have hprofile : quittingStoppingLawProfile reward laws = compactProfile := by
    funext player
    unfold quittingStoppingLawProfile compactProfile
      quittingCompactStoppingLawProfile quittingCompactStoppingLawsOfProfile laws
      quittingBehaviorStoppingLaws
    congr 1
    exact (CompactStoppingLaw.toPMF_ofPMF _).symm
  rw [hprofile] at hattains
  calc
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who representative)) who =
      quittingTerminalPayoff reward
        (Function.update compactProfile who
          (quittingPureTimeBehaviorStrategy reward who representative)) who :=
        quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile
          reward profile who representative
    _ = quittingBehaviorDeviationPayoffCap reward compactProfile who := hattains
    _ = quittingBehaviorDeviationPayoffCap reward profile who := by
      simpa only [quittingBehaviorDeviationPayoffCap,
        quittingContinuationBestResponseValue] using
          (quittingContinuationBestResponseValue_eq_compactStoppingLawsOfProfile
            reward profile who).symm

end GameTheory
