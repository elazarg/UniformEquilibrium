import UniformEquilibrium.Quitting.Paths.SparseWholePayoffFiniteStoppingLaw
import UniformEquilibrium.Quitting.Paths.CommonStoppingCalendarRetiming
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance

/-! # Whole-payoff compression of finite independent stopping profiles -/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sparse replacement selected for one player's current finite stopping
law. Its atoms remain literal choices from that law. -/
def quittingSparseFiniteStoppingLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (mixer : ι) :
    FinDist (Option ℕ) :=
  (Classical.choose
    (exists_sparseFiniteStoppingLaw_wholePayoff_eq reward laws mixer)).map
      Subtype.val

/-- Replace current player laws successively, always sparsifying against the
opponents produced by the preceding replacements. -/
def quittingSparseFiniteStoppingLawsAlong
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    List ι → (ι → FinDist (Option ℕ)) → ι → FinDist (Option ℕ)
  | [], laws => laws
  | mixer :: rest, laws => quittingSparseFiniteStoppingLawsAlong reward rest
      (Function.update laws mixer
        (quittingSparseFiniteStoppingLaw reward laws mixer))

theorem quittingSparseFiniteStoppingLaw_wholePayoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (mixer observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (Function.update
          (fun who => (laws who).toPMF) mixer
          (quittingSparseFiniteStoppingLaw reward laws mixer).toPMF)) observer =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (fun who => (laws who).toPMF)) observer := by
  exact (Classical.choose_spec
    (exists_sparseFiniteStoppingLaw_wholePayoff_eq reward laws mixer)).2 observer

theorem card_support_quittingSparseFiniteStoppingLaw_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (mixer : ι) :
    (quittingSparseFiniteStoppingLaw reward laws mixer).supportFinset.card ≤
      Fintype.card ι + 1 := by
  let sparse := Classical.choose
    (exists_sparseFiniteStoppingLaw_wholePayoff_eq reward laws mixer)
  have hcard := (Classical.choose_spec
    (exists_sparseFiniteStoppingLaw_wholePayoff_eq reward laws mixer)).1
  have hsupport : (quittingSparseFiniteStoppingLaw reward laws mixer).supportFinset =
      sparse.supportFinset.image Subtype.val := by
    ext choice
    simp [quittingSparseFiniteStoppingLaw, sparse,
      FinDist.mem_supportFinset, FinDist.support_map]
  rw [hsupport]
  refine (Finset.card_image_le.trans ?_)
  let supportEquiv : {choice // choice ∈ sparse.supportFinset} ≃
      {choice // sparse.prob choice ≠ 0} :=
    Equiv.subtypeEquivRight fun choice => by
      rw [FinDist.mem_supportFinset]
      constructor
      · exact fun hmem => (FinDist.prob_pos_iff.mpr hmem).ne'
      · intro hne
        exact FinDist.prob_pos_iff.mp <|
          lt_of_le_of_ne (sparse.prob_nonneg choice) (Ne.symm hne)
  rw [← Fintype.card_coe]
  exact (Fintype.card_congr supportEquiv).trans_le hcard

theorem quittingSparseFiniteStoppingLawsAlong_of_not_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : List ι) (laws : ι → FinDist (Option ℕ)) {who : ι}
    (hwho : who ∉ players) :
    quittingSparseFiniteStoppingLawsAlong reward players laws who = laws who := by
  induction players generalizing laws with
  | nil => rfl
  | cons mixer rest ih =>
      simp only [List.mem_cons, not_or] at hwho
      rw [quittingSparseFiniteStoppingLawsAlong, ih _ hwho.2]
      simp [Function.update_of_ne hwho.1]

theorem card_support_quittingSparseFiniteStoppingLawsAlong_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : List ι) (laws : ι → FinDist (Option ℕ))
    {who : ι} (hwho : who ∈ players) :
    (quittingSparseFiniteStoppingLawsAlong reward players laws who).supportFinset.card ≤
      Fintype.card ι + 1 := by
  induction players generalizing laws with
  | nil => simp at hwho
  | cons mixer rest ih =>
      rw [List.mem_cons] at hwho
      rcases hwho with rfl | hrest
      · by_cases hin : who ∈ rest
        · rw [quittingSparseFiniteStoppingLawsAlong]
          exact ih _ hin
        · rw [quittingSparseFiniteStoppingLawsAlong,
            quittingSparseFiniteStoppingLawsAlong_of_not_mem reward rest _ hin]
          simpa using card_support_quittingSparseFiniteStoppingLaw_le
            reward laws who
      · rw [quittingSparseFiniteStoppingLawsAlong]
        exact ih _ hrest

/-- Successive current-opponent sparse replacements preserve the complete
prescribed payoff vector. -/
theorem quittingSparseFiniteStoppingLawsAlong_wholePayoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : List ι) (laws : ι → FinDist (Option ℕ)) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (fun who =>
          (quittingSparseFiniteStoppingLawsAlong reward players laws who).toPMF))
        observer =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (fun who => (laws who).toPMF))
        observer := by
  induction players generalizing laws with
  | nil => rfl
  | cons mixer rest ih =>
      rw [quittingSparseFiniteStoppingLawsAlong]
      apply (ih _).trans
      have hlaws : (fun who => (Function.update laws mixer
          (quittingSparseFiniteStoppingLaw reward laws mixer) who).toPMF) =
          Function.update (fun who => (laws who).toPMF) mixer
            (quittingSparseFiniteStoppingLaw reward laws mixer).toPMF := by
        funext who
        by_cases hwho : who = mixer <;> simp [hwho]
      rw [hlaws]
      exact quittingSparseFiniteStoppingLaw_wholePayoff_eq
        reward laws mixer observer

/-- Sparsify every player's current law once. -/
def quittingSparseFiniteStoppingLaws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) : ι → FinDist (Option ℕ) :=
  quittingSparseFiniteStoppingLawsAlong reward Finset.univ.toList laws

theorem card_support_quittingSparseFiniteStoppingLaws_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (who : ι) :
    (quittingSparseFiniteStoppingLaws reward laws who).supportFinset.card ≤
      Fintype.card ι + 1 := by
  apply card_support_quittingSparseFiniteStoppingLawsAlong_le
  simp

theorem quittingSparseFiniteStoppingLaws_wholePayoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (fun who =>
          (quittingSparseFiniteStoppingLaws reward laws who).toPMF)) observer =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (fun who => (laws who).toPMF))
        observer := by
  exact quittingSparseFiniteStoppingLawsAlong_wholePayoff_eq
    reward Finset.univ.toList laws observer

/-- The payoff-preserving sparse laws, retimed onto one common consecutive
finite calendar. -/
def quittingFiniteCalendarPayoffLaws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) : ι → FinDist (Option ℕ) :=
  let sparse := quittingSparseFiniteStoppingLaws reward laws
  let calendar := quittingFiniteStoppingCalendar sparse
  fun who => (sparse who).map (quittingFiniteCalendarRetiming calendar)

theorem quittingFiniteCalendarPayoffLaws_wholePayoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (fun who =>
          (quittingFiniteCalendarPayoffLaws reward laws who).toPMF)) observer =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (fun who => (laws who).toPMF))
        observer := by
  letI : Nonempty ι := ⟨observer⟩
  let sparse := quittingSparseFiniteStoppingLaws reward laws
  let calendar := quittingFiniteStoppingCalendar sparse
  have houtcome :=
    quittingIndependentTerminalOutcomeLaw_finiteCalendarRetiming_eq sparse
  rw [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff]
  change Math.Probability.expect _ _ = Math.Probability.expect _ _
  rw [show (fun who =>
      (quittingFiniteCalendarPayoffLaws reward laws who).toPMF) =
      fun who => (sparse who).toPMF.map
        (quittingFiniteCalendarRetiming calendar) by rfl]
  rw [houtcome]
  change quittingStoppingLawExpectedPayoff reward
      (fun who => (sparse who).toPMF) observer =
    quittingStoppingLawExpectedPayoff reward
      (fun who => (laws who).toPMF) observer
  rw [← quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    ← quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff]
  exact quittingSparseFiniteStoppingLaws_wholePayoff_eq reward laws observer

theorem quittingFiniteCalendarPayoffLaws_finiteDate_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (who : ι) {time : ℕ}
    (htime : some time ∈
      (quittingFiniteCalendarPayoffLaws reward laws who).support) :
    time < Fintype.card ι * (Fintype.card ι + 1) := by
  letI : Nonempty ι := ⟨who⟩
  let sparse := quittingSparseFiniteStoppingLaws reward laws
  let calendar := quittingFiniteStoppingCalendar sparse
  have hdate : time < calendar.card := by
    apply finiteCalendarRetiming_support_lt_card sparse who
    exact htime
  apply hdate.trans_le
  apply card_quittingFiniteStoppingCalendar_le
  exact card_support_quittingSparseFiniteStoppingLaws_le reward laws

theorem card_support_quittingFiniteCalendarPayoffLaws_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (who : ι) :
    (quittingFiniteCalendarPayoffLaws reward laws who).supportFinset.card ≤
      Fintype.card ι + 1 := by
  let sparse := quittingSparseFiniteStoppingLaws reward laws
  let calendar := quittingFiniteStoppingCalendar sparse
  have hsupport :
      (quittingFiniteCalendarPayoffLaws reward laws who).supportFinset =
        (sparse who).supportFinset.image
          (quittingFiniteCalendarRetiming calendar) := by
    ext choice
    simp [quittingFiniteCalendarPayoffLaws, sparse, calendar,
      FinDist.mem_supportFinset, FinDist.support_map]
  rw [hsupport]
  exact Finset.card_image_le.trans
    (card_support_quittingSparseFiniteStoppingLaws_le reward laws who)

end GameTheory
