import UniformEquilibrium.Quitting.Paths.PureTimeDeadlineProfile

/-!
# First finite deadlines in canonical pure-time profiles
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A nonempty finite deadline support has a first displayed date, with a
nonempty coalition there and no earlier displayed coalition. -/
theorem exists_quittingPureTime_firstDeadline
    (times : QuittingPureTimeProfile ι)
    (hsupport : (quittingPureTimeDeadlineSupport times).Nonempty) :
    ∃ deadline,
      (quittingPureTimeCoalitionAt times deadline).Nonempty ∧
      ∀ time < deadline, quittingPureTimeCoalitionAt times time = ∅ := by
  let deadline := (quittingPureTimeDeadlineSupport times).min' hsupport
  have hdeadlineMem : deadline ∈ quittingPureTimeDeadlineSupport times :=
    Finset.min'_mem _ hsupport
  have hcoalition : (quittingPureTimeCoalitionAt times deadline).Nonempty := by
    obtain ⟨who, hwho⟩ :=
      (mem_quittingPureTimeDeadlineSupport_iff times deadline).1 hdeadlineMem
    exact ⟨who, by simp [quittingPureTimeCoalitionAt, hwho]⟩
  refine ⟨deadline, hcoalition, ?_⟩
  intro time htime
  by_contra hne
  have hnonempty : (quittingPureTimeCoalitionAt times time).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨who, hwhoMem⟩ := hnonempty
  have hwho : times who = some time := by
    simpa [quittingPureTimeCoalitionAt] using hwhoMem
  have htimeMem : time ∈ quittingPureTimeDeadlineSupport times :=
    (mem_quittingPureTimeDeadlineSupport_iff times time).2 ⟨who, hwho⟩
  exact (not_le_of_gt htime)
    (Finset.min'_le (quittingPureTimeDeadlineSupport times) time htimeMem)

/-- A nonempty opponent deadline support has a first opponent date, with a
nonempty opponent coalition there and none earlier. -/
theorem exists_quittingPureTime_firstOpponentDeadline
    (times : QuittingPureTimeProfile ι) (owner : ι)
    (hsupport : (quittingPureTimeOpponentDeadlineSupport times owner).Nonempty) :
    ∃ deadline,
      (quittingPureTimeOpponentCoalitionAt times owner deadline).Nonempty ∧
      ∀ time < deadline,
        quittingPureTimeOpponentCoalitionAt times owner time = ∅ := by
  let deadline :=
    (quittingPureTimeOpponentDeadlineSupport times owner).min' hsupport
  have hdeadlineMem :
      deadline ∈ quittingPureTimeOpponentDeadlineSupport times owner :=
    Finset.min'_mem _ hsupport
  obtain ⟨other, hotherNe, hotherTime⟩ :=
    (mem_quittingPureTimeOpponentDeadlineSupport_iff times owner deadline).1
      hdeadlineMem
  have hcoalition :
      (quittingPureTimeOpponentCoalitionAt times owner deadline).Nonempty := by
    refine ⟨other, Finset.mem_erase.mpr ⟨hotherNe, ?_⟩⟩
    simp [quittingPureTimeCoalitionAt, hotherTime]
  refine ⟨deadline, hcoalition, ?_⟩
  intro time htime
  by_contra hne
  have hnonempty :
      (quittingPureTimeOpponentCoalitionAt times owner time).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨other, hotherMem⟩ := hnonempty
  have hotherNe : other ≠ owner := (Finset.mem_erase.mp hotherMem).1
  have hotherTime : times other = some time := by
    simpa [quittingPureTimeCoalitionAt] using (Finset.mem_erase.mp hotherMem).2
  have htimeMem : time ∈ quittingPureTimeOpponentDeadlineSupport times owner :=
    (mem_quittingPureTimeOpponentDeadlineSupport_iff times owner time).2
      ⟨other, hotherNe, hotherTime⟩
  exact (not_le_of_gt htime)
    (Finset.min'_le
      (quittingPureTimeOpponentDeadlineSupport times owner) time htimeMem)

end GameTheory
