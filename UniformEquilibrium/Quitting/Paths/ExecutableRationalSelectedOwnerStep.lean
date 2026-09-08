import UniformEquilibrium.Quitting.Paths.ExecutableRationalCapThresholdBlock

/-! # Executable rational selected-owner renewal step

An explicit finite set controls which owners weak exclusion may select and
which owners require strict preemptors.  Both selections and the common
positive preemption floor use only finite rational comparisons.
-/

namespace GameTheory

variable {players : ℕ}

/-- Every rational finite source has a designated owner whose payoff is at
most its singleton reward. -/
def RationalQuittingFiniteWordOwnerExclusionOn
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players)) : Prop :=
  ∀ roots : List (RationalQuittingRoot players), ∃ owner ∈ owners,
    (rationalQuittingFiniteWordSemanticPair reward roots).1 owner ≤
      reward (quittingSingletonTerminal owner) owner

/-- Every designated owner has a strict singleton-column preemptor. -/
def RationalQuittingOwnersStrictPreempted
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players)) : Prop :=
  ∀ owner ∈ owners, ∃ blocker, 0 <
    reward (quittingSingletonTerminal blocker) blocker -
      reward (quittingSingletonTerminal owner) blocker

/-- Executable scan for a designated weak-exclusion owner. -/
def rationalQuittingFiniteWordExcludedOwnerOn
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (roots : List (RationalQuittingRoot players)) : Fin players :=
  Fin.find (fun owner => owner ∈ owners ∧
    (rationalQuittingFiniteWordSemanticPair reward roots).1 owner ≤
      reward (quittingSingletonTerminal owner) owner) (hWE roots)

theorem rationalQuittingFiniteWordExcludedOwnerOn_mem
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (roots : List (RationalQuittingRoot players)) :
    rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots ∈ owners := by
  exact (Fin.find_spec (hWE roots)).1

theorem rationalQuittingFiniteWordExcludedOwnerOn_payoff_le
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (roots : List (RationalQuittingRoot players)) :
    (rationalQuittingFiniteWordSemanticPair reward roots).1
        (rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots) ≤
      reward (quittingSingletonTerminal
        (rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots))
        (rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots) := by
  exact (Fin.find_spec (hWE roots)).2

/-- The singleton-column preemption gap produced by a candidate blocker. -/
def rationalQuittingOwnerPreemptionGap
    (reward : RationalQuittingReward players)
    (owner blocker : Fin players) : ℚ :=
  reward (quittingSingletonTerminal blocker) blocker -
    reward (quittingSingletonTerminal owner) blocker

private theorem exists_rationalQuittingMaximumGapBlocker
    (reward : RationalQuittingReward players) (owner : Fin players) :
    ∃ blocker, ∀ candidate,
      rationalQuittingOwnerPreemptionGap reward owner candidate ≤
        rationalQuittingOwnerPreemptionGap reward owner blocker := by
  obtain ⟨blocker, -, hmaximal⟩ := Finset.exists_max_image Finset.univ
    (rationalQuittingOwnerPreemptionGap reward owner)
    ⟨owner, Finset.mem_univ owner⟩
  exact ⟨blocker, fun candidate => hmaximal candidate (Finset.mem_univ candidate)⟩

/-- Executable maximum-gap blocker scan for any supplied owner. -/
def rationalQuittingSelectedOwnerBlocker
    (reward : RationalQuittingReward players)
    (owner : Fin players) : Fin players :=
  Fin.find (fun blocker => ∀ candidate,
    rationalQuittingOwnerPreemptionGap reward owner candidate ≤
      rationalQuittingOwnerPreemptionGap reward owner blocker)
    (exists_rationalQuittingMaximumGapBlocker reward owner)

theorem rationalQuittingSelectedOwnerBlocker_maximizes
    (reward : RationalQuittingReward players)
    (owner candidate : Fin players) :
    rationalQuittingOwnerPreemptionGap reward owner candidate ≤
      rationalQuittingOwnerPreemptionGap reward owner
        (rationalQuittingSelectedOwnerBlocker reward owner) := by
  exact Fin.find_spec
    (exists_rationalQuittingMaximumGapBlocker reward owner) candidate

theorem rationalQuittingSelectedOwnerBlocker_spec
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (owner : Fin players) (howner : owner ∈ owners) :
    0 < reward (quittingSingletonTerminal
          (rationalQuittingSelectedOwnerBlocker reward owner))
        (rationalQuittingSelectedOwnerBlocker reward owner) -
      reward (quittingSingletonTerminal owner)
        (rationalQuittingSelectedOwnerBlocker reward owner) := by
  obtain ⟨blocker, hpositive⟩ := hpreempted owner howner
  exact hpositive.trans_le
    (rationalQuittingSelectedOwnerBlocker_maximizes reward owner blocker)

/-- The maximum singleton-column gap for one owner. -/
def rationalQuittingOwnerMaximumPreemptionGap
    (reward : RationalQuittingReward players) (owner : Fin players) : ℚ :=
  let gaps := Finset.univ.image
    (rationalQuittingOwnerPreemptionGap reward owner)
  gaps.max' (Finset.image_nonempty.mpr ⟨owner, Finset.mem_univ owner⟩)

theorem rationalQuittingSelectedOwnerBlocker_gap_eq_maximum
    (reward : RationalQuittingReward players) (owner : Fin players) :
    rationalQuittingOwnerPreemptionGap reward owner
        (rationalQuittingSelectedOwnerBlocker reward owner) =
      rationalQuittingOwnerMaximumPreemptionGap reward owner := by
  unfold rationalQuittingOwnerMaximumPreemptionGap
  apply le_antisymm
  · apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨
      rationalQuittingSelectedOwnerBlocker reward owner,
      Finset.mem_univ _, rfl⟩
  · apply Finset.max'_le
    intro gap hgap
    obtain ⟨candidate, -, rfl⟩ := Finset.mem_image.mp hgap
    exact rationalQuittingSelectedOwnerBlocker_maximizes reward owner candidate

/-- The rational gap attached to the executable blocker of one owner. -/
def rationalQuittingSelectedOwnerGap
    (reward : RationalQuittingReward players)
    (owner : Fin players) : ℚ :=
  reward (quittingSingletonTerminal
      (rationalQuittingSelectedOwnerBlocker reward owner))
    (rationalQuittingSelectedOwnerBlocker reward owner) -
  reward (quittingSingletonTerminal owner)
    (rationalQuittingSelectedOwnerBlocker reward owner)

theorem rationalQuittingSelectedOwnerGap_eq_maximum
    (reward : RationalQuittingReward players) (owner : Fin players) :
    rationalQuittingSelectedOwnerGap reward owner =
      rationalQuittingOwnerMaximumPreemptionGap reward owner := by
  exact rationalQuittingSelectedOwnerBlocker_gap_eq_maximum reward owner

/-- One fixed rational floor for all designated-owner preemption
gaps. -/
def rationalQuittingSelectedOwnerPreemptionFloor
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners) : ℚ :=
  let gaps := owners.image
    (rationalQuittingOwnerMaximumPreemptionGap reward)
  gaps.min' (by
    obtain ⟨owner, howner, -⟩ := hWE []
    exact Finset.image_nonempty.mpr ⟨owner, howner⟩)

theorem rationalQuittingSelectedOwnerPreemptionFloor_pos
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners) :
    0 < rationalQuittingSelectedOwnerPreemptionFloor
      reward owners hWE := by
  let gaps := owners.image
    (rationalQuittingOwnerMaximumPreemptionGap reward)
  let hnonempty : gaps.Nonempty := by
    obtain ⟨owner, howner, -⟩ := hWE []
    exact Finset.image_nonempty.mpr ⟨owner, howner⟩
  have hmem := Finset.min'_mem gaps hnonempty
  rw [Finset.mem_image] at hmem
  obtain ⟨owner, howner, hgap⟩ := hmem
  change 0 < gaps.min' hnonempty
  rw [← hgap]
  rw [← rationalQuittingSelectedOwnerGap_eq_maximum]
  exact rationalQuittingSelectedOwnerBlocker_spec
      reward owners hpreempted owner howner

theorem rationalQuittingSelectedOwnerPreemptionFloor_le
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (owner : Fin players) (howner : owner ∈ owners) :
    rationalQuittingSelectedOwnerPreemptionFloor reward owners hWE ≤
      rationalQuittingSelectedOwnerGap reward owner := by
  rw [rationalQuittingSelectedOwnerGap_eq_maximum]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨owner, howner, rfl⟩

/-- The common floor is literally the minimum over designated owners of their
maximum blocker gaps, as in the quantitative packet. -/
theorem rationalQuittingSelectedOwnerPreemptionFloor_eq_minimumMaximum
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners) :
    rationalQuittingSelectedOwnerPreemptionFloor reward owners hWE =
      let maximumGaps := owners.image
        (rationalQuittingOwnerMaximumPreemptionGap reward)
      maximumGaps.min' (by
        obtain ⟨owner, howner, -⟩ := hWE []
        exact Finset.image_nonempty.mpr ⟨owner, howner⟩) := by
  rfl

private theorem rationalFiniteWord_coordinateDebt_nonneg_on
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (who : Fin players) :
    0 ≤ (rationalQuittingFiniteWordSemanticPair reward roots).2 who -
      (rationalQuittingFiniteWordSemanticPair reward roots).1 who := by
  let profile := quittingLiteralRootStackProfile
    (rationalQuittingRewardToReal reward)
    (roots.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  have hpair := quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward roots
  have hnonnegative := quittingTerminalSemanticDebt_nonneg_of_attainable
    (rationalQuittingRewardToReal reward) ⟨profile, rfl⟩ who
  rw [hpair] at hnonnegative
  simp only [quittingTerminalSemanticDebt] at hnonnegative
  exact_mod_cast hnonnegative

private theorem rationalFiniteWord_selectedOwnerMargin_le_debt_on
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (owner : Fin players)
    (howner : (rationalQuittingFiniteWordSemanticPair reward roots).1 owner ≤
      reward (quittingSingletonTerminal owner) owner) :
    (rationalQuittingFiniteWordSemanticPair reward roots).2 owner -
        reward (quittingSingletonTerminal owner) owner ≤
      rationalFiniteSourceDebt reward roots := by
  let pair := rationalQuittingFiniteWordSemanticPair reward roots
  have hcoordinate : pair.2 owner - pair.1 owner ≤
      rationalQuittingSemanticDebtSum pair := by
    rw [rationalQuittingSemanticDebtSum]
    exact Finset.single_le_sum
      (fun player _ => rationalFiniteWord_coordinateDebt_nonneg_on reward roots player)
      (Finset.mem_univ owner)
  change pair.2 owner - reward (quittingSingletonTerminal owner) owner ≤ _
  calc
    _ ≤ pair.2 owner - pair.1 owner := sub_le_sub_left howner _
    _ ≤ _ := hcoordinate

/-- One executable rational selected-owner renewal block. -/
def executableRationalSelectedOwnerDebtBlock
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (roots : List (RationalQuittingRoot players))
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    List (RationalQuittingRoot players) :=
  if hpositive : 0 < rationalFiniteSourceDebt reward roots then
    let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots
    let blocker := rationalQuittingSelectedOwnerBlocker reward owner
    executableRationalCapThresholdBlock reward roots owner blocker M hM hreward
      hpositive (rationalQuittingSelectedOwnerBlocker_spec reward owners hpreempted
        owner (rationalQuittingFiniteWordExcludedOwnerOn_mem reward owners hWE roots))
  else []

/-- The selected block retains its literal row bound, with a fixed common
preemption floor available independently of the target accuracy. -/
theorem executableRationalSelectedOwnerDebtBlock_length_le
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (roots : List (RationalQuittingRoot players))
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < rationalFiniteSourceDebt reward roots) :
    (executableRationalSelectedOwnerDebtBlock
        reward owners hWE hpreempted roots M hM hreward).length ≤
      1 + quittingSoloCapThresholdHorizon (M : ℝ)
        ((rationalFiniteSourceDebt reward roots /
          (32 * (M + rationalFiniteSourceDebt reward roots)) : ℚ) : ℝ)
        ((rationalQuittingSelectedOwnerGap reward
          (rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots) : ℚ) : ℝ) := by
  let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots
  let blocker := rationalQuittingSelectedOwnerBlocker reward owner
  have howner := rationalQuittingFiniteWordExcludedOwnerOn_payoff_le
    reward owners hWE roots
  have hmargin := rationalFiniteWord_selectedOwnerMargin_le_debt_on
    reward roots owner howner
  have hscale : rationalFiniteSourceCapThresholdScale reward roots owner =
      rationalFiniteSourceDebt reward roots := max_eq_left hmargin
  have hblock :=
    (executableRationalCapThresholdBlock_length_and_debtSum_le
      reward roots owner blocker M hM hreward hpositive
        (rationalQuittingSelectedOwnerBlocker_spec reward owners hpreempted
          owner (rationalQuittingFiniteWordExcludedOwnerOn_mem
            reward owners hWE roots))).1
  rw [hscale] at hblock
  rw [executableRationalSelectedOwnerDebtBlock, dif_pos hpositive]
  exact hblock

/-- At positive debt the selected block satisfies the packet's rational
quarter-quadratic debt recurrence. -/
theorem executableRationalSelectedOwnerDebtBlock_debtSum_le
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (roots : List (RationalQuittingRoot players))
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < rationalFiniteSourceDebt reward roots) :
    rationalFiniteSourceDebt reward
        (executableRationalSelectedOwnerDebtBlock
          reward owners hWE hpreempted roots M hM hreward ++ roots) ≤
      rationalFiniteSourceDebt reward roots -
        3 * rationalFiniteSourceDebt reward roots ^ 2 /
          (128 * M + 24 * rationalFiniteSourceDebt reward roots) := by
  let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots
  let blocker := rationalQuittingSelectedOwnerBlocker reward owner
  have howner := rationalQuittingFiniteWordExcludedOwnerOn_payoff_le
    reward owners hWE roots
  have hmargin := rationalFiniteWord_selectedOwnerMargin_le_debt_on
    reward roots owner howner
  have hscale : rationalFiniteSourceCapThresholdScale reward roots owner =
      rationalFiniteSourceDebt reward roots := max_eq_left hmargin
  have hblock :=
    (executableRationalCapThresholdBlock_length_and_debtSum_le
      reward roots owner blocker M hM hreward hpositive
        (rationalQuittingSelectedOwnerBlocker_spec reward owners hpreempted
          owner (rationalQuittingFiniteWordExcludedOwnerOn_mem
            reward owners hWE roots))).2
  rw [hscale] at hblock
  rw [executableRationalSelectedOwnerDebtBlock, dif_pos hpositive]
  change rationalQuittingSemanticDebtSum
      (rationalQuittingFiniteWordSemanticPair reward
        (executableRationalCapThresholdBlock reward roots owner blocker M hM hreward
          hpositive (rationalQuittingSelectedOwnerBlocker_spec
            reward owners hpreempted owner
              (rationalQuittingFiniteWordExcludedOwnerOn_mem
                reward owners hWE roots)) ++ roots)) ≤ _
  have hblock' :
      ((rationalFiniteSourceDebt reward
        (executableRationalCapThresholdBlock reward roots owner blocker M hM hreward
          hpositive (rationalQuittingSelectedOwnerBlocker_spec
            reward owners hpreempted owner
              (rationalQuittingFiniteWordExcludedOwnerOn_mem
                reward owners hWE roots)) ++ roots) : ℚ) : ℝ) ≤
        ((rationalFiniteSourceDebt reward roots -
          3 * rationalFiniteSourceDebt reward roots ^ 2 /
            (128 * M + 24 * rationalFiniteSourceDebt reward roots) : ℚ) : ℝ) := by
    rw [rationalFiniteSourceDebt,
      ← quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast]
    simpa only [List.map_append, quittingLiteralRootStackProfile_append] using hblock
  exact_mod_cast hblock'

end GameTheory
