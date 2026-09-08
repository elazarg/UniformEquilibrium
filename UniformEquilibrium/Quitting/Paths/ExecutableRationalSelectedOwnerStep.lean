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

/-- Total executable blocker scan, using an excluded owner as harmless fallback
outside the designated owner set. -/
def rationalQuittingSelectedOwnerBlocker
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (owner : Fin players) : Fin players :=
  if howner : owner ∈ owners then
    Fin.find (fun blocker => 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker)
      (hpreempted owner howner)
  else rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE []

theorem rationalQuittingSelectedOwnerBlocker_spec
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (owner : Fin players) (howner : owner ∈ owners) :
    0 < reward (quittingSingletonTerminal
          (rationalQuittingSelectedOwnerBlocker
            reward owners hWE hpreempted owner))
        (rationalQuittingSelectedOwnerBlocker reward owners hWE hpreempted owner) -
      reward (quittingSingletonTerminal owner)
        (rationalQuittingSelectedOwnerBlocker
          reward owners hWE hpreempted owner) := by
  rw [rationalQuittingSelectedOwnerBlocker, dif_pos howner]
  exact Fin.find_spec (hpreempted owner howner)

/-- The rational gap attached to the executable blocker of one owner. -/
def rationalQuittingSelectedOwnerGap
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (owner : Fin players) : ℚ :=
  reward (quittingSingletonTerminal
      (rationalQuittingSelectedOwnerBlocker reward owners hWE hpreempted owner))
    (rationalQuittingSelectedOwnerBlocker reward owners hWE hpreempted owner) -
  reward (quittingSingletonTerminal owner)
    (rationalQuittingSelectedOwnerBlocker reward owners hWE hpreempted owner)

/-- One fixed positive rational floor for all designated-owner preemption
gaps. -/
def rationalQuittingSelectedOwnerPreemptionFloor
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners) : ℚ :=
  let gaps := owners.image
    (rationalQuittingSelectedOwnerGap reward owners hWE hpreempted)
  gaps.min' (by
    obtain ⟨owner, howner, -⟩ := hWE []
    exact Finset.image_nonempty.mpr ⟨owner, howner⟩)

theorem rationalQuittingSelectedOwnerPreemptionFloor_pos
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners) :
    0 < rationalQuittingSelectedOwnerPreemptionFloor
      reward owners hWE hpreempted := by
  let gaps := owners.image
    (rationalQuittingSelectedOwnerGap reward owners hWE hpreempted)
  let hnonempty : gaps.Nonempty := by
    obtain ⟨owner, howner, -⟩ := hWE []
    exact Finset.image_nonempty.mpr ⟨owner, howner⟩
  have hmem := Finset.min'_mem gaps hnonempty
  rw [Finset.mem_image] at hmem
  obtain ⟨owner, howner, hgap⟩ := hmem
  change 0 < gaps.min' hnonempty
  rw [← hgap]
  exact rationalQuittingSelectedOwnerBlocker_spec
    reward owners hWE hpreempted owner howner

theorem rationalQuittingSelectedOwnerPreemptionFloor_le
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (owner : Fin players) (howner : owner ∈ owners) :
    rationalQuittingSelectedOwnerPreemptionFloor reward owners hWE hpreempted ≤
      rationalQuittingSelectedOwnerGap reward owners hWE hpreempted owner := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨owner, howner, rfl⟩

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
    let blocker := rationalQuittingSelectedOwnerBlocker
      reward owners hWE hpreempted owner
    executableRationalCapThresholdBlock reward roots owner blocker M hM hreward
      hpositive (rationalQuittingSelectedOwnerBlocker_spec reward owners hWE hpreempted
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
        ((rationalQuittingSelectedOwnerGap reward owners hWE hpreempted
          (rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots) : ℚ) : ℝ) := by
  let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots
  let blocker := rationalQuittingSelectedOwnerBlocker reward owners hWE hpreempted owner
  have howner := rationalQuittingFiniteWordExcludedOwnerOn_payoff_le
    reward owners hWE roots
  have hmargin := rationalFiniteWord_selectedOwnerMargin_le_debt_on
    reward roots owner howner
  have hscale : rationalFiniteSourceCapThresholdScale reward roots owner =
      rationalFiniteSourceDebt reward roots := max_eq_left hmargin
  have hblock :=
    (executableRationalCapThresholdBlock_length_and_debtSum_le
      reward roots owner blocker M hM hreward hpositive
        (rationalQuittingSelectedOwnerBlocker_spec reward owners hWE hpreempted
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
  let blocker := rationalQuittingSelectedOwnerBlocker reward owners hWE hpreempted owner
  have howner := rationalQuittingFiniteWordExcludedOwnerOn_payoff_le
    reward owners hWE roots
  have hmargin := rationalFiniteWord_selectedOwnerMargin_le_debt_on
    reward roots owner howner
  have hscale : rationalFiniteSourceCapThresholdScale reward roots owner =
      rationalFiniteSourceDebt reward roots := max_eq_left hmargin
  have hblock :=
    (executableRationalCapThresholdBlock_length_and_debtSum_le
      reward roots owner blocker M hM hreward hpositive
        (rationalQuittingSelectedOwnerBlocker_spec reward owners hWE hpreempted
          owner (rationalQuittingFiniteWordExcludedOwnerOn_mem
            reward owners hWE roots))).2
  rw [hscale] at hblock
  rw [executableRationalSelectedOwnerDebtBlock, dif_pos hpositive]
  change rationalQuittingSemanticDebtSum
      (rationalQuittingFiniteWordSemanticPair reward
        (executableRationalCapThresholdBlock reward roots owner blocker M hM hreward
          hpositive (rationalQuittingSelectedOwnerBlocker_spec
            reward owners hWE hpreempted owner
              (rationalQuittingFiniteWordExcludedOwnerOn_mem
                reward owners hWE roots)) ++ roots)) ≤ _
  have hblock' :
      ((rationalFiniteSourceDebt reward
        (executableRationalCapThresholdBlock reward roots owner blocker M hM hreward
          hpositive (rationalQuittingSelectedOwnerBlocker_spec
            reward owners hWE hpreempted owner
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
