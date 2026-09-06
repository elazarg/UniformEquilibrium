import UniformEquilibrium.Quitting.Paths.ActualExactPrefixBlock
import UniformEquilibrium.Quitting.Paths.SummableRootSurvival
import UniformEquilibrium.Quitting.Root.ExactCapClockTransport
import UniformEquilibrium.Quitting.Root.PureTimeCapChild
import UniformEquilibrium.Quitting.Root.TerminalGapPrefixDebtorTransport

/-!
# Nested terminal cap children and one fixed transported debtor

The literal cap-child genealogy and the fixed outsider
response are transported through every later child. The source profiles and
roots remain the supplied actual objects.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The displayed root with the cap owner forced to Continue. -/
def quittingForcedOwnerContinueRoot
    (roots : ℕ → ι → PMF Bool) (owner : ι) (depth : ℕ) : ι → PMF Bool :=
  Function.update (roots depth) owner (PMF.pure false)

/-- The barred root's joint survival is exactly the original owner-deleted
mass, and forcing the owner to Continue can only increase survival. -/
theorem quittingForcedOwnerContinueRoot_survival
    (roots : ℕ → ι → PMF Bool) (owner : ι) (depth : ℕ) :
    quittingStationaryContinueMass
          (quittingForcedOwnerContinueRoot roots owner depth) =
        quittingRootOpponentContinueMass (roots depth) owner ∧
      quittingStationaryContinueMass (roots depth) ≤
        quittingStationaryContinueMass
          (quittingForcedOwnerContinueRoot roots owner depth) := by
  exact ⟨rfl, quittingStationaryContinueMass_le_update_pure_false
    (roots depth) owner⟩

omit [DecidableEq ι] in
/-- Survival of a reverse root word is the chronologically indexed product. -/
theorem quittingLiteralRootStackJointSurvival_reversePrefixRootStack
    (roots : ℕ → ι → PMF Bool) (depth : ℕ) :
    quittingLiteralRootStackJointSurvival
        (quittingReversePrefixRootStack roots depth) =
      ∏ time ∈ Finset.range depth,
        quittingStationaryContinueMass (roots time) := by
  induction depth with
  | zero => simp [quittingLiteralRootStackJointSurvival]
  | succ depth ih =>
      rw [quittingReversePrefixRootStack_succ]
      simp only [quittingLiteralRootStackJointSurvival, List.map_cons,
        List.prod_cons, Finset.prod_range_succ]
      change quittingStationaryContinueMass (roots depth) *
          quittingLiteralRootStackJointSurvival
            (quittingReversePrefixRootStack roots depth) = _
      rw [ih]
      ring

/-- Exact source roots transport the initial `Quit0` cap into the literal
actual child sequence.  Each child is a cap replacement, has zero owner debt,
has a sure owner Quit at its displayed date, and nests under the owner-forced
Continue roots. -/
theorem quittingPureTimeCapChild_source_facts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth))
    (hexact : ∀ depth, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles depth) player)
      0 (roots depth))
    (hpositive : ∀ depth, 0 < quittingStationaryContinueMass (roots depth))
    (hbase : quittingTerminalPayoff reward
        (quittingPureTimeCapChild reward (profiles 0) owner 0) owner =
      quittingContinuationBestResponseValue reward (profiles 0) owner) :
    (∀ depth,
      quittingTerminalPayoff reward
          (quittingPureTimeCapChild reward (profiles depth) owner depth) owner =
        quittingContinuationBestResponseValue reward (profiles depth) owner) ∧
      (∀ depth, quittingTerminalDeviationDebt reward
        (quittingPureTimeCapChild reward (profiles depth) owner depth) owner = 0) ∧
      (∀ depth, quittingProfileLiveRoot reward
        (quittingPureTimeCapChild reward (profiles depth) owner depth) depth owner =
          PMF.pure true) ∧
      ∀ depth, quittingPureTimeCapChild reward (profiles (depth + 1)) owner
          (depth + 1) =
        quittingRootThenContinuationProfile reward
          (quittingForcedOwnerContinueRoot roots owner depth)
          (quittingPureTimeCapChild reward (profiles depth) owner depth) := by
  have hactual := quittingReversePrefixProfile_eq_of_nested
    reward profiles roots hnested
  have hclock := quitting_pureTimeCap_literalPrefix_transport
    reward roots (profiles 0) owner (by simpa [quittingPureTimeCapChild] using hbase)
    (fun depth => by rw [hactual depth]; exact hexact depth)
    (fun depth => (hpositive depth).trans_le
      (quittingStationaryContinueMass_le_ownContinueProbability
        (roots depth) owner))
  constructor
  · intro depth
    simpa [quittingPureTimeCapChild, hactual depth] using (hclock depth).1
  constructor
  · intro depth
    apply quittingPureTimeCapChild_ownerDebt_eq_zero
    simpa [quittingPureTimeCapChild, hactual depth] using (hclock depth).1
  constructor
  · intro depth
    exact quittingPureTimeCapChild_sure_owner_at_deadline
      reward (profiles depth) owner depth
  · intro depth
    simpa [quittingPureTimeCapChild, quittingForcedOwnerContinueRoot,
      hactual depth, hactual (depth + 1)] using (hclock depth).2.2

/-- Every complete original prefix survives no more than a later window after
forcing one coordinate to Continue.  This is the finite comparison that lets
one common original-prefix floor control all transported child responses. -/
theorem quittingJointSurvivalPrefix_le_forcedContinueWindow
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) :
    (∏ time ∈ Finset.range (start + fuel),
        quittingStationaryContinueMass (roots time)) ≤
      ∏ offset ∈ Finset.range fuel,
        quittingStationaryContinueMass
          (Function.update (roots (start + offset)) owner (PMF.pure false)) := by
  let initialProduct : ℝ := (∏ time ∈ Finset.range start,
    quittingStationaryContinueMass (roots time))
  let laterProduct : ℝ := (∏ offset ∈ Finset.range fuel,
    quittingStationaryContinueMass (roots (start + offset)))
  have hprefix1 : initialProduct ≤ 1 := Finset.prod_le_one
    (fun time _ => quittingStationaryContinueMass_nonneg (roots time))
    (fun time _ => quittingStationaryContinueMass_le_one (roots time))
  have hwindow0 : 0 ≤ laterProduct := Finset.prod_nonneg fun offset _ =>
    quittingStationaryContinueMass_nonneg (roots (start + offset))
  have hdrop : initialProduct * laterProduct ≤ laterProduct := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hprefix1) hwindow0]
  rw [Finset.prod_range_add]
  exact hdrop.trans <| Finset.prod_le_prod
    (fun offset _ => quittingStationaryContinueMass_nonneg
      (roots (start + offset)))
    (fun offset _ => quittingStationaryContinueMass_le_update_pure_false
      (roots (start + offset)) owner)

/-- The shifted reverse word of forced-Continue roots executes to the literal
later child, rather than merely to a payoff-equivalent supplied tail. -/
theorem quittingForcedContinueReversePrefixProfile_eq_child
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hchildNested : ∀ depth,
      quittingPureTimeCapChild reward (profiles (depth + 1)) owner (depth + 1) =
        quittingRootThenContinuationProfile reward
          (quittingForcedOwnerContinueRoot roots owner depth)
          (quittingPureTimeCapChild reward (profiles depth) owner depth))
    (start fuel : ℕ) :
    quittingLiteralRootStackProfile reward
        (quittingReversePrefixRootStack
          (fun offset => quittingForcedOwnerContinueRoot roots owner
            (start + offset)) fuel)
        (quittingPureTimeCapChild reward (profiles start) owner start) =
      quittingPureTimeCapChild reward (profiles (start + fuel)) owner
        (start + fuel) := by
  let shiftedProfiles := fun offset =>
    quittingPureTimeCapChild reward (profiles (start + offset)) owner
      (start + offset)
  let shiftedRoots := fun offset =>
    quittingForcedOwnerContinueRoot roots owner (start + offset)
  have hshiftNested : ∀ offset, shiftedProfiles (offset + 1) =
      quittingRootThenContinuationProfile reward (shiftedRoots offset)
        (shiftedProfiles offset) := by
    intro offset
    dsimp [shiftedProfiles, shiftedRoots]
    simpa only [Nat.add_assoc] using hchildNested (start + offset)
  have hactual := quittingReversePrefixProfile_eq_of_nested
    reward shiftedProfiles shiftedRoots hshiftNested fuel
  simpa [quittingReversePrefixProfile, shiftedProfiles, shiftedRoots] using hactual

/-- At any fixed child depth, the terminal gap selects one outsider and one
literal pure-time-or-Never cap response.  Copying that same response through
the actual forced-Continue roots gives the exact gain formula at every later
child and preserves one common positive debt floor. -/
theorem HasTerminalExploitabilityGap.exists_fixedOutsiderResponse_for_all_capChildren
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap prefixFloor : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hgap : 0 < gap)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth))
    (hexact : ∀ depth, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles depth) player)
      0 (roots depth))
    (hpositive : ∀ depth, 0 < quittingStationaryContinueMass (roots depth))
    (hbase : quittingTerminalPayoff reward
        (quittingPureTimeCapChild reward (profiles 0) owner 0) owner =
      quittingContinuationBestResponseValue reward (profiles 0) owner)
    (hprefixFloor : ∀ horizon, prefixFloor ≤
      ∏ time ∈ Finset.range horizon,
        quittingStationaryContinueMass (roots time))
    (start : ℕ) :
    ∃ (who : ι) (choice : Option ℕ),
      who ≠ owner ∧
        (choice = none ∨ ∃ time ≤ start, choice = some time) ∧
        quittingTerminalPayoff reward
            (Function.update
              (quittingPureTimeCapChild reward (profiles start) owner start) who
              (quittingPureTimeBehaviorStrategy reward who choice)) who =
          quittingContinuationBestResponseValue reward
            (quittingPureTimeCapChild reward (profiles start) owner start) who ∧
        gap ≤ quittingTerminalDeviationDebt reward
          (quittingPureTimeCapChild reward (profiles start) owner start) who ∧
        ∀ fuel,
          let shiftedRoots := fun offset =>
            quittingForcedOwnerContinueRoot roots owner (start + offset)
          let word := quittingReversePrefixRootStack shiftedRoots fuel
          let response := quittingCopyLiteralRootStackThenDeviation
            reward word who
              (quittingPureTimeBehaviorStrategy reward who choice)
          quittingTerminalPayoff reward
                (Function.update
                  (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
                    (start + fuel))
                  who response) who -
              quittingTerminalPayoff reward
                (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
                  (start + fuel)) who =
            quittingLiteralRootStackJointSurvival word *
              (quittingTerminalPayoff reward
                  (Function.update
                    (quittingPureTimeCapChild reward (profiles start) owner start) who
                    (quittingPureTimeBehaviorStrategy reward who choice)) who -
                quittingTerminalPayoff reward
                  (quittingPureTimeCapChild reward (profiles start) owner start) who) ∧
          prefixFloor * gap ≤
            quittingTerminalDeviationDebt reward
              (quittingPureTimeCapChild reward (profiles (start + fuel)) owner
                (start + fuel)) who := by
  have hfacts := quittingPureTimeCapChild_source_facts
    reward profiles roots owner hnested hexact hpositive hbase
  have hownerDebt := hfacts.2.1 start
  have hsure := hfacts.2.2.1 start
  obtain ⟨who, choice, hwho, hchoice, hcap, hdebt, -, -⟩ :=
    hexploit.exists_outsider_pureTimeCap_with_prefix_debt
      reward (quittingPureTimeCapChild reward (profiles start) owner start)
      owner start (by rw [hownerDebt]; exact hgap) hsure [] 1 (by simp
        [quittingLiteralRootStackJointSurvival])
  refine ⟨who, choice, hwho, hchoice, hcap, hdebt, fun fuel => ?_⟩
  let shiftedRoots := fun offset =>
    quittingForcedOwnerContinueRoot roots owner (start + offset)
  let word := quittingReversePrefixRootStack shiftedRoots fuel
  let baseResponse := quittingPureTimeBehaviorStrategy reward who choice
  let response := quittingCopyLiteralRootStackThenDeviation
    reward word who baseResponse
  have hprofile : quittingLiteralRootStackProfile reward word
        (quittingPureTimeCapChild reward (profiles start) owner start) =
      quittingPureTimeCapChild reward (profiles (start + fuel)) owner
        (start + fuel) := by
    exact quittingForcedContinueReversePrefixProfile_eq_child
      reward profiles roots owner hfacts.2.2.2 start fuel
  have hsurvival : prefixFloor ≤
      quittingLiteralRootStackJointSurvival word := by
    rw [show word = quittingReversePrefixRootStack shiftedRoots fuel by rfl,
      quittingLiteralRootStackJointSurvival_reversePrefixRootStack]
    exact (hprefixFloor (start + fuel)).trans
      (quittingJointSurvivalPrefix_le_forcedContinueWindow
        roots owner start fuel)
  constructor
  · rw [← hprofile]
    exact quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq
      reward word (quittingPureTimeCapChild reward (profiles start) owner start) who
        (quittingPureTimeBehaviorStrategy reward who choice)
  · rw [← hprofile]
    apply quittingLiteralRootStackProfile_debt_ge_survivalFloor_mul_gain
      reward word (quittingPureTimeCapChild reward (profiles start) owner start) who
        (quittingPureTimeBehaviorStrategy reward who choice)
      hsurvival hgap.le
    rw [hcap]
    unfold quittingTerminalDeviationDebt at hdebt
    linarith

end GameTheory
