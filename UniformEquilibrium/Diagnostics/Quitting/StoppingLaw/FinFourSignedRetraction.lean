import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualReachPaidFirstDisagreement
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport
import MathUE.FiniteResponseCycleLedger

/-!
# Four-coordinate signed retraction for quitting profiles

Replacing the four complete strategies of one Fin4 profile by those of a
second profile gives a literal four-edge hybrid path.  A positive total-debt
increase along that path selects one reverse edge carrying one quarter of the
increase.  The exact debt ledger then exposes either a paid reverse response
by the changed player or positive debt for one fixed nonmover, which is
localized by an actual source-supported paid row.
-/

noncomputable section

namespace GameTheory

open Math.Probability

private def QuittingPaidFirstDisagreementRow.castGain
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {observer : ι} {gain gain' : ℝ}
    (row : QuittingPaidFirstDisagreementRow reward profile observer gain)
    (hgain : gain = gain') :
    QuittingPaidFirstDisagreementRow reward profile observer gain' :=
  hgain ▸ row

private theorem QuittingPaidFirstDisagreementRow.castGain_sourceWitness
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {observer : ι} {gain gain' : ℝ}
    (row : QuittingPaidFirstDisagreementRow reward profile observer gain)
    (hgain : gain = gain') :
    (row.castGain hgain).sourceWitness = row.sourceWitness := by
  subst gain'
  rfl

private theorem QuittingPaidFirstDisagreementRow.castGain_start
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {observer : ι} {gain gain' : ℝ}
    (row : QuittingPaidFirstDisagreementRow reward profile observer gain)
    (hgain : gain = gain') :
    (row.castGain hgain).start = row.start := by
  subst gain'
  rfl

private theorem QuittingPaidFirstDisagreementRow.castGain_liveMass
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {observer : ι} {gain gain' : ℝ}
    (row : QuittingPaidFirstDisagreementRow reward profile observer gain)
    (hgain : gain = gain') :
    (row.castGain hgain).liveMass = row.liveMass := by
  subst gain'
  rfl

/-- Replace the coordinates with index below `count` by their target
strategies.  Only counts from zero through four are used below. -/
def quittingFinFourCoordinateHybrid
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (source target : (quittingGame reward).BehaviorProfile)
    (count : ℕ) : (quittingGame reward).BehaviorProfile :=
  fun who => if who.val < count then target who else source who

namespace quittingFinFourCoordinateHybrid

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  (source target : (quittingGame reward).BehaviorProfile)

@[simp] theorem zero :
    quittingFinFourCoordinateHybrid source target 0 = source := by
  funext who
  simp [quittingFinFourCoordinateHybrid]

@[simp] theorem four :
    quittingFinFourCoordinateHybrid source target 4 = target := by
  funext who
  simp [quittingFinFourCoordinateHybrid, who.isLt]

theorem succ_eq_update (count : ℕ) (hcount : count < 4) :
    quittingFinFourCoordinateHybrid source target (count + 1) =
      Function.update (quittingFinFourCoordinateHybrid source target count)
        ⟨count, hcount⟩ (target ⟨count, hcount⟩) := by
  funext who
  by_cases hwho : who = ⟨count, hcount⟩
  · subst who
    simp [quittingFinFourCoordinateHybrid]
  · have hval : who.val ≠ count := by
      intro heq
      apply hwho
      apply Fin.ext
      exact heq
    rw [Function.update_of_ne hwho]
    simp only [quittingFinFourCoordinateHybrid]
    by_cases hlt : who.val < count
    · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
    · have hge : count < who.val := lt_of_le_of_ne (Nat.le_of_not_gt hlt)
        (Ne.symm hval)
      rw [if_neg hlt, if_neg (Nat.not_lt_of_ge hge)]

theorem eq_update_succ (count : ℕ) (hcount : count < 4) :
    quittingFinFourCoordinateHybrid source target count =
      Function.update
        (quittingFinFourCoordinateHybrid source target (count + 1))
        ⟨count, hcount⟩ (source ⟨count, hcount⟩) := by
  funext who
  by_cases hwho : who = ⟨count, hcount⟩
  · subst who
    simp [quittingFinFourCoordinateHybrid]
  · have hval : who.val ≠ count := by
      intro heq
      apply hwho
      apply Fin.ext
      exact heq
    rw [Function.update_of_ne hwho]
    simp only [quittingFinFourCoordinateHybrid]
    by_cases hlt : who.val < count
    · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
    · have hge : count < who.val := lt_of_le_of_ne (Nat.le_of_not_gt hlt)
        (Ne.symm hval)
      rw [if_neg hlt, if_neg (Nat.not_lt_of_ge hge)]

end quittingFinFourCoordinateHybrid

/-- One selected reverse edge of the four-coordinate hybrid path. -/
structure QuittingFinFourSignedRetraction
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (source target : (quittingGame reward).BehaviorProfile)
    (debtIncrease : ℝ) where
  count : ℕ
  count_lt_four : count < 4
  debtDrop : debtIncrease / 4 ≤
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingFinFourCoordinateHybrid source target (count + 1))) -
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingFinFourCoordinateHybrid source target count))

namespace QuittingFinFourSignedRetraction

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {source target : (quittingGame reward).BehaviorProfile}
  {debtIncrease : ℝ}

def mover (edge : QuittingFinFourSignedRetraction source target debtIncrease) :
    Fin 4 := ⟨edge.count, edge.count_lt_four⟩

def moreOffMinimum
    (edge : QuittingFinFourSignedRetraction source target debtIncrease) :
    (quittingGame reward).BehaviorProfile :=
  quittingFinFourCoordinateHybrid source target (edge.count + 1)

def towardSource
    (edge : QuittingFinFourSignedRetraction source target debtIncrease) :
    (quittingGame reward).BehaviorProfile :=
  quittingFinFourCoordinateHybrid source target edge.count

def reverseGain
    (edge : QuittingFinFourSignedRetraction source target debtIncrease) : ℝ :=
  quittingTerminalPayoff reward edge.towardSource edge.mover -
    quittingTerminalPayoff reward edge.moreOffMinimum edge.mover

theorem towardSource_eq_update
    (edge : QuittingFinFourSignedRetraction source target debtIncrease) :
    edge.towardSource = Function.update edge.moreOffMinimum edge.mover
      (source edge.mover) := by
  exact quittingFinFourCoordinateHybrid.eq_update_succ source target
    edge.count edge.count_lt_four

theorem moreOffMinimum_eq_target_of_lt
    (edge : QuittingFinFourSignedRetraction source target debtIncrease)
    (who : Fin 4) (hwho : who.val < edge.count + 1) :
    edge.moreOffMinimum who = target who := by
  simp [moreOffMinimum, quittingFinFourCoordinateHybrid, hwho]

theorem moreOffMinimum_eq_source_of_le
    (edge : QuittingFinFourSignedRetraction source target debtIncrease)
    (who : Fin 4) (hwho : edge.count + 1 ≤ who.val) :
    edge.moreOffMinimum who = source who := by
  simp [moreOffMinimum, quittingFinFourCoordinateHybrid,
    Nat.not_lt_of_ge hwho]

theorem towardSource_eq_target_of_lt
    (edge : QuittingFinFourSignedRetraction source target debtIncrease)
    (who : Fin 4) (hwho : who.val < edge.count) :
    edge.towardSource who = target who := by
  simp [towardSource, quittingFinFourCoordinateHybrid, hwho]

theorem towardSource_eq_source_of_le
    (edge : QuittingFinFourSignedRetraction source target debtIncrease)
    (who : Fin 4) (hwho : edge.count ≤ who.val) :
    edge.towardSource who = source who := by
  simp [towardSource, quittingFinFourCoordinateHybrid,
    Nat.not_lt_of_ge hwho]

/-- Exact total-debt decomposition of the selected reverse edge. -/
theorem debtDrop_eq_reverseGain_add_nonmoverDebtDrop
    (edge : QuittingFinFourSignedRetraction source target debtIncrease) :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward edge.moreOffMinimum) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward edge.towardSource) =
      edge.reverseGain +
        ∑ who ∈ (Finset.univ.erase edge.mover),
          (quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward edge.moreOffMinimum) who -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward edge.towardSource) who) := by
  have hmover := quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    reward edge.moreOffMinimum edge.mover (source edge.mover)
  rw [← edge.towardSource_eq_update] at hmover
  have hmore := Finset.sum_erase_add Finset.univ
    (fun who => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward edge.moreOffMinimum) who)
    (Finset.mem_univ edge.mover)
  have htoward := Finset.sum_erase_add Finset.univ
    (fun who => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward edge.towardSource) who)
    (Finset.mem_univ edge.mover)
  rw [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebtSum]
  rw [← hmore, ← htoward]
  simp only [Finset.sum_sub_distrib]
  dsimp only [reverseGain]
  linarith

end QuittingFinFourSignedRetraction

/-- A positive total-debt increase selects a literal reverse hybrid edge
carrying at least one quarter of that increase. -/
theorem nonempty_quittingFinFourSignedRetraction
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (source target : (quittingGame reward).BehaviorProfile)
    (debtIncrease : ℝ)
    (hincrease : debtIncrease ≤
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward target) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source)) :
    Nonempty (QuittingFinFourSignedRetraction source target debtIncrease) := by
  let debtAt : ℕ → ℝ := fun count =>
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingFinFourCoordinateHybrid source target count))
  have htotal : debtIncrease ≤ debtAt 4 - debtAt 0 := by
    simpa [debtAt] using hincrease
  by_cases h0 : debtIncrease / 4 ≤ debtAt 1 - debtAt 0
  · exact ⟨⟨0, by omega, h0⟩⟩
  by_cases h1 : debtIncrease / 4 ≤ debtAt 2 - debtAt 1
  · exact ⟨⟨1, by omega, h1⟩⟩
  by_cases h2 : debtIncrease / 4 ≤ debtAt 3 - debtAt 2
  · exact ⟨⟨2, by omega, h2⟩⟩
  have h3 : debtIncrease / 4 ≤ debtAt 4 - debtAt 3 := by
    have h0' : debtAt 1 - debtAt 0 < debtIncrease / 4 := lt_of_not_ge h0
    have h1' : debtAt 2 - debtAt 1 < debtIncrease / 4 := lt_of_not_ge h1
    have h2' : debtAt 3 - debtAt 2 < debtIncrease / 4 := lt_of_not_ge h2
    linarith
  exact ⟨⟨3, by omega, h3⟩⟩

/-- The two literal paid outputs of one positive Fin4 signed retraction. -/
inductive QuittingFinFourSignedRetractionPaidAlternative
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {source target : (quittingGame reward).BehaviorProfile}
    {debtIncrease M : ℝ}
    (edge : QuittingFinFourSignedRetraction source target debtIncrease) : Type
  | moverPaid
      (gainFloor : debtIncrease / 8 ≤ edge.reverseGain)
      (row : QuittingPaidFirstDisagreementRow reward edge.moreOffMinimum
        edge.mover (debtIncrease / 32))
      (sourceWitness_mem : row.sourceWitness ∈
        (quittingBehaviorStoppingLaw reward
          (edge.moreOffMinimum edge.mover)).support)
      (ownSurvival_floor : debtIncrease / 8 ≤ 4 * M *
        quittingHazardSurvival
          (quittingBehaviorLiveHazard reward
            (edge.moreOffMinimum edge.mover)) row.start)
      (opponentReach_floor : debtIncrease / 8 ≤ 8 * M * row.liveMass)
      (jointReach_floor : (debtIncrease / 8) * (debtIncrease / 8) ≤
        32 * M * M * quittingSurvivalPrefix
          (quittingProfileLiveRoot reward edge.moreOffMinimum) row.start)
  | nonmoverPaid
      (observer : Fin 4)
      (observer_ne_mover : observer ≠ edge.mover)
      (observerDebt_floor : debtIncrease / 24 ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward edge.moreOffMinimum) observer)
      (row : QuittingPaidFirstDisagreementRow reward edge.moreOffMinimum
        observer (debtIncrease / 96))
      (sourceWitness_mem : row.sourceWitness ∈
        (quittingBehaviorStoppingLaw reward
          (edge.moreOffMinimum observer)).support)
      (ownSurvival_floor : debtIncrease / 24 ≤ 4 * M *
        quittingHazardSurvival
          (quittingBehaviorLiveHazard reward
            (edge.moreOffMinimum observer)) row.start)
      (opponentReach_floor : debtIncrease / 24 ≤ 8 * M * row.liveMass)
      (jointReach_floor : (debtIncrease / 24) * (debtIncrease / 24) ≤
        32 * M * M * quittingSurvivalPrefix
          (quittingProfileLiveRoot reward edge.moreOffMinimum) row.start)

/-- Every positive signed reverse edge has a mover-paid row or a nonmover-paid
row at the exact constants displayed by the packet. -/
theorem nonempty_paidAlternative
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {source target : (quittingGame reward).BehaviorProfile}
    {debtIncrease M : ℝ}
    (edge : QuittingFinFourSignedRetraction source target debtIncrease)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hincrease : 0 < debtIncrease) :
    Nonempty (QuittingFinFourSignedRetractionPaidAlternative (M := M) edge) := by
  have hdrop := edge.debtDrop
  change debtIncrease / 4 ≤
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward edge.moreOffMinimum) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward edge.towardSource) at hdrop
  rw [edge.debtDrop_eq_reverseGain_add_nonmoverDebtDrop] at hdrop
  by_cases hpaid : debtIncrease / 8 ≤ edge.reverseGain
  · have hmoverDebt : debtIncrease / 8 ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward edge.moreOffMinimum)
          edge.mover := by
      have hdeviation := quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward edge.moreOffMinimum edge.mover (source edge.mover)
      rw [← edge.towardSource_eq_update] at hdeviation
      dsimp only [QuittingFinFourSignedRetraction.reverseGain] at hpaid
      change debtIncrease / 8 ≤
        quittingContinuationBestResponseValue reward edge.moreOffMinimum
            edge.mover -
          quittingTerminalPayoff reward edge.moreOffMinimum edge.mover
      linarith
    obtain ⟨row, hsource, hown, hopponent, hjoint⟩ :=
      positiveDebt_exists_actualJointReach_paidRow_mem_support reward
        edge.moreOffMinimum edge.mover M (debtIncrease / 8) hreward
        (by positivity) hmoverDebt
    have hgainEq : debtIncrease / 8 / 4 = debtIncrease / 32 := by ring
    let row' := row.castGain hgainEq
    have hsource' : row'.sourceWitness ∈
        (quittingBehaviorStoppingLaw reward
          (edge.moreOffMinimum edge.mover)).support := by
      rw [row.castGain_sourceWitness hgainEq]
      exact hsource
    have hown' : debtIncrease / 8 ≤ 4 * M *
        quittingHazardSurvival
          (quittingBehaviorLiveHazard reward
            (edge.moreOffMinimum edge.mover)) row'.start := by
      rw [row.castGain_start hgainEq]
      exact hown
    have hopponent' : debtIncrease / 8 ≤ 8 * M * row'.liveMass := by
      rw [row.castGain_liveMass hgainEq]
      exact hopponent
    have hjoint' : (debtIncrease / 8) * (debtIncrease / 8) ≤
        32 * M * M * quittingSurvivalPrefix
          (quittingProfileLiveRoot reward edge.moreOffMinimum) row'.start := by
      rw [row.castGain_start hgainEq]
      exact hjoint
    exact ⟨.moverPaid hpaid row' hsource' hown' hopponent' hjoint'⟩
  · have hnonmoverSum : debtIncrease / 8 <
        ∑ who ∈ (Finset.univ.erase edge.mover),
          (quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward edge.moreOffMinimum) who -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward edge.towardSource) who) := by
      have hgain : edge.reverseGain < debtIncrease / 8 := lt_of_not_ge hpaid
      linarith
    have hcard : (Finset.univ.erase edge.mover).card = 3 := by
      simp
    have hindices : (Finset.univ.erase edge.mover).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hcardZero := congrArg Finset.card hempty
      simp at hcardZero
    have htotal : ((Finset.univ.erase edge.mover).card : ℝ) *
          (debtIncrease / 24) ≤
        ∑ who ∈ (Finset.univ.erase edge.mover),
          (quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward edge.moreOffMinimum) who -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward edge.towardSource) who) := by
      calc
        ((Finset.univ.erase edge.mover).card : ℝ) *
            (debtIncrease / 24) = 3 * (debtIncrease / 24) := by
              rw [hcard]
              norm_num
        _ = debtIncrease / 8 := by ring
        _ ≤ _ := hnonmoverSum.le
    obtain ⟨observer, hobserverMem, hobserverDiff⟩ :=
      MathUE.FiniteResponseCycleLedger.exists_mem_value_ge_of_card_mul_le_sum
        (Finset.univ.erase edge.mover) hindices
        (fun who =>
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward edge.moreOffMinimum) who -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward edge.towardSource) who)
        (debtIncrease / 24) htotal
    have hobserverNe : observer ≠ edge.mover := by
      simpa using hobserverMem
    have hobserverDebt : debtIncrease / 24 ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward edge.moreOffMinimum) observer := by
      have htargetNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward (quittingTerminalSemanticPair_mem_carrier reward edge.towardSource)
        observer
      linarith
    obtain ⟨row, hsource, hown, hopponent, hjoint⟩ :=
      positiveDebt_exists_actualJointReach_paidRow_mem_support reward
        edge.moreOffMinimum observer M (debtIncrease / 24) hreward
        (by positivity) hobserverDebt
    have hgainEq : debtIncrease / 24 / 4 = debtIncrease / 96 := by ring
    let row' := row.castGain hgainEq
    have hsource' : row'.sourceWitness ∈
        (quittingBehaviorStoppingLaw reward
          (edge.moreOffMinimum observer)).support := by
      rw [row.castGain_sourceWitness hgainEq]
      exact hsource
    have hown' : debtIncrease / 24 ≤ 4 * M *
        quittingHazardSurvival
          (quittingBehaviorLiveHazard reward
            (edge.moreOffMinimum observer)) row'.start := by
      rw [row.castGain_start hgainEq]
      exact hown
    have hopponent' : debtIncrease / 24 ≤ 8 * M * row'.liveMass := by
      rw [row.castGain_liveMass hgainEq]
      exact hopponent
    have hjoint' : (debtIncrease / 24) * (debtIncrease / 24) ≤
        32 * M * M * quittingSurvivalPrefix
          (quittingProfileLiveRoot reward edge.moreOffMinimum) row'.start := by
      rw [row.castGain_start hgainEq]
      exact hjoint
    exact ⟨.nonmoverPaid observer hobserverNe hobserverDebt row' hsource'
      hown' hopponent' hjoint'⟩

/-- Packet-normalized output when the selected vertex exceeds its retained
source by `epsilon / 2`. -/
inductive QuittingFinFourUniformExcessPaidAlternative
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {source target : (quittingGame reward).BehaviorProfile}
    {epsilon M : ℝ}
    (edge : QuittingFinFourSignedRetraction source target (epsilon / 2)) : Type
  | moverPaid
      (gainFloor : epsilon / 16 ≤ edge.reverseGain)
      (row : QuittingPaidFirstDisagreementRow reward edge.moreOffMinimum
        edge.mover (epsilon / 64))
      (sourceWitness_mem : row.sourceWitness ∈
        (quittingBehaviorStoppingLaw reward
          (edge.moreOffMinimum edge.mover)).support)
      (ownSurvival_floor : epsilon / 16 ≤ 4 * M *
        quittingHazardSurvival
          (quittingBehaviorLiveHazard reward
            (edge.moreOffMinimum edge.mover)) row.start)
      (opponentReach_floor : epsilon / 16 ≤ 8 * M * row.liveMass)
      (jointReach_floor : (epsilon / 16) * (epsilon / 16) ≤
        32 * M * M * quittingSurvivalPrefix
          (quittingProfileLiveRoot reward edge.moreOffMinimum) row.start)
  | nonmoverPaid
      (observer : Fin 4)
      (observer_ne_mover : observer ≠ edge.mover)
      (observerDebt_floor : epsilon / 48 ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward edge.moreOffMinimum) observer)
      (row : QuittingPaidFirstDisagreementRow reward edge.moreOffMinimum
        observer (epsilon / 192))
      (sourceWitness_mem : row.sourceWitness ∈
        (quittingBehaviorStoppingLaw reward
          (edge.moreOffMinimum observer)).support)
      (ownSurvival_floor : epsilon / 48 ≤ 4 * M *
        quittingHazardSurvival
          (quittingBehaviorLiveHazard reward
            (edge.moreOffMinimum observer)) row.start)
      (opponentReach_floor : epsilon / 48 ≤ 8 * M * row.liveMass)
      (jointReach_floor : (epsilon / 48) * (epsilon / 48) ≤
        32 * M * M * quittingSurvivalPrefix
          (quittingProfileLiveRoot reward edge.moreOffMinimum) row.start)

/-- The exact `epsilon / 16`, `epsilon / 64`, `epsilon / 48`, and
`epsilon / 192` specialization used by a uniformly off-minimum cycle. -/
theorem nonempty_uniformExcessPaidAlternative
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {source target : (quittingGame reward).BehaviorProfile}
    {epsilon M : ℝ}
    (edge : QuittingFinFourSignedRetraction source target (epsilon / 2))
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hepsilon : 0 < epsilon) :
    Nonempty (QuittingFinFourUniformExcessPaidAlternative (M := M) edge) := by
  obtain ⟨alternative⟩ := nonempty_paidAlternative edge hreward (by positivity)
  cases alternative with
  | moverPaid hgain row hsource hown hopponent hjoint =>
      have hfloor : epsilon / 2 / 8 = epsilon / 16 := by ring
      have hrowGain : epsilon / 2 / 32 = epsilon / 64 := by ring
      let row' := row.castGain hrowGain
      have hsource' : row'.sourceWitness ∈
          (quittingBehaviorStoppingLaw reward
            (edge.moreOffMinimum edge.mover)).support := by
        rw [row.castGain_sourceWitness hrowGain]
        exact hsource
      have hown' : epsilon / 16 ≤ 4 * M *
          quittingHazardSurvival
            (quittingBehaviorLiveHazard reward
              (edge.moreOffMinimum edge.mover)) row'.start := by
        rw [row.castGain_start hrowGain, ← hfloor]
        exact hown
      have hopponent' : epsilon / 16 ≤ 8 * M * row'.liveMass := by
        rw [row.castGain_liveMass hrowGain, ← hfloor]
        exact hopponent
      have hjoint' : (epsilon / 16) * (epsilon / 16) ≤
          32 * M * M * quittingSurvivalPrefix
            (quittingProfileLiveRoot reward edge.moreOffMinimum) row'.start := by
        rw [row.castGain_start hrowGain, ← hfloor]
        exact hjoint
      rw [hfloor] at hgain
      exact ⟨.moverPaid hgain row' hsource' hown' hopponent' hjoint'⟩
  | nonmoverPaid observer hne hdebt row hsource hown hopponent hjoint =>
      have hfloor : epsilon / 2 / 24 = epsilon / 48 := by ring
      have hrowGain : epsilon / 2 / 96 = epsilon / 192 := by ring
      let row' := row.castGain hrowGain
      have hsource' : row'.sourceWitness ∈
          (quittingBehaviorStoppingLaw reward
            (edge.moreOffMinimum observer)).support := by
        rw [row.castGain_sourceWitness hrowGain]
        exact hsource
      have hown' : epsilon / 48 ≤ 4 * M *
          quittingHazardSurvival
            (quittingBehaviorLiveHazard reward
              (edge.moreOffMinimum observer)) row'.start := by
        rw [row.castGain_start hrowGain, ← hfloor]
        exact hown
      have hopponent' : epsilon / 48 ≤ 8 * M * row'.liveMass := by
        rw [row.castGain_liveMass hrowGain, ← hfloor]
        exact hopponent
      have hjoint' : (epsilon / 48) * (epsilon / 48) ≤
          32 * M * M * quittingSurvivalPrefix
            (quittingProfileLiveRoot reward edge.moreOffMinimum) row'.start := by
        rw [row.castGain_start hrowGain, ← hfloor]
        exact hjoint
      rw [hfloor] at hdebt
      exact ⟨.nonmoverPaid observer hne hdebt row' hsource' hown'
        hopponent' hjoint'⟩

end GameTheory
