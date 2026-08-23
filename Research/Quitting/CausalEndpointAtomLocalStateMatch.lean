/-
This module localizes a direct endpoint-recipient atom from its global
profile to the literal reached Bellman row.  The rectangle mode is fenced.
-/

import Research.Quitting.ConcentratedCollisionFourRoleMonodromy
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawFiniteSpliceMarkedLaw
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCausalCollisionAtomicOrientation

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota] [Nonempty iota]

/-- Two terminal laws whose canonical roots agree before a reached stage
differ globally by the common live mass times the difference of their shifted
laws.  This is the eventwise version of prefix scaling. -/
theorem quittingTerminalOutcomeMass_sub_eq_liveMass_mul_spine_sub
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (first second : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset iota // S.Nonempty})
    (hagree : ∀ time, time < stage →
      quittingProfileLiveRoot reward first time =
        quittingProfileLiveRoot reward second time) :
    quittingTerminalOutcomeMass reward first (some terminal) -
        quittingTerminalOutcomeMass reward second (some terminal) =
      quittingLiveMass reward second stage *
        (quittingTerminalOutcomeMass reward
            (quittingAllContinueProfileSpine reward first stage)
            (some terminal) -
          quittingTerminalOutcomeMass reward
            (quittingAllContinueProfileSpine reward second stage)
            (some terminal)) := by
  let event : Finset (QuittingTerminalOutcome iota) := {some terminal}
  let eventReward := quittingTerminalOutcomeEventReward event
  let observer : iota := Classical.choice inferInstance
  let firstRoot := quittingProfileLiveRoot reward first
  let secondRoot := quittingProfileLiveRoot reward second
  have hfirst := quittingTerminalOutcomeEventMass_eq_rootSequenceTerminalValue
    reward first event (by simp [event]) observer
  have hsecond := quittingTerminalOutcomeEventMass_eq_rootSequenceTerminalValue
    reward second event (by simp [event]) observer
  have hfirstSpine :=
    quittingTerminalOutcomeEventMass_eq_rootSequenceTerminalValue reward
      (quittingAllContinueProfileSpine reward first stage) event
      (by simp [event]) observer
  have hsecondSpine :=
    quittingTerminalOutcomeEventMass_eq_rootSequenceTerminalValue reward
      (quittingAllContinueProfileSpine reward second stage) event
      (by simp [event]) observer
  have hfirstSpineRoot : quittingProfileLiveRoot reward
      (quittingAllContinueProfileSpine reward first stage) =
        fun offset ↦ firstRoot (stage + offset) := by
    funext offset player
    unfold quittingProfileLiveRoot firstRoot
    exact quittingAllContinueProfileSpine_apply_liveHist
      reward first stage player offset
  have hsecondSpineRoot : quittingProfileLiveRoot reward
      (quittingAllContinueProfileSpine reward second stage) =
        fun offset ↦ secondRoot (stage + offset) := by
    funext offset player
    unfold quittingProfileLiveRoot secondRoot
    exact quittingAllContinueProfileSpine_apply_liveHist
      reward second stage player offset
  rw [hfirstSpineRoot] at hfirstSpine
  rw [hsecondSpineRoot] at hsecondSpine
  have hprefix :=
    quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
      eventReward firstRoot secondRoot observer stage (by
        intro time htime
        exact hagree time htime)
  rw [quittingRootSequenceTerminalValue_eq_shift eventReward firstRoot
        observer stage,
      quittingRootSequenceTerminalValue_eq_shift eventReward secondRoot
        observer stage] at hprefix
  have hcalc :
      quittingTerminalOutcomeEventMass reward first event -
          quittingTerminalOutcomeEventMass reward second event =
        quittingJointSurvivalWeight secondRoot 0 stage *
          (quittingTerminalOutcomeEventMass reward
              (quittingAllContinueProfileSpine reward first stage) event -
            quittingTerminalOutcomeEventMass reward
              (quittingAllContinueProfileSpine reward second stage) event) := by
    calc
      _ = quittingRootSequenceTerminalValue eventReward firstRoot observer 0 -
          quittingRootSequenceTerminalValue eventReward secondRoot observer 0 :=
        congrArg₂ (fun x y : ℝ ↦ x - y) hfirst hsecond
      _ = quittingJointSurvivalWeight secondRoot 0 stage *
          (quittingRootSequenceTerminalValue eventReward
              (fun offset ↦ firstRoot (stage + offset)) observer 0 -
            quittingRootSequenceTerminalValue eventReward
              (fun offset ↦ secondRoot (stage + offset)) observer 0) := hprefix
      _ = quittingJointSurvivalWeight secondRoot 0 stage *
          (quittingTerminalOutcomeEventMass reward
              (quittingAllContinueProfileSpine reward first stage) event -
            quittingTerminalOutcomeEventMass reward
              (quittingAllContinueProfileSpine reward second stage) event) := by
        rw [hfirstSpine, hsecondSpine]
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
  simpa only [event, quittingTerminalOutcomeEventMass, Finset.sum_singleton,
    firstRoot, secondRoot] using hcalc

/-- Every signed payoff atom itself obeys the same prefix factorization. -/
theorem quittingTerminalPayoffDifferenceAtom_eq_liveMass_mul_spineAtom
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : iota) (stage : ℕ)
    (terminal : {S : Finset iota // S.Nonempty})
    (hagree : ∀ time, time < stage →
      quittingProfileLiveRoot reward first time =
        quittingProfileLiveRoot reward second time) :
    quittingTerminalPayoffDifferenceAtom reward first second observer
        (some terminal) =
      quittingLiveMass reward second stage *
        quittingTerminalPayoffDifferenceAtom reward
          (quittingAllContinueProfileSpine reward first stage)
          (quittingAllContinueProfileSpine reward second stage)
          observer (some terminal) := by
  unfold quittingTerminalPayoffDifferenceAtom
  rw [quittingTerminalOutcomeMass_sub_eq_liveMass_mul_spine_sub
    reward first second stage terminal hagree]
  ring

/-- A one-stage pure endpoint update has exactly the required common prefix,
so every direct atom between the global endpoint profiles localizes to the
same atom at their actual reached row. -/
theorem quittingTerminalPayoffDifferenceAtom_stagePureEndpoint_eq_liveMass_mul_local
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : iota) (stage : ℕ) (action : Bool)
    (terminal : {S : Finset iota // S.Nonempty}) :
    let endpoint := Function.update profile mover
      (quittingStagePureEndpointBehaviorDeviation reward profile mover stage
        action)
    quittingTerminalPayoffDifferenceAtom reward endpoint profile observer
        (some terminal) =
      quittingLiveMass reward profile stage *
        quittingTerminalPayoffDifferenceAtom reward
          (quittingAllContinueProfileSpine reward endpoint stage)
          (quittingAllContinueProfileSpine reward profile stage)
          observer (some terminal) := by
  dsimp only
  apply quittingTerminalPayoffDifferenceAtom_eq_liveMass_mul_spineAtom
  intro time htime
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation]
  exact quittingRootSequenceUpdate_stageDeviationHazard_of_lt
    (quittingProfileLiveRoot reward profile) mover (PMF.pure action)
      (fun offset ↦
        quittingProfileLiveRoot reward profile (stage + 1 + offset) mover)
      htime

/-- A quantitative global prescribed-recipient atom becomes a quantitative
atom on the literal state-matched reached row, with no loss.  The absence of
loss uses only `liveMass ≤ 1`; the exact equality above retains the prefix
survival if it is needed later. -/
theorem prescribedEndpointRecipientAtom_localStateMatch
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover recipient : iota) (stage : ℕ) (action : Bool)
    (terminal : {S : Finset iota // S.Nonempty})
    (charge : ℝ) (hcharge : 0 < charge)
    (hglobal : charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update profile mover
            (quittingStagePureEndpointBehaviorDeviation reward profile mover
              stage action)) profile recipient (some terminal)) :
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (quittingAllContinueProfileSpine reward
            (Function.update profile mover
              (quittingStagePureEndpointBehaviorDeviation reward profile mover
                stage action)) stage)
          (quittingAllContinueProfileSpine reward profile stage)
          recipient (some terminal) := by
  let localAtom := quittingTerminalPayoffDifferenceAtom reward
    (quittingAllContinueProfileSpine reward
      (Function.update profile mover
        (quittingStagePureEndpointBehaviorDeviation reward profile mover stage
          action)) stage)
    (quittingAllContinueProfileSpine reward profile stage)
    recipient (some terminal)
  have hfactor :=
    quittingTerminalPayoffDifferenceAtom_stagePureEndpoint_eq_liveMass_mul_local
      reward profile mover recipient stage action terminal
  have hcardPos : 0 <
      (Fintype.card (QuittingTerminalOutcome iota) : ℝ) := by positivity
  have hglobalPos : 0 < quittingTerminalPayoffDifferenceAtom reward
      (Function.update profile mover
        (quittingStagePureEndpointBehaviorDeviation reward profile mover stage
          action)) profile recipient (some terminal) := by
    have hhalfPos : 0 < charge / 2 := by positivity
    nlinarith
  have hliveNonneg := quittingLiveMass_nonneg reward profile stage
  have hliveLe := quittingLiveMass_le_one reward profile stage
  have hlocalPos : 0 < localAtom := by
    rw [show quittingTerminalPayoffDifferenceAtom reward
          (Function.update profile mover
            (quittingStagePureEndpointBehaviorDeviation reward profile mover
              stage action)) profile recipient (some terminal) =
        quittingLiveMass reward profile stage * localAtom by
      simpa only [localAtom] using hfactor] at hglobalPos
    rcases mul_pos_iff.mp hglobalPos with hpositive | hnegative
    · exact hpositive.2
    · exact False.elim ((not_lt_of_ge hliveNonneg) hnegative.1)
  have hfactorLe : quittingTerminalPayoffDifferenceAtom reward
        (Function.update profile mover
          (quittingStagePureEndpointBehaviorDeviation reward profile mover stage
            action)) profile recipient (some terminal) ≤ localAtom := by
    rw [show quittingTerminalPayoffDifferenceAtom reward
          (Function.update profile mover
            (quittingStagePureEndpointBehaviorDeviation reward profile mover
              stage action)) profile recipient (some terminal) =
        quittingLiveMass reward profile stage * localAtom by
      simpa only [localAtom] using hfactor]
    exact mul_le_of_le_one_left hlocalPos.le hliveLe
  exact hglobal.trans (mul_le_mul_of_nonneg_left hfactorLe hcardPos.le)

/-- Source-minus-endpoint orientation used by the debt-recipient decoder. -/
theorem prescribedSourceEndpointRecipientAtom_localStateMatch
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover recipient : iota) (stage : ℕ) (action : Bool)
    (terminal : {S : Finset iota // S.Nonempty})
    (charge : ℝ) (hcharge : 0 < charge)
    (hglobal : charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward profile
          (Function.update profile mover
            (quittingStagePureEndpointBehaviorDeviation reward profile mover
              stage action)) recipient (some terminal)) :
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (quittingAllContinueProfileSpine reward profile stage)
          (quittingAllContinueProfileSpine reward
            (Function.update profile mover
              (quittingStagePureEndpointBehaviorDeviation reward profile mover
                stage action)) stage)
          recipient (some terminal) := by
  let endpoint := Function.update profile mover
    (quittingStagePureEndpointBehaviorDeviation reward profile mover stage action)
  let localAtom := quittingTerminalPayoffDifferenceAtom reward
    (quittingAllContinueProfileSpine reward profile stage)
    (quittingAllContinueProfileSpine reward endpoint stage)
    recipient (some terminal)
  have hagree : ∀ time, time < stage →
      quittingProfileLiveRoot reward profile time =
        quittingProfileLiveRoot reward endpoint time := by
    intro time htime
    symm
    dsimp only [endpoint]
    rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
      quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation]
    exact quittingRootSequenceUpdate_stageDeviationHazard_of_lt
      (quittingProfileLiveRoot reward profile) mover (PMF.pure action)
        (fun offset ↦
          quittingProfileLiveRoot reward profile (stage + 1 + offset) mover)
        htime
  have hfactor :=
    quittingTerminalPayoffDifferenceAtom_eq_liveMass_mul_spineAtom
      reward profile endpoint recipient stage terminal hagree
  have hliveEq : quittingLiveMass reward endpoint stage =
      quittingLiveMass reward profile stage := by
    dsimp only [endpoint]
    exact quittingLiveMass_stagePureEndpoint_eq profile mover stage action
  rw [hliveEq] at hfactor
  have hcardPos : 0 <
      (Fintype.card (QuittingTerminalOutcome iota) : ℝ) := by positivity
  have hglobalPos : 0 < quittingTerminalPayoffDifferenceAtom reward profile
      endpoint recipient (some terminal) := by
    have hhalfPos : 0 < charge / 2 := by positivity
    dsimp only [endpoint] at hglobal ⊢
    nlinarith
  have hliveNonneg := quittingLiveMass_nonneg reward profile stage
  have hliveLe := quittingLiveMass_le_one reward profile stage
  have hlocalPos : 0 < localAtom := by
    rw [show quittingTerminalPayoffDifferenceAtom reward profile endpoint
          recipient (some terminal) =
        quittingLiveMass reward profile stage * localAtom by
      simpa only [localAtom] using hfactor] at hglobalPos
    rcases mul_pos_iff.mp hglobalPos with hpositive | hnegative
    · exact hpositive.2
    · exact False.elim ((not_lt_of_ge hliveNonneg) hnegative.1)
  have hfactorLe : quittingTerminalPayoffDifferenceAtom reward profile endpoint
      recipient (some terminal) ≤ localAtom := by
    rw [show quittingTerminalPayoffDifferenceAtom reward profile endpoint
          recipient (some terminal) =
        quittingLiveMass reward profile stage * localAtom by
      simpa only [localAtom] using hfactor]
    exact mul_le_of_le_one_left hlocalPos.le hliveLe
  exact hglobal.trans (mul_le_mul_of_nonneg_left hfactorLe hcardPos.le)

omit [Nonempty iota] in
/-- The two shifted endpoint profiles are one literal common-tail Bellman
edge: only the mover's first root coordinate differs. -/
theorem stagePureEndpoint_shiftedProfiles_commonTail
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : iota) (stage : ℕ) (action : Bool) :
    let endpoint := Function.update profile mover
      (quittingStagePureEndpointBehaviorDeviation reward profile mover stage
        action)
    let sourceLocal := quittingAllContinueProfileSpine reward profile stage
    let targetLocal := quittingAllContinueProfileSpine reward endpoint stage
    quittingProfileLiveRoot reward sourceLocal 0 =
        quittingProfileLiveRoot reward profile stage ∧
      quittingProfileLiveRoot reward targetLocal 0 =
        Function.update (quittingProfileLiveRoot reward profile stage) mover
          (PMF.pure action) ∧
      ∀ offset,
        quittingProfileLiveRoot reward targetLocal (offset + 1) =
          quittingProfileLiveRoot reward sourceLocal (offset + 1) := by
  dsimp only
  let endpoint := Function.update profile mover
    (quittingStagePureEndpointBehaviorDeviation reward profile mover stage
      action)
  have hspine (p : (quittingGame reward).BehaviorProfile) :
      quittingProfileLiveRoot reward
          (quittingAllContinueProfileSpine reward p stage) =
        fun offset ↦ quittingProfileLiveRoot reward p (stage + offset) := by
    funext offset player
    unfold quittingProfileLiveRoot
    exact quittingAllContinueProfileSpine_apply_liveHist
      reward p stage player offset
  constructor
  · rw [hspine]
    simp
  constructor
  · rw [hspine]
    simp only [Nat.add_zero]
    exact quittingProfileLiveRoot_stagePureEndpoint_self
      profile mover stage action
  · intro offset
    rw [hspine, hspine]
    dsimp only [endpoint]
    rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
      quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation,
      quittingRootSequenceUpdate]
    have htime : stage + (offset + 1) = stage + 1 + offset := by omega
    rw [htime, quittingStageDeviationHazard_add]
    exact Function.update_eq_self mover _

omit [Nonempty iota] in
/-- Updating a different player's behavior does not alter the mover's
canonical live marginal, hence does not alter the mover's one-stage endpoint
strategy. -/
theorem quittingStagePureEndpointBehaviorDeviation_update_other
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : iota) (hne : mover ≠ observer)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (stage : ℕ) (action : Bool) :
    quittingStagePureEndpointBehaviorDeviation reward
        (Function.update profile observer deviation) mover stage action =
      quittingStagePureEndpointBehaviorDeviation reward profile mover stage
        action := by
  funext time history
  unfold quittingStagePureEndpointBehaviorDeviation
  unfold quittingStageDeviationHazard
  split_ifs
  all_goals try rfl
  all_goals
    unfold quittingProfileLiveRoot
    rw [Function.update_of_ne hne]

/-- A rectangle's common recipient deviation commutes into the background.
The two rectangle endpoints are therefore another one-stage pure endpoint
edge on a common literal tail. -/
theorem rectangleEndpoint_localStateMatch
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover recipient : iota) (hne : mover ≠ recipient)
    (deviation : (quittingGame reward).BehaviorStrategy recipient)
    (stage : ℕ) (action : Bool)
    (terminal : {S : Finset iota // S.Nonempty})
    (charge : ℝ) (hcharge : 0 < charge)
    (hglobal : charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update
            (Function.update profile mover
              (quittingStagePureEndpointBehaviorDeviation reward profile mover
                stage action)) recipient deviation)
          (Function.update profile recipient deviation)
          recipient (some terminal)) :
    let base := Function.update profile recipient deviation
    let target := Function.update base mover
      (quittingStagePureEndpointBehaviorDeviation reward base mover stage action)
    let sourceLocal := quittingAllContinueProfileSpine reward base stage
    let targetLocal := quittingAllContinueProfileSpine reward target stage
    charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward targetLocal sourceLocal
            recipient (some terminal) ∧
      quittingProfileLiveRoot reward sourceLocal 0 =
          quittingProfileLiveRoot reward base stage ∧
      quittingProfileLiveRoot reward targetLocal 0 =
          Function.update (quittingProfileLiveRoot reward base stage) mover
            (PMF.pure action) ∧
      ∀ offset,
        quittingProfileLiveRoot reward targetLocal (offset + 1) =
          quittingProfileLiveRoot reward sourceLocal (offset + 1) := by
  dsimp only
  let base := Function.update profile recipient deviation
  have hstrategy := quittingStagePureEndpointBehaviorDeviation_update_other
    reward profile mover recipient hne deviation stage action
  have hprofiles : Function.update
        (Function.update profile mover
          (quittingStagePureEndpointBehaviorDeviation reward profile mover stage
            action)) recipient deviation =
      Function.update base mover
        (quittingStagePureEndpointBehaviorDeviation reward base mover stage
          action) := by
    dsimp only [base]
    rw [hstrategy]
    exact Function.update_comm hne _ _ profile
  have hlocal := prescribedEndpointRecipientAtom_localStateMatch reward base
    mover recipient stage action terminal (charge / 2) (by positivity) (by
      rw [← hprofiles]
      dsimp only [base]
      convert hglobal using 1
      all_goals ring)
  have htails := stagePureEndpoint_shiftedProfiles_commonTail reward base mover
    stage action
  refine ⟨?_, htails.1, htails.2.1, htails.2.2⟩
  dsimp only [base] at hlocal ⊢
  convert hlocal using 1
  all_goals ring

namespace ConcentratedCollisionFourRole

def HasPacketLocalPrescribedAtom
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {marked : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (rank : ℕ) (mover recipient : iota)
    (terminal : {S : Finset iota // S.Nonempty}) : Prop :=
  ∃ transfer : packetTransfer minimum packet rank,
    transfer.mover = mover ∧ transfer.recipient = recipient ∧
      let profile := packetProfile packet rank
      let endpoint := targetProfile reward profile (packet.mark rank) mover
      let sourceLocal := quittingAllContinueProfileSpine reward profile
        (packet.mark rank)
      let targetLocal := quittingAllContinueProfileSpine reward endpoint
        (packet.mark rank)
      let charge := packetRecipientCharge packet rank mover recipient
      charge / 2 ≤
          (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward sourceLocal
              targetLocal recipient (some terminal) ∧
        quittingProfileLiveRoot reward sourceLocal 0 =
            root reward profile (packet.mark rank) ∧
        quittingProfileLiveRoot reward targetLocal 0 =
            Function.update (root reward profile (packet.mark rank)) mover
              (PMF.pure (action reward profile (packet.mark rank) mover)) ∧
        ∀ offset,
          quittingProfileLiveRoot reward targetLocal (offset + 1) =
            quittingProfileLiveRoot reward sourceLocal (offset + 1)

def HasPacketLocalRectangleAtom
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {marked : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (rank : ℕ) (mover recipient : iota)
    (terminal : {S : Finset iota // S.Nonempty}) : Prop :=
  ∃ transfer : packetTransfer minimum packet rank,
    transfer.mover = mover ∧ transfer.recipient = recipient ∧
      ∃ deviation : (quittingGame reward).BehaviorStrategy recipient,
        let profile := packetProfile packet rank
        let base := Function.update profile recipient deviation
        let target := Function.update base mover
          (quittingStagePureEndpointBehaviorDeviation reward base mover
            (packet.mark rank)
            (action reward profile (packet.mark rank) mover))
        let sourceLocal := quittingAllContinueProfileSpine reward base
          (packet.mark rank)
        let targetLocal := quittingAllContinueProfileSpine reward target
          (packet.mark rank)
        let charge := packetRecipientCharge packet rank mover recipient
        charge / 4 ≤
            (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
              quittingTerminalPayoffDifferenceAtom reward targetLocal
                sourceLocal recipient (some terminal) ∧
          quittingProfileLiveRoot reward sourceLocal 0 =
              quittingProfileLiveRoot reward base (packet.mark rank) ∧
          quittingProfileLiveRoot reward targetLocal 0 =
              Function.update
                (quittingProfileLiveRoot reward base (packet.mark rank)) mover
                (PMF.pure (action reward profile (packet.mark rank) mover)) ∧
          ∀ offset,
            quittingProfileLiveRoot reward targetLocal (offset + 1) =
              quittingProfileLiveRoot reward sourceLocal (offset + 1)

/-- Direct (non-rectangle) labels in the recurrent packet are fully
source-matched: the same fixed atom is quantitative on the actual reached
common-tail Bellman edge. -/
theorem packetTransferAtomLabel_prescribed_localStateMatch
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {marked : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (rank : ℕ) (mover recipient : iota)
    (terminal : {S : Finset iota // S.Nonempty})
    (hlabel : packetTransferAtomLabel minimum packet rank mover recipient
      .prescribed terminal) :
    HasPacketLocalPrescribedAtom minimum packet rank mover recipient
      terminal := by
  unfold HasPacketLocalPrescribedAtom
  rcases hlabel with ⟨transfer, hmover, hrecipient, hatom⟩
  refine ⟨transfer, hmover, hrecipient, ?_⟩
  subst hmover
  subst hrecipient
  dsimp only
  have hcharge : 0 < packetRecipientCharge packet rank transfer.mover
      transfer.recipient := by
    simpa only [packetRecipientCharge, packetTransfer, packetProfile] using
      transfer.recipient_pos
  have hlocal := prescribedSourceEndpointRecipientAtom_localStateMatch reward
    (packetProfile packet rank) transfer.mover transfer.recipient
    (packet.mark rank)
    (action reward (packetProfile packet rank) (packet.mark rank)
      transfer.mover) terminal
    (packetRecipientCharge packet rank transfer.mover transfer.recipient)
    hcharge (by
      simpa only [packetProfile, packetRecipientCharge, packetTransfer,
        targetProfile] using hatom)
  have htails := stagePureEndpoint_shiftedProfiles_commonTail reward
    (packetProfile packet rank) transfer.mover (packet.mark rank)
      (action reward (packetProfile packet rank) (packet.mark rank)
        transfer.mover)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [targetProfile] using hlocal
  · simpa only [root] using htails.1
  · simpa only [root, targetProfile] using htails.2.1
  · simpa only [targetProfile] using htails.2.2

/-- Rectangle labels also localize to one common-tail endpoint edge, after
placing their shared recipient deviation into the background profile. -/
theorem packetTransferAtomLabel_rectangle_localStateMatch
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {marked : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (minimum : QuittingTerminalSemanticPair iota)
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (rank : ℕ) (mover recipient : iota)
    (terminal : {S : Finset iota // S.Nonempty})
    (hlabel : packetTransferAtomLabel minimum packet rank mover recipient
      .rectangle terminal) :
    HasPacketLocalRectangleAtom minimum packet rank mover recipient
      terminal := by
  unfold HasPacketLocalRectangleAtom
  rcases hlabel with
    ⟨transfer, hmover, hrecipient, deviation, hatom⟩
  refine ⟨transfer, hmover, hrecipient, deviation, ?_⟩
  subst hmover
  subst hrecipient
  dsimp only
  have hcharge : 0 < packetRecipientCharge packet rank transfer.mover
      transfer.recipient := by
    simpa only [packetRecipientCharge, packetTransfer, packetProfile] using
      transfer.recipient_pos
  have hlocal := rectangleEndpoint_localStateMatch reward
    (packetProfile packet rank) transfer.mover transfer.recipient
    transfer.recipient_ne_mover.symm deviation (packet.mark rank)
    (action reward (packetProfile packet rank) (packet.mark rank)
      transfer.mover) terminal
    (packetRecipientCharge packet rank transfer.mover transfer.recipient)
    hcharge (by
      simpa only [packetProfile, packetRecipientCharge, packetTransfer,
        targetProfile] using hatom)
  simpa only [packetProfile] using hlocal

/-- **Every recurrent collision atom is prefix-localized.**  After the
tail-escape alternative, finite selection leaves either one fixed prescribed
atom on the actual reached common-tail endpoint edge, or one fixed rectangle
atom on the corresponding edge after putting the rectangle's shared
recipient deviation into the background.  Both retain the nonvanishing
recipient charge.  The rectangle conclusion is still counterfactual: it does
not give a profitable recipient deviation at the original reached row. -/
theorem packet_tailEscape_or_fixedLocalPrescribed_or_rectangle
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (minimum : QuittingTerminalSemanticPair iota)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {marked : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < marked.val.card)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0))
    (hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (source reward (packetProfile packet rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum))) :
    (∃ᶠ rank in atTop, packetEscape minimum packet rank) ∨
      (∃ mover recipient terminal,
        mover ≠ owner ∧ recipient ≠ mover ∧
          ∃ᶠ rank in atTop,
            HasPacketLocalPrescribedAtom minimum packet rank mover recipient
                terminal ∧
              packetRecipientFloor minimum packet ≤
                packetRecipientCharge packet rank mover recipient) ∨
      ∃ mover recipient terminal,
        mover ≠ owner ∧ recipient ≠ mover ∧
          ∃ᶠ rank in atTop,
            HasPacketLocalRectangleAtom minimum packet rank mover recipient
                terminal ∧
              packetRecipientFloor minimum packet ≤
                packetRecipientCharge packet rank mover recipient := by
  have hdispatch := packet_tailEscapeFrequently_or_fixedThreeRoleAtomLabel
    minimum packet hminimumCarrier hminimum hminimumDebt
      hcollision hscale hscaleTendsto hsourceDebt
  rcases hdispatch with hescape |
      ⟨mover, recipient, mode, terminal, hmover, hrecipient, hfrequent⟩
  · exact Or.inl hescape
  · right
    cases mode with
    | prescribed =>
        left
        refine ⟨mover, recipient, terminal, hmover, hrecipient, ?_⟩
        apply hfrequent.mp
        exact Filter.Eventually.of_forall fun rank hrow ↦
          ⟨packetTransferAtomLabel_prescribed_localStateMatch minimum packet
            rank mover recipient terminal hrow.1, hrow.2⟩
    | rectangle =>
        right
        refine ⟨mover, recipient, terminal, hmover, hrecipient, ?_⟩
        apply hfrequent.mp
        exact Filter.Eventually.of_forall fun rank hrow ↦
          ⟨packetTransferAtomLabel_rectangle_localStateMatch minimum packet
            rank mover recipient terminal hrow.1, hrow.2⟩

end ConcentratedCollisionFourRole

end GameTheory
