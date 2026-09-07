import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowSupportPeelingConverse
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-! # Literal ordered-premium boundary fixtures -/

noncomputable section

namespace GameTheory.OrderedPremiumBoundaryFixtures

open QuittingSureSetOwnerRepair

def singleton : Payoff (Fin 4) := ![1, 0, 0, 0]

/-- Only the displayed triple pays players one and two above their singletons. -/
def twoRecipientReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal player =>
    if terminal.val = {0, 1, 2} then
      if player = 1 then 2 else if player = 2 then 3 else singleton player
    else singleton player

@[simp] theorem twoRecipient_singleton (player : Fin 4) :
    twoRecipientReward (quittingSingletonTerminal player) player = singleton player := by
  fin_cases player <;> norm_num +decide [twoRecipientReward, quittingSingletonTerminal, singleton]

theorem twoRecipient_nonnegativePremium : HasNonnegativeOwnQuittingPremium twoRecipientReward := by
  intro terminal player _
  rw [twoRecipient_singleton]
  fin_cases player <;> simp [twoRecipientReward, singleton] <;> split_ifs <;> norm_num

theorem twoRecipient_weakSupportPeeling :
    HasWeakQuittingPremiumSupportPeeling twoRecipientReward := by
  apply (hasWeakQuittingPremiumSupportPeeling_iff _).mpr
  intro active hactive
  by_cases hzero : (0 : Fin 4) ∈ active
  · refine ⟨0, hzero, ?_⟩
    intro terminal hterminal _ _
    simp [twoRecipientReward, singleton]
  · obtain ⟨chosen, hchosen⟩ := hactive
    refine ⟨chosen, hchosen, ?_⟩
    intro terminal hterminal hsubset _
    have hneq : terminal ≠ ({0, 1, 2} : Finset (Fin 4)) := by
      intro heq
      apply hzero
      apply hsubset
      simp [heq]
    rw [twoRecipient_singleton]
    simp [twoRecipientReward, hneq]

/-- The exact player order zero, one, two, three passes the premium rule. -/
theorem twoRecipient_rank_rule
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4)
    (hpositive : twoRecipientReward (quittingSingletonTerminal player) player <
      twoRecipientReward terminal player) :
    ∃ earlier ∈ terminal.val, earlier.val < player.val := by
  rw [twoRecipient_singleton] at hpositive
  by_cases htriple : terminal.val = ({0, 1, 2} : Finset (Fin 4))
  · refine ⟨0, by simp [htriple], ?_⟩
    fin_cases player <;> simp_all +decide [twoRecipientReward, singleton]
  · simp [twoRecipientReward, htriple] at hpositive

/-- The over-strong graph that joins every rewarded participant to every
co-member contains both directions between one and two. -/
def premiumCoMemberEdge
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (source target : Fin 4) : Prop :=
  source ≠ target ∧ ∃ terminal : {S : Finset (Fin 4) // S.Nonempty},
    source ∈ terminal.val ∧ target ∈ terminal.val ∧
      reward (quittingSingletonTerminal source) source < reward terminal source

theorem twoRecipient_coMember_twoCycle :
    premiumCoMemberEdge twoRecipientReward 1 2 ∧ premiumCoMemberEdge twoRecipientReward 2 1 := by
  constructor
  · refine ⟨by decide, ⟨{0, 1, 2}, by simp⟩, by simp, by simp, ?_⟩
    norm_num +decide [twoRecipientReward, singleton, quittingSingletonTerminal]
  · refine ⟨by decide, ⟨{0, 1, 2}, by simp⟩, by simp, by simp, ?_⟩
    norm_num +decide [twoRecipientReward, singleton, quittingSingletonTerminal]
    change (0 : ℝ) < 3
    norm_num

/-- `false` is the exceptional pair; `true` is the exceptional triple. -/
def raisedCoalition (triple : Bool) : Finset (Fin 4) :=
  if triple then {0, 1, 2} else {0, 1}

def raisedReward (triple : Bool) : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal player => if terminal.val = raisedCoalition triple
    then singleton player + 1 else singleton player

def raisedRoot (triple : Bool) : Fin 4 → PMF Bool := quittingPureSetRoot (raisedCoalition triple)

@[simp] theorem raised_absorptionMass (triple : Bool) :
    quittingRootAbsorptionMass (raisedRoot triple) = 1 := by
  apply quittingRootAbsorptionMass_pureSetRoot_of_nonempty
  cases triple <;> simp [raisedCoalition]

@[simp] theorem raised_singleton (triple : Bool) (player : Fin 4) :
    raisedReward triple (quittingSingletonTerminal player) player = singleton player := by
  cases triple <;> fin_cases player <;>
    norm_num +decide [raisedReward, raisedCoalition, quittingSingletonTerminal, singleton]

theorem raised_nonnegativePremium (triple : Bool) :
    HasNonnegativeOwnQuittingPremium (raisedReward triple) := by
  intro terminal player _
  rw [raised_singleton]
  unfold raisedReward
  split_ifs <;> linarith

theorem raised_not_weakSupportPeeling (triple : Bool) :
    ¬ HasWeakQuittingPremiumSupportPeeling (raisedReward triple) := by
  intro hpeel
  have hnonempty : (raisedCoalition triple).Nonempty := by cases triple <;> simp [raisedCoalition]
  obtain ⟨player, hplayer, hlow⟩ :=
    (hasWeakQuittingPremiumSupportPeeling_iff _).mp hpeel (raisedCoalition triple) hnonempty
  have h := hlow (raisedCoalition triple) hnonempty (Finset.Subset.refl _) hplayer
  rw [raised_singleton] at h
  norm_num [raisedReward] at h

theorem raised_quitPayoff (triple : Bool) (tail : Payoff (Fin 4)) (player : Fin 4) :
    quittingRootQuitPayoff (raisedReward triple) tail (raisedRoot triple) player =
      if player ∈ raisedCoalition triple then singleton player + 1 else singleton player := by
  unfold raisedRoot
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert]
  cases triple <;> fin_cases player <;>
    norm_num +decide [quittingSetReward, raisedReward, raisedCoalition, singleton]

theorem raised_continuePayoff (triple : Bool) (tail : Payoff (Fin 4)) (player : Fin 4) :
    quittingRootContinuePayoff (raisedReward triple) tail (raisedRoot triple) player =
      if player ∈ raisedCoalition triple then singleton player else singleton player + 1 := by
  unfold raisedRoot
  rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
  · cases triple <;> fin_cases player <;>
      norm_num +decide [quittingSetReward, raisedReward, raisedCoalition, singleton]
  · cases triple <;> fin_cases player <;> decide

theorem raised_exactRootNash (triple : Bool) (tail : Payoff (Fin 4)) :
    IsεQuittingRootNash (raisedReward triple) tail 0 (raisedRoot triple) := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash _ _ _).mp
  intro player
  rw [quittingRootEndpointDifference, raised_quitPayoff, raised_continuePayoff]
  cases triple <;> fin_cases player <;>
    norm_num +decide [raisedRoot, raisedCoalition, quittingPureSetRoot,
      quittingSetAction, singleton]

theorem raised_successor (triple : Bool) (tail : Payoff (Fin 4)) :
    quittingRootSuccessorPayoff (raisedReward triple) tail (raisedRoot triple) = ![2, 1, 1, 1] := by
  funext player
  rw [quittingRootSuccessorPayoff_eq_endpointMix, raised_quitPayoff, raised_continuePayoff]
  cases triple <;> fin_cases player <;>
    norm_num +decide [raisedRoot, raisedCoalition, quittingPureSetRoot,
      quittingSetAction, singleton]

theorem raised_successor_strictlyAboveSingleton (triple : Bool)
    (tail : Payoff (Fin 4)) (player : Fin 4) :
    raisedReward triple (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff (raisedReward triple) tail (raisedRoot triple) player := by
  rw [raised_singleton, raised_successor]
  fin_cases player <;> norm_num [singleton]

theorem raised_sureExitSet (triple : Bool) :
    IsQuittingSureExitSet (raisedReward triple) (raisedCoalition triple) := by
  cases triple <;> constructor <;> intro player hplayer <;> fin_cases player <;>
    simp_all +decide [quittingSetReward, raisedReward, singleton]

theorem raised_terminalNash (triple : Bool) :
    (quittingGame (raisedReward triple)).IsεAsymptoticNash
      (quittingTerminalPayoff (raisedReward triple)) 0
      (quittingStationaryProfile (raisedReward triple) (raisedRoot triple)) :=
  (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet _ _).mpr (raised_sureExitSet triple)

/-- Every pair premium in the triple obstruction is zero. -/
theorem triple_pair_reward (first second player : Fin 4) :
    raisedReward true ⟨{first, second}, by simp⟩ player = singleton player := by
  have hneq : ({first, second} : Finset (Fin 4)) ≠ {0, 1, 2} := by
    fin_cases first <;> fin_cases second <;> decide
  simp [raisedReward, raisedCoalition, hneq]

end GameTheory.OrderedPremiumBoundaryFixtures
