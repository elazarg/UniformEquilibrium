import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualReachedPairPremarkResidual
import UniformEquilibrium.Diagnostics.Quitting.LiteralOneDateProfile
import UniformEquilibrium.Quitting.Paths.BehaviorSupportedPureTimeReplacement
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.SelfTailClosure

/-!
# Two exact late releases after a finite stopping-law calendar

This module isolates the local compiler used by the positive-Never restart.
The source is all Continue at the fresh row and its continuation is the
literal all-Continue profile.  First one owner quits, producing a singleton;
then one outsider joins at the same row.  Both endpoints are complete
behavioral profiles, not temporal Nash rows.
-/

noncomputable section

namespace GameTheory

open Math.Probability QuittingSureSetOwnerRepair

/-- Literal data for two successive releases at one fresh live row. -/
structure QuittingPositiveNeverTwoRelease
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) where
  sourceProfile : (quittingGame reward).BehaviorProfile
  mark : ℕ
  owner : Fin 4
  outsider : Fin 4
  outsider_ne_owner : outsider ≠ owner
  source_root_eq :
    quittingProfileLiveRoot reward sourceProfile mark = quittingAllContinueRoot
  source_tail_eq :
    quittingAllContinueProfileSpine reward sourceProfile (mark + 1) =
      quittingAlwaysContinueProfile reward

namespace QuittingPositiveNeverTwoRelease

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

/-- The first released profile makes the owner Quit at the fresh row. -/
def singletonProfile (data : QuittingPositiveNeverTwoRelease reward) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralOneDateProfile reward data.sourceProfile data.owner data.mark true

/-- The second released profile makes the outsider join the owner at the
same fresh row. -/
def pairProfile (data : QuittingPositiveNeverTwoRelease reward) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralOneDateProfile reward data.singletonProfile data.outsider data.mark true

/-- The first release changes only the owner's complete behavioral strategy. -/
theorem source_to_singleton_ancestry
    (data : QuittingPositiveNeverTwoRelease reward) :
    IsQuittingBehaviorReplacementAncestry data.sourceProfile
      data.singletonProfile := by
  exact isQuittingBehaviorReplacementAncestry_update data.sourceProfile data.owner _

/-- The second release changes only the outsider's complete behavioral strategy. -/
theorem singleton_to_pair_ancestry
    (data : QuittingPositiveNeverTwoRelease reward) :
    IsQuittingBehaviorReplacementAncestry data.singletonProfile
      data.pairProfile := by
  exact isQuittingBehaviorReplacementAncestry_update data.singletonProfile data.outsider _

/-- The first released root is exactly the pure owner singleton. -/
theorem singletonProfile_root_eq_pureSingleton
    (data : QuittingPositiveNeverTwoRelease reward) :
    quittingProfileLiveRoot reward data.singletonProfile data.mark =
      quittingPureSetRoot ({data.owner} : Finset (Fin 4)) := by
  rw [singletonProfile, quittingProfileLiveRoot_literalOneDateProfile,
    data.source_root_eq]
  funext player
  by_cases hplayer : player = data.owner
  · subst player
    simp [quittingPureSetRoot, quittingSetAction]
  · rw [Function.update_of_ne hplayer]
    simp [quittingAllContinueRoot, quittingPureSetRoot, quittingSetAction, hplayer]

/-- The second released root is exactly the pure owner-outsider pair. -/
theorem pairProfile_root_eq_purePair
    (data : QuittingPositiveNeverTwoRelease reward) :
    quittingProfileLiveRoot reward data.pairProfile data.mark =
      quittingPureSetRoot ({data.owner, data.outsider} : Finset (Fin 4)) := by
  rw [pairProfile, quittingProfileLiveRoot_literalOneDateProfile,
    data.singletonProfile_root_eq_pureSingleton]
  funext player
  by_cases hplayer : player = data.outsider
  · subst player
    simp [quittingPureSetRoot, quittingSetAction]
  · rw [Function.update_of_ne hplayer]
    simp [quittingPureSetRoot, quittingSetAction, hplayer]

/-- The first release gains reach times the owner's singleton reward. -/
theorem singletonPayoff_sub_sourcePayoff_eq
    (data : QuittingPositiveNeverTwoRelease reward) :
    quittingTerminalPayoff reward data.singletonProfile data.owner -
        quittingTerminalPayoff reward data.sourceProfile data.owner =
      quittingLiveMass reward data.sourceProfile data.mark *
        reward (quittingSingletonTerminal data.owner) data.owner := by
  rw [singletonProfile,
    quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect]
  rw [data.source_root_eq, data.source_tail_eq]
  have hzero :
      (quittingTerminalSemanticPair reward
        (quittingAlwaysContinueProfile reward)).1 = (0 : Payoff (Fin 4)) := by
    funext player
    exact quittingTerminalPayoff_quittingAlwaysContinue reward player
  rw [hzero]
  have hlocal :
      quittingRootSuccessorPayoff reward 0
          (Function.update quittingAllContinueRoot data.owner (PMF.pure true)) data.owner -
        quittingRootSuccessorPayoff reward 0 quittingAllContinueRoot data.owner =
      reward (quittingSingletonTerminal data.owner) data.owner := by
    change quittingRootExpectedPayoff reward 0
          (Function.update quittingAllContinueRoot data.owner (PMF.pure true)) data.owner -
        quittingRootSuccessorPayoff reward 0 quittingAllContinueRoot data.owner = _
    rw [quittingRootExpectedPayoff_update_sub_successorPayoff]
    simp [quittingAllContinueRoot]
  rw [hlocal]

/-- At a pure owner singleton, an outsider's endpoint difference is exactly
the pair-minus-singleton table gap, independently of the declared tail. -/
theorem quittingRootEndpointDifference_pureSingleton_outsider
    (tail : Payoff (Fin 4)) (owner outsider : Fin 4)
    (hne : outsider ≠ owner) :
    quittingRootEndpointDifference reward tail
        (quittingPureSetRoot ({owner} : Finset (Fin 4))) outsider =
      reward ⟨{owner, outsider}, by simp⟩ outsider -
        reward (quittingSingletonTerminal owner) outsider := by
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_pureSetRoot_eq_insert,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
  · simp [quittingSetReward, Finset.pair_comm, hne]
    congr 2
  · simp [hne]

/-- The second release is represented by an actual screened nonempty-host mark. -/
def outsiderMark
    (data : QuittingPositiveNeverTwoRelease reward)
    (hgap : 0 ≤ reward
        ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
      reward (quittingSingletonTerminal data.owner) data.outsider) :
    QuittingActualReachedScreenedEndpointMark reward where
  sourceProfile := data.singletonProfile
  mover := data.outsider
  other := data.owner
  mark := data.mark
  selectedAction := true
  other_ne_mover := data.outsider_ne_owner.symm
  source_mover_opposite := by
    rw [data.singletonProfile_root_eq_pureSingleton]
    simp [quittingPureSetRoot, quittingSetAction, data.outsider_ne_owner]
  source_other_quits := by
    rw [data.singletonProfile_root_eq_pureSingleton]
    simp [quittingPureSetRoot, quittingSetAction]
  selected_endpoint_gain_nonneg := by
    rw [data.singletonProfile_root_eq_pureSingleton]
    change 0 ≤ quittingRootExpectedPayoff reward _
          (Function.update (quittingPureSetRoot {data.owner})
            data.outsider (PMF.pure true)) data.outsider -
        quittingRootSuccessorPayoff reward _
          (quittingPureSetRoot {data.owner}) data.outsider
    rw [quittingRootExpectedPayoff_update_sub_successorPayoff]
    have hcoefficient :
        ((PMF.pure true : PMF Bool) true).toReal -
            ((quittingPureSetRoot ({data.owner} : Finset (Fin 4))
              data.outsider) true).toReal = 1 := by
      simp [quittingPureSetRoot, quittingSetAction, data.outsider_ne_owner]
    rw [hcoefficient, one_mul,
      quittingRootEndpointDifference_pureSingleton_outsider
        _ data.owner data.outsider data.outsider_ne_owner]
    exact hgap

/-- The outsider's local endpoint gap is exactly pair reward minus singleton
reward; the continuation is screened by the sure-quitting owner. -/
theorem outsiderMark_localEndpointGap_eq
    (data : QuittingPositiveNeverTwoRelease reward)
    (hgap : 0 ≤ reward
        ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
      reward (quittingSingletonTerminal data.owner) data.outsider) :
    (data.outsiderMark hgap).localEndpointGap =
      reward ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
        reward (quittingSingletonTerminal data.owner) data.outsider := by
  unfold QuittingActualReachedScreenedEndpointMark.localEndpointGap outsiderMark
  rw [data.singletonProfile_root_eq_pureSingleton]
  change quittingRootExpectedPayoff reward _
        (Function.update (quittingPureSetRoot {data.owner})
          data.outsider (PMF.pure true)) data.outsider -
      quittingRootSuccessorPayoff reward _
        (quittingPureSetRoot {data.owner}) data.outsider = _
  rw [quittingRootExpectedPayoff_update_sub_successorPayoff]
  have hcoefficient :
      ((PMF.pure true : PMF Bool) true).toReal -
          ((quittingPureSetRoot ({data.owner} : Finset (Fin 4))
            data.outsider) true).toReal = 1 := by
    simp [quittingPureSetRoot, quittingSetAction, data.outsider_ne_owner]
  rw [hcoefficient, one_mul,
    quittingRootEndpointDifference_pureSingleton_outsider
      _ data.owner data.outsider data.outsider_ne_owner]

/-- The screened mark's literal target is the displayed pair profile. -/
theorem outsiderMark_targetProfile_eq_pairProfile
    (data : QuittingPositiveNeverTwoRelease reward)
    (hgap : 0 ≤ reward
        ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
      reward (quittingSingletonTerminal data.owner) data.outsider) :
    (data.outsiderMark hgap).targetProfile = data.pairProfile := rfl

/-- The screened mark has the pure singleton as its nonempty host. -/
def outsiderMarkPureHost
    (data : QuittingPositiveNeverTwoRelease reward)
    (hgap : 0 ≤ reward
        ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
      reward (quittingSingletonTerminal data.owner) data.outsider) :
    QuittingActualReachedScreenedEndpointMark.PurePairData
      (data.outsiderMark hgap) where
  coalition := {data.owner}
  coalition_nonempty := Finset.singleton_nonempty data.owner
  source_root_eq := data.singletonProfile_root_eq_pureSingleton

/-- The second release gains reach times the pair-minus-singleton reward gap. -/
theorem pairPayoff_sub_singletonPayoff_eq
    (data : QuittingPositiveNeverTwoRelease reward)
    (hgap : 0 ≤ reward
        ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
      reward (quittingSingletonTerminal data.owner) data.outsider) :
    quittingTerminalPayoff reward data.pairProfile data.outsider -
        quittingTerminalPayoff reward data.singletonProfile data.outsider =
      quittingLiveMass reward data.singletonProfile data.mark *
        (reward ⟨{data.owner, data.outsider}, by simp⟩ data.outsider -
          reward (quittingSingletonTerminal data.owner) data.outsider) := by
  have h :=
    (data.outsiderMark hgap).markedToggleGain_eq_liveMass_mul_localEndpointGap
      |>.trans (by rw [data.outsiderMark_localEndpointGap_eq hgap])
  change quittingTerminalPayoff reward
        (data.outsiderMark hgap).targetProfile data.outsider -
      quittingTerminalPayoff reward data.singletonProfile data.outsider = _ at h
  rw [data.outsiderMark_targetProfile_eq_pairProfile hgap] at h
  exact h

end QuittingPositiveNeverTwoRelease

end GameTheory
