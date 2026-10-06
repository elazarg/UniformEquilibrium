import UniformEquilibrium.Quitting.Classification.JoiningAttractiveCoreBadJacobian
import UniformEquilibrium.Quitting.Root.NegativeBadRootSelectedReturn

/-! # Actual selected return on the dense attractive-core annotation domain

The negative-index obstruction internally counts all full ambient fixed
points. The source hypotheses supply their actual derivatives. The pure-core
exit is explicit; boundary restoration is not part of this declaration.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_exactRoot_singletonSublevel_of_joiningAttractive_generic_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hattractive : HasStrictJoiningAttractivePremiumCore reward)
    (hcard : (quittingPremiumCore reward).card = 3)
    (havoid : tail ∈ quittingPairTieAvoidanceDomain reward (quittingCoreOrderedPairs reward))
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (quittingPureSetRoot (quittingPremiumCore reward))) :
    ∃ root, IsεQuittingRootNash reward tail 0 root ∧
      ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
        reward (quittingSingletonTerminal player) player := by
  apply exists_exactRoot_singletonSublevel_of_badRoot_negative_derivatives reward tail
  intro root hnash hbad
  exact joiningAttractive_badRoot_hasFDerivAt_and_negative_det reward tail hattractive hcard
    havoid hbelow hnopure root hnash hbad

end GameTheory
