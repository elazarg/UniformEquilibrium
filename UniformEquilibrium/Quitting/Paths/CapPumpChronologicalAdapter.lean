/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.NashBellmanChronologicalForcing
import UniformEquilibrium.Quitting.Paths.CapPumpSecondPersistentLabel

/-!
# Cap-pump adapters for chronological quitting certificates

The cap pump supplies only survival.  Full chronological certificates below
therefore retain the exact bounded Nash--Bellman spine as explicit input.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingChronologicalDebtShadowingSurvivalFields

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {roots : ℕ → ι → PMF Bool} {owner : ι} {K M : ℝ}

/-- Owner-persistent cap pumping fills exactly the two chronological survival
fields, without asserting any forcing or discrepancy field. -/
theorem of_capPumpOwner
    (data : QuittingChronologicalDebtData ι)
    (pump : QuittingBoundedCapPump reward data.root owner K M)
    (hfavorable : ¬Summable pump.favorableDrop)
    (hreverse : Summable pump.reverseRise)
    (howner : ¬Summable
      (quittingMarginalQuitHazard data.root owner)) :
    QuittingChronologicalDebtShadowingSurvivalFields data := by
  have hpersistent :=
    pump.hasTwoPersistent_of_owner hfavorable hreverse howner
  obtain ⟨first, second, hne, hfirst, hsecond⟩ := hpersistent
  have hcard : 2 ≤ Fintype.card ι :=
    Fintype.one_lt_card_iff.mpr ⟨first, second, hne⟩
  exact .of_twoPersistent data hcard
    ⟨first, second, hne, hfirst, hsecond⟩

/-- Known-mover excess fills exactly the two chronological survival fields,
again on the unchanged root chronology. -/
theorem of_capPumpKnownMoverExcess
    (data : QuittingChronologicalDebtData ι)
    (pump : QuittingBoundedCapPump reward data.root owner K M)
    {mover : ι} (hne : mover ≠ owner)
    (hmover : ¬Summable
      (quittingMarginalQuitHazard data.root mover))
    (hexcess : ¬BddAbove (Set.range (pump.knownMoverExcess mover))) :
    QuittingChronologicalDebtShadowingSurvivalFields data := by
  have hpersistent :=
    pump.hasTwoPersistent_of_knownMoverExcess hne hmover hexcess
  obtain ⟨first, second, hdistinct, hfirst, hsecond⟩ := hpersistent
  have hcard : 2 ≤ Fintype.card ι :=
    Fintype.one_lt_card_iff.mpr ⟨first, second, hdistinct⟩
  exact .of_twoPersistent data hcard
    ⟨first, second, hdistinct, hfirst, hsecond⟩

end QuittingChronologicalDebtShadowingSurvivalFields

/-- An exact bounded Nash--Bellman spine plus owner-persistent cap pumping
yields the full chronological certificate.  The cap pump supplies only the
two survival arguments of the existing exact-spine constructor. -/
theorem nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine_capPumpOwner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    {owner : ι} {K M : ℝ}
    (pump : QuittingBoundedCapPump reward roots owner K M)
    (hfavorable : ¬Summable pump.favorableDrop)
    (hreverse : Summable pump.reverseRise)
    (howner : ¬Summable (quittingMarginalQuitHazard roots owner))
    (hbound : ∀ time who,
      |value time who| ≤ quittingRewardBound reward)
    (hbellman : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (eta : ℝ) (heta : 0 < eta) :
    Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta) := by
  obtain ⟨hopponent, hjoint⟩ :=
    pump.survival_of_owner hfavorable hreverse howner
  exact nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine
    reward value roots hbound hbellman hnash hjoint hopponent eta heta

/-- The corresponding exact-spine consumer when a known mover is persistent
and the mover-subtracted cap excess is unbounded. -/
theorem nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine_capPumpKnownMoverExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    {owner mover : ι} {K M : ℝ}
    (pump : QuittingBoundedCapPump reward roots owner K M)
    (hne : mover ≠ owner)
    (hmover : ¬Summable (quittingMarginalQuitHazard roots mover))
    (hexcess : ¬BddAbove (Set.range (pump.knownMoverExcess mover)))
    (hbound : ∀ time who,
      |value time who| ≤ quittingRewardBound reward)
    (hbellman : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (eta : ℝ) (heta : 0 < eta) :
    Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta) := by
  obtain ⟨hopponent, hjoint⟩ :=
    pump.survival_of_knownMoverExcess hne hmover hexcess
  exact nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine
    reward value roots hbound hbellman hnash hjoint hopponent eta heta

end GameTheory
