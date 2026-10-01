/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope

/-! # Arbitrary-tail endpoints of independent singleton roots

Exact owner and nonowner endpoints, the Boolean marginal identities they use,
and solo absorption share this owner. The tail is arbitrary; no equilibrium,
singleton sign or positive-hazard hypothesis is needed for the endpoint formulas.
-/

noncomputable section

namespace GameTheory

open StochasticGame _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Marginals of a solo-quitter row -/

/-- The owner's and the complementary mass of a Boolean hazard sum to one. -/
theorem quittingSoloHazardMass_add (hazard : PMF Bool) :
    (hazard false).toReal + (hazard true).toReal = 1 := by
  simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one hazard

omit [Fintype ι] in
/-- The owner's marginal at its own solo row is the supplied hazard. -/
@[simp] theorem quittingSoloStationaryRoot_apply_owner
    (owner : ι) (hazard : PMF Bool) :
    quittingSoloStationaryRoot owner hazard owner = hazard := by
  simp [quittingSoloStationaryRoot]

omit [Fintype ι] in
/-- Every coordinate other than the owner continues surely at a solo row. -/
theorem quittingSoloStationaryRoot_apply_other
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    quittingSoloStationaryRoot owner hazard other = PMF.pure false := by
  simp [quittingSoloStationaryRoot, hne]

/-! ## Exact endpoint formulas at a solo-quitter row -/

/-- The owner's pure-Quit endpoint at its own solo row is its singleton
reward, whatever the declared continuation. -/
theorem quittingRootQuitPayoff_soloStationaryRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) (tail : Payoff ι) :
    quittingRootQuitPayoff reward tail
        (quittingSoloStationaryRoot owner hazard) owner =
      quittingSoloReward reward owner owner := by
  have h := congrFun
    (quittingRootSuccessorPayoff_solo reward owner (PMF.pure true) tail) owner
  unfold quittingRootQuitPayoff
  rw [update_quittingSoloStationaryRoot_owner]
  simpa [quittingRootSuccessorPayoff] using h

/-- The owner's pure-Continue endpoint at its own solo row is the declared
continuation, because no opponent can absorb. -/
theorem quittingRootContinuePayoff_soloStationaryRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) (tail : Payoff ι) :
    quittingRootContinuePayoff reward tail
        (quittingSoloStationaryRoot owner hazard) owner = tail owner := by
  have h := congrFun
    (quittingRootSuccessorPayoff_solo reward owner (PMF.pure false) tail) owner
  unfold quittingRootContinuePayoff
  rw [update_quittingSoloStationaryRoot_owner]
  simpa [quittingRootSuccessorPayoff] using h

/-- An inactive coordinate's pure-Quit endpoint at a solo row mixes quitting
alone with colliding with the owner, and does not depend on the declared
continuation. -/
theorem quittingRootQuitPayoff_soloStationaryRoot_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (tail : Payoff ι) :
    quittingRootQuitPayoff reward tail
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard false).toReal * quittingSoloReward reward other other +
        (hazard true).toReal *
          quittingSingletonCollisionReward reward owner other := by
  have h := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    (fun _ => quittingSoloStationaryRoot owner hazard) other tail 0
  rw [h]
  exact quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
    reward hne hazard

/-- An inactive coordinate's pure-Continue endpoint at a solo row is the
row's own successor value there: the coordinate already continues surely. -/
theorem quittingRootContinuePayoff_soloStationaryRoot_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (tail : Payoff ι) :
    quittingRootContinuePayoff reward tail
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard true).toReal * quittingSoloReward reward owner other +
        (hazard false).toReal * tail other := by
  have h := congrFun
    (quittingRootSuccessorPayoff_solo reward owner hazard tail) other
  unfold quittingRootContinuePayoff
  rw [update_quittingSoloStationaryRoot_other hne]
  simpa [quittingRootSuccessorPayoff] using h

/-! ## Exact solo absorption -/

/-- **Absorption at the solo-quitter row.**  The all-continue mass is
`1 - p < 1` exactly when the owner's rate `p` is positive.

This lemma is not decoration.  The all-continue row reproduces *every* value
vector and is endpoint-Nash against every tail dominating the singleton
rewards, so "reproduces its own value and is endpoint-Nash" certifies
nothing by itself; the declared value only becomes a genuine expected
terminal payoff once play is absorbed with probability one. -/
theorem quittingStationaryContinueMass_soloStationaryRoot_lt_one
    (owner : ι) (hazard : PMF Bool) (hpositive : 0 < (hazard true).toReal) :
    quittingStationaryContinueMass
      (quittingSoloStationaryRoot owner hazard) < 1 := by
  have hsum := quittingSoloHazardMass_add hazard
  rw [quittingStationaryContinueMass_solo]
  linarith

/-- The solo row's one-stage absorption probability is the owner's rate. -/
@[simp] theorem quittingRootAbsorptionMass_soloStationaryRoot
    (owner : ι) (hazard : PMF Bool) :
    quittingRootAbsorptionMass (quittingSoloStationaryRoot owner hazard) =
      (hazard true).toReal := by
  have hsum := quittingSoloHazardMass_add hazard
  unfold quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_solo]
  linarith

end GameTheory
