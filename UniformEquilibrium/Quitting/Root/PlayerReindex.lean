/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.PMFProduct.Reindex
import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Low-level player reindexing for quitting roots

This module owns the table- and root-level part of player relabeling.  The
behavioral transport in `Classification.PlayerReindex` builds on these
definitions, while fixed-cap root arguments can import this narrow layer.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι κ : Type}

/-- Transport of nonempty quitter coalitions along a player equivalence. -/
def quittingCoalitionEquiv (e : ι ≃ κ) :
    {S : Finset ι // S.Nonempty} ≃ {T : Finset κ // T.Nonempty} where
  toFun S := ⟨S.1.map e.toEmbedding, Finset.map_nonempty.mpr S.2⟩
  invFun T := ⟨T.1.map e.symm.toEmbedding, Finset.map_nonempty.mpr T.2⟩
  left_inv S := by
    refine Subtype.ext ?_
    refine Finset.ext fun i => ?_
    simp [Finset.mem_map_equiv]
  right_inv T := by
    refine Subtype.ext ?_
    refine Finset.ext fun j => ?_
    simp [Finset.mem_map_equiv]

/-- The transported coalition is the image of the original coalition. -/
@[simp] theorem quittingCoalitionEquiv_coe (e : ι ≃ κ)
    (S : {S : Finset ι // S.Nonempty}) :
    (quittingCoalitionEquiv e S : Finset κ) = S.1.map e.toEmbedding :=
  rfl

/-- The pulled-back coalition is the preimage of the original coalition. -/
@[simp] theorem quittingCoalitionEquiv_symm_coe (e : ι ≃ κ)
    (T : {T : Finset κ // T.Nonempty}) :
    ((quittingCoalitionEquiv e).symm T : Finset ι) = T.1.map e.symm.toEmbedding :=
  rfl

/-- Transport a quitting terminal reward table along a player equivalence. -/
def quittingRewardReindex (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    {T : Finset κ // T.Nonempty} → Payoff κ :=
  fun T j => reward ((quittingCoalitionEquiv e).symm T) (e.symm j)

/-- Evaluation of a transported quitting reward table. -/
@[simp] theorem quittingRewardReindex_apply (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (T : {T : Finset κ // T.Nonempty}) (j : κ) :
    quittingRewardReindex e reward T j =
      reward ((quittingCoalitionEquiv e).symm T) (e.symm j) :=
  rfl

/-- Transport a payoff vector along a player equivalence. -/
def quittingPayoffReindex (e : ι ≃ κ) (payoff : Payoff ι) : Payoff κ :=
  fun who => payoff (e.symm who)

/-- Transport a Boolean product root along a player equivalence. -/
def quittingRootReindex (e : ι ≃ κ) (root : ι → PMF Bool) : κ → PMF Bool :=
  fun who => root (e.symm who)

@[simp] theorem quittingPayoffReindex_apply (e : ι ≃ κ)
    (payoff : Payoff ι) (who : κ) :
    quittingPayoffReindex e payoff who = payoff (e.symm who) :=
  rfl

@[simp] theorem quittingRootReindex_apply (e : ι ≃ κ)
    (root : ι → PMF Bool) (who : κ) :
    quittingRootReindex e root who = root (e.symm who) :=
  rfl

/-- Transport of joint Quit/Continue actions along a player equivalence. -/
def quittingActEquiv (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) where
  toFun action := fun who => action (e.symm who)
  invFun action := fun who => action (e who)
  left_inv action := by
    funext who
    simp
  right_inv action := by
    funext who
    simp

@[simp] theorem quittingActEquiv_apply (e : ι ≃ κ)
    (action : ι → Bool) (who : κ) :
    quittingActEquiv e action who = action (e.symm who) :=
  rfl

@[simp] theorem quittingActEquiv_symm_apply (e : ι ≃ κ)
    (action : κ → Bool) (who : ι) :
    (quittingActEquiv e).symm action who = action (e who) :=
  rfl

section Finite

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Reindexing maps the quitter set along the player equivalence. -/
theorem quittingQuitters_reindex (e : ι ≃ κ) (action : ι → Bool) :
    quittingQuitters (quittingActEquiv e action) =
      (quittingQuitters action).map e.toEmbedding := by
  refine Finset.ext fun who => ?_
  simp [quittingQuitters, Finset.mem_map_equiv]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Compatibility name used by the behavioral player-reindex layer. -/
theorem quittingActEquiv_quitterSet (e : ι ≃ κ) (action : ι → Bool) :
    Finset.filter (fun who => quittingActEquiv e action who = true) Finset.univ =
      (Finset.filter (fun who => action who = true) Finset.univ).map
        e.toEmbedding :=
  quittingQuitters_reindex e action

omit [DecidableEq ι] [DecidableEq κ] in
private theorem pmfPi_map_quittingActEquiv
    (e : ι ≃ κ) (root : ι → PMF Bool) :
    PMF.map (quittingActEquiv e) (pmfPi root) =
      pmfPi (quittingRootReindex e root) := by
  exact pmfPi_map_precompEquiv e (quittingActEquiv e) (fun _ _ => rfl) root

omit [DecidableEq ι] [DecidableEq κ] in
private theorem quittingRootPayoff_reindex_at_apply
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (action : ι → Bool) (who : ι) :
    quittingRootPayoff (quittingRewardReindex e reward)
        (quittingPayoffReindex e tail) (quittingActEquiv e action) (e who) =
      quittingRootPayoff reward tail action who := by
  unfold quittingRootPayoff
  rw [quittingQuitters_reindex]
  by_cases hquit : (quittingQuitters action).Nonempty
  · have hmap : ((quittingQuitters action).map e.toEmbedding).Nonempty :=
      Finset.map_nonempty.mpr hquit
    rw [dif_pos hquit, dif_pos hmap]
    simp only [quittingRewardReindex_apply, Equiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    ext player
    simp [Finset.mem_map_equiv]
  · have hmap : ¬ ((quittingQuitters action).map e.toEmbedding).Nonempty :=
      fun h => hquit (Finset.map_nonempty.mp h)
    rw [dif_neg hquit, dif_neg hmap]
    simp

omit [DecidableEq ι] [DecidableEq κ] in
/-- One-stage quitting payoffs commute with player reindexing. -/
theorem quittingRootPayoff_reindex
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (action : ι → Bool) (who : κ) :
    quittingRootPayoff (quittingRewardReindex e reward)
        (quittingPayoffReindex e tail) (quittingActEquiv e action) who =
      quittingRootPayoff reward tail action (e.symm who) := by
  simpa using quittingRootPayoff_reindex_at_apply e reward tail action (e.symm who)

omit [DecidableEq ι] [DecidableEq κ] in
/-- Expected root payoffs commute with player reindexing. -/
theorem quittingRootExpectedPayoff_reindex
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : κ) :
    quittingRootExpectedPayoff (quittingRewardReindex e reward)
        (quittingPayoffReindex e tail) (quittingRootReindex e root) who =
      quittingRootExpectedPayoff reward tail root (e.symm who) := by
  unfold quittingRootExpectedPayoff
  rw [← pmfPi_map_quittingActEquiv e root, expect_map]
  apply congrArg (expect (pmfPi root))
  funext action
  exact quittingRootPayoff_reindex e reward tail action who

omit [Fintype ι] [Fintype κ] in
/-- Reindexing commutes with replacement of one marginal. -/
theorem quittingRootReindex_update (e : ι ≃ κ)
    (root : ι → PMF Bool) (who : ι) (marginal : PMF Bool) :
    quittingRootReindex e (Function.update root who marginal) =
      Function.update (quittingRootReindex e root) (e who) marginal := by
  funext other
  by_cases hother : other = e who
  · subst other
    simp
  · have hpreimage : e.symm other ≠ who := by
      intro h
      apply hother
      simpa using congrArg e h
    simp [quittingRootReindex, Function.update_of_ne hpreimage,
      Function.update_of_ne hother]

/-- Quit-minus-Continue endpoint gains commute with player reindexing. -/
theorem quittingRootEndpointDifference_reindex
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : κ) :
    quittingRootEndpointDifference (quittingRewardReindex e reward)
        (quittingPayoffReindex e tail) (quittingRootReindex e root) who =
      quittingRootEndpointDifference reward tail root (e.symm who) := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  have htrue := quittingRootReindex_update e root (e.symm who) (PMF.pure true)
  have hfalse := quittingRootReindex_update e root (e.symm who) (PMF.pure false)
  rw [Equiv.apply_symm_apply] at htrue hfalse
  rw [← htrue, ← hfalse,
    quittingRootExpectedPayoff_reindex,
    quittingRootExpectedPayoff_reindex]

/-- Exact root Nash is invariant under a player relabeling. -/
theorem isZeroQuittingRootNash_reindex_iff
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    IsεQuittingRootNash (quittingRewardReindex e reward)
        (quittingPayoffReindex e tail) 0 (quittingRootReindex e root) ↔
      IsεQuittingRootNash reward tail 0 root := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash,
    ← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  constructor
  · intro hnash who
    have hwho := hnash (e who)
    simpa [quittingRootEndpointDifference_reindex] using hwho
  · intro hnash who
    have hwho := hnash (e.symm who)
    simpa [quittingRootEndpointDifference_reindex] using hwho

omit [DecidableEq ι] [DecidableEq κ] in
/-- Joint absorption mass is invariant under player relabeling. -/
theorem quittingRootAbsorptionMass_reindex
    (e : ι ≃ κ) (root : ι → PMF Bool) :
    quittingRootAbsorptionMass (quittingRootReindex e root) =
      quittingRootAbsorptionMass root := by
  rw [quittingRootAbsorptionMass, quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  congr 1
  exact (Fintype.prod_equiv e
    (fun who => ((root who) false).toReal)
    (fun who => ((quittingRootReindex e root who) false).toReal)
    (fun who => by simp)).symm

end Finite

end GameTheory
