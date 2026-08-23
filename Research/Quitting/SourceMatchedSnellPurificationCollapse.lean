/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.SourceMatchedSnellPurification
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable

/-!
# The source-matched Snell-purification interface admits regime-free candidates

`Research/Quitting/SourceMatchedSnellPurification.lean` states an open
face-enlargement interface: every certified candidate carrying a schedule must
yield either a uniform-equilibrium payoff or a certified candidate with a
strictly larger source face.  This module records two checked facts that limit
what proving that interface could buy.

**Free padding.**  The candidate's `selected_support` field bounds activity
*above* by `face`; no field forces a face member to be active.  So
`SourceMatchedSnellCandidate.padFace` re-certifies any candidate verbatim with
one extra face member, and `sourceMatchedSnellStep_of_not_mem_face` discharges
`SourceMatchedSnellStep` for every candidate whose face is not already
`Finset.univ.erase owner` -- with no equilibrium produced and no new
certification work.  The finite-face induction of
`exists_uniformPayoff_of_sourceMatchedSnellCandidate` therefore carries no
content on its own: only the maximal-face case can force the equilibrium
branch.

**A regime-free certified candidate.**  `svCandidate` and `svSchedule` are a
fully explicit candidate and schedule on the Solan--Vieille boundary table of
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`: player
`1` quits alone at rate `(t + 2)⁻²`, everyone else continues purely, the
annotation is `value t = E t • reward {1} + s t • boundary` with
`boundary = ![1, 1, 2, 2]`, `E t = (t + 2)⁻¹`, `s t = (t + 1) / (t + 2)`, and
the owner is player `2`.  Every certification field is proved here -- the exact
policy recursion, exact endpoint Nash at every date, positive remaining
absorption, the vanishing conditioned mesh, and the conditioned box -- and the
conditioned value is the constant singleton row `reward {1} = ![4, 1, 0, 0]`.
The rescaled owner endpoint gap is exactly `1` at every date
(`svRescaledEndpointDifference_owner`), so the schedule assembles with
`endpoint_eta = 2`.

No terminal exploitability witness, seam witness, minmax datum, or debt provenance is
consumed anywhere in that construction; the only input is "player `1` can quit
alone, and player `2` is paid `0` by that exit".  Consequently
`uniformPayoff_solanVieilleBoundary_of_purification` is checked: assuming
`SourceMatchedSnellPurification` for `boundaryReward` yields a
uniform-equilibrium payoff for that table.

Two honesty caveats.  This module does not decide whether the Solan--Vieille
table has such a payoff, and therefore does not refute the interface.  Its
theorems show that an implementation of the interface cannot be powered by
data from a terminal exploitability witness reaching it through the candidate, because the
interface certifies candidates carrying no such data.  The proposition
definition `SourceMatchedSnellCandidateFromPreemptionEdge` generalizes
`svCandidate` from the Solan--Vieille table to every reward carrying a strict
solo-preemption edge.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

/-! ## Face enlargement is free padding -/

section FreeEnlargement

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Re-certify a candidate verbatim with one extra source-face member.  Only
`face` changes: `selected_support` bounds activity above by the face, so a
larger face is never a stronger requirement. -/
def SourceMatchedSnellCandidate.padFace
    (c : SourceMatchedSnellCandidate reward) {j : ι} (hj : j ≠ c.owner) :
    SourceMatchedSnellCandidate reward where
  roots := c.roots
  value := c.value
  boundary := c.boundary
  face := insert j c.face
  owner := c.owner
  owner_not_mem_face := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => hj h.symm, c.owner_not_mem_face⟩
  positive := c.positive
  mesh_tendsto := c.mesh_tendsto
  policy := c.policy
  endpoint_nash := c.endpoint_nash
  conditioned_bound := c.conditioned_bound

@[simp] theorem SourceMatchedSnellCandidate.padFace_face
    (c : SourceMatchedSnellCandidate reward) {j : ι} (hj : j ≠ c.owner) :
    (c.padFace hj).face = insert j c.face := rfl

/-- The same schedule certifies the padded candidate. -/
def SourceMatchedSnellSchedule.padFace
    {c : SourceMatchedSnellCandidate reward}
    (schedule : SourceMatchedSnellSchedule c) {j : ι} (hj : j ≠ c.owner) :
    SourceMatchedSnellSchedule (c.padFace hj) where
  time := schedule.time
  theta := schedule.theta
  strictMono := schedule.strictMono
  theta_pos := schedule.theta_pos
  theta_le_one := schedule.theta_le_one
  theta_tendsto_zero := schedule.theta_tendsto_zero
  theta_not_summable := schedule.theta_not_summable
  selected_mesh_bound := schedule.selected_mesh_bound
  endpoint_eta := schedule.endpoint_eta
  endpoint_eta_pos := schedule.endpoint_eta_pos
  selected_endpoint_gap := schedule.selected_endpoint_gap
  selected_support := fun n player hplayer =>
    Finset.mem_insert_of_mem (schedule.selected_support n player hplayer)

/-- **Free enlargement.**  A candidate whose face omits one non-owner already
satisfies the interface's second disjunct, with no equilibrium produced and no
new certification work. -/
theorem sourceMatchedSnellStep_of_not_mem_face
    {c : SourceMatchedSnellCandidate reward}
    (schedule : SourceMatchedSnellSchedule c) {j : ι}
    (hface : j ∉ c.face) (howner : j ≠ c.owner) :
    SourceMatchedSnellStep c :=
  Or.inr ⟨c.padFace howner, ⟨schedule.padFace howner⟩,
    Finset.ssubset_insert hface⟩

/-- Every non-maximal face discharges the step.  Hence the whole content of
`SourceMatchedSnellPurification` sits at `face = Finset.univ.erase owner`,
where the enlargement branch is unavailable. -/
theorem sourceMatchedSnellStep_of_face_ssubset
    {c : SourceMatchedSnellCandidate reward}
    (schedule : SourceMatchedSnellSchedule c)
    (hface : c.face ⊂ Finset.univ.erase c.owner) :
    SourceMatchedSnellStep c := by
  obtain ⟨j, hjmem, hjface⟩ := Finset.exists_of_ssubset hface
  exact sourceMatchedSnellStep_of_not_mem_face schedule hjface
    (Finset.ne_of_mem_erase hjmem)

/-- The edge-local assembly proposition: a strict solo-preemption edge alone
assembles a certified candidate with a schedule, with no data from a terminal exploitability witness
input.  `svCandidate` proves its Solan--Vieille instance. -/
def SourceMatchedSnellCandidateFromPreemptionEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ quitter owner : ι, QuittingSoloPreempts reward 1 quitter owner →
    ∃ c : SourceMatchedSnellCandidate reward,
      Nonempty (SourceMatchedSnellSchedule c) ∧ c.owner = owner ∧
        c.face = {quitter}

end FreeEnlargement

/-! ## An explicit regime-free candidate on the Solan--Vieille table -/

namespace SourceMatchedSnellCollapse

open SolanVieilleBoundary

/-- The lone active player: `1` quits alone at every date. -/
def quitter : Player := 1

/-- The schedule's owner: `1`'s solo exit pays player `2` nothing, while `2`'s
own solo exit pays it `1`. -/
def owner : Player := 2

theorem owner_preempted :
    QuittingSoloPreempts boundaryReward 1 quitter owner :=
  (soloPreempts_iff quitter owner).2 (Or.inl (by decide))

theorem spectator_cases : ∀ p : Player, p ≠ quitter → p = 0 ∨ p = 2 ∨ p = 3 := by
  decide

/-! ### The solo hazard tail -/

/-- The solo hazard `(t + 2)⁻²`.  Its remaining eventual absorption is exactly
`(t + 2)⁻¹`, so the conditioned mesh is `(t + 2)⁻¹` and vanishes. -/
def svHazard (t : ℕ) : ℝ := 1 / ((t : ℝ) + 2) ^ 2

theorem svHazard_nonneg (t : ℕ) : 0 ≤ svHazard t := by
  unfold svHazard
  positivity

theorem svHazard_le_one (t : ℕ) : svHazard t ≤ 1 := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hpos : (0 : ℝ) < ((t : ℝ) + 2) ^ 2 := by positivity
  rw [svHazard, div_le_one hpos]
  nlinarith

/-- The root tail: `quitter` quits at rate `svHazard`, everyone else continues
purely. -/
def svRoots (t : ℕ) : Player → PMF Bool := fun player =>
  if player = quitter then
    quittingHazardCoin (svHazard t) (svHazard_nonneg t) (svHazard_le_one t)
  else PMF.pure false

theorem svRoots_of_ne (t : ℕ) {player : Player} (h : player ≠ quitter) :
    svRoots t player = PMF.pure false := by
  simp [svRoots, h]

theorem svRoots_active (t : ℕ) :
    IsQuittingActiveRoot ({quitter} : Finset Player) (svRoots t) := by
  intro player hplayer
  exact svRoots_of_ne t (by simpa using hplayer)

theorem hazardOfRoot_svRoots_quitter (t : ℕ) :
    hazardOfRoot (svRoots t) quitter = svHazard t := by
  simp [hazardOfRoot, svRoots]

theorem svContinueMass (t : ℕ) :
    quittingStationaryContinueMass (svRoots t) = 1 - svHazard t := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_four]
  norm_num [svRoots, quitter, Fin.ext_iff]

theorem svAbsorptionMass (t : ℕ) :
    quittingRootAbsorptionMass (svRoots t) = svHazard t := by
  rw [quittingRootAbsorptionMass, svContinueMass]
  ring

/-! ### The exact survival calculus -/

theorem svJointSurvivalWeight (t fuel : ℕ) :
    quittingJointSurvivalWeight svRoots t fuel =
      ((t : ℝ) + 1) * ((t : ℝ) + fuel + 2) /
        (((t : ℝ) + 2) * ((t : ℝ) + fuel + 1)) := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  induction fuel with
  | zero =>
      rw [quittingJointSurvivalWeight_eq_prod]
      have h1 : (t : ℝ) + 2 ≠ 0 := by positivity
      have h2 : (t : ℝ) + 1 ≠ 0 := by positivity
      simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, add_zero]
      field_simp
  | succ fuel ih =>
      have hfuel : (0 : ℝ) ≤ (fuel : ℝ) := Nat.cast_nonneg fuel
      have hcast : ((t + fuel : ℕ) : ℝ) = (t : ℝ) + (fuel : ℝ) := by
        push_cast
        ring
      rw [quittingJointSurvivalWeight_succ, ih, svContinueMass, svHazard, hcast]
      have h1 : (t : ℝ) + 2 ≠ 0 := by positivity
      have h2 : (t : ℝ) + fuel + 1 ≠ 0 := by positivity
      have h3 : (t : ℝ) + fuel + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem svJointSurvivalLimit (t : ℕ) :
    quittingJointSurvivalLimit svRoots t = ((t : ℝ) + 1) / ((t : ℝ) + 2) := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hbig : Tendsto (fun fuel : ℕ => (t : ℝ) + fuel + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ _
      (Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun fuel : ℕ => ((t : ℝ) + fuel + 1)⁻¹) atTop (nhds 0) :=
    hbig.inv_tendsto_atTop
  have heq : (fun fuel : ℕ => quittingJointSurvivalWeight svRoots t fuel) =
      fun fuel : ℕ => ((t : ℝ) + 1) / ((t : ℝ) + 2) +
        ((t : ℝ) + 1) / ((t : ℝ) + 2) * ((t : ℝ) + fuel + 1)⁻¹ := by
    funext fuel
    have hfuel : (0 : ℝ) ≤ (fuel : ℝ) := Nat.cast_nonneg fuel
    have h1 : (t : ℝ) + 2 ≠ 0 := by positivity
    have h2 : (t : ℝ) + fuel + 1 ≠ 0 := by positivity
    rw [svJointSurvivalWeight]
    field_simp
    ring
  have hlimit : Tendsto (fun fuel : ℕ => quittingJointSurvivalWeight svRoots t fuel)
      atTop (nhds (((t : ℝ) + 1) / ((t : ℝ) + 2))) := by
    rw [heq]
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  exact tendsto_nhds_unique (tendsto_quittingJointSurvivalLimit svRoots t) hlimit

theorem svEventualAbsorption (t : ℕ) :
    quittingTailEventualAbsorption svRoots t = 1 / ((t : ℝ) + 2) := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have h1 : (t : ℝ) + 2 ≠ 0 := by positivity
  rw [quittingTailEventualAbsorption, svJointSurvivalLimit]
  field_simp
  ring

theorem svEventualAbsorption_pos (t : ℕ) :
    0 < quittingTailEventualAbsorption svRoots t := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  rw [svEventualAbsorption]
  positivity

theorem svConditionedAbsorptionWeight (t : ℕ) :
    quittingTailConditionedAbsorptionWeight svRoots t = 1 / ((t : ℝ) + 2) := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have h1 : (t : ℝ) + 2 ≠ 0 := by positivity
  rw [quittingTailConditionedAbsorptionWeight, svAbsorptionMass,
    svEventualAbsorption, svHazard]
  field_simp

theorem svConditionedAbsorptionWeight_tendsto :
    Tendsto (quittingTailConditionedAbsorptionWeight svRoots) atTop (nhds 0) := by
  have heq : quittingTailConditionedAbsorptionWeight svRoots =
      fun t : ℕ => 1 / ((t : ℝ) + 2) := funext svConditionedAbsorptionWeight
  rw [heq]
  have hbig : Tendsto (fun t : ℕ => (t : ℝ) + 2) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.congr (fun t => (one_div ((t : ℝ) + 2)).symm)
    hbig.inv_tendsto_atTop

/-! ### The annotation -/

/-- The singleton row delivered by `quitter`'s solo exit: `![4, 1, 0, 0]`. -/
def svQuitReward : Payoff Player :=
  boundaryReward ⟨{quitter}, Finset.singleton_nonempty quitter⟩

/-- The phantom boundary.  No candidate field bounds it; the value `2` in the
spectator coordinates is what makes exact endpoint Nash hold from date `0`
onwards, with no finite prefix discarded. -/
def svBoundary : Payoff Player := ![1, 1, 2, 2]

/-- The annotation `value t = E t • reward {quitter} + s t • boundary`, written
out with `E t = (t + 2)⁻¹` and `s t = (t + 1) / (t + 2)`. -/
def svValue (t : ℕ) : Payoff Player := fun who =>
  (svQuitReward who + ((t : ℝ) + 1) * svBoundary who) / ((t : ℝ) + 2)

theorem svQuitReward_quitter : svQuitReward quitter = 1 := rfl

theorem svQuitReward_owner : svQuitReward owner = 0 := rfl

theorem svValue_quitter (t : ℕ) : svValue t quitter = 1 := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have h1 : (t : ℝ) + 2 ≠ 0 := by positivity
  have hboundary : svBoundary quitter = 1 := rfl
  rw [svValue, svQuitReward_quitter, hboundary]
  field_simp
  ring

theorem one_le_svValue_spectator (t : ℕ) {who : Player} (hne : who ≠ quitter) :
    1 ≤ svValue t who := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have h2 : (0 : ℝ) < (t : ℝ) + 2 := by positivity
  rw [svValue, le_div_iff₀ h2]
  rcases spectator_cases who hne with rfl | rfl | rfl
  · rw [show svQuitReward 0 = 4 from rfl, show svBoundary 0 = 1 from rfl]
    linarith
  · rw [show svQuitReward 2 = 0 from rfl, show svBoundary 2 = 2 from rfl]
    linarith
  · rw [show svQuitReward 3 = 0 from rfl, show svBoundary 3 = 2 from rfl]
    linarith

/-- The one-stage successor of the annotation: a singleton-active affine step. -/
theorem svSuccessor (t : ℕ) (who : Player) :
    quittingRootSuccessorPayoff boundaryReward (svValue (t + 1)) (svRoots t) who =
      (1 - svHazard t) * svValue (t + 1) who + svHazard t * svQuitReward who := by
  rw [show quittingRootSuccessorPayoff boundaryReward (svValue (t + 1))
      (svRoots t) who =
    quittingRootExpectedPayoff boundaryReward (svValue (t + 1))
      (svRoots t) who from rfl,
    quittingRootExpectedPayoff_singleton_active boundaryReward
      (svValue (t + 1)) (svRoots t) quitter who (svRoots_active t),
    hazardOfRoot_svRoots_quitter]
  rfl

/-- **Exact policy recursion.**  It holds for the whole affine family, whatever
the singleton row and the boundary are. -/
theorem svPolicy (t : ℕ) :
    svValue t =
      quittingRootSuccessorPayoff boundaryReward (svValue (t + 1)) (svRoots t) := by
  funext who
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have h2 : (t : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (t : ℝ) + 1 + 2 ≠ 0 := by positivity
  rw [svSuccessor, svValue, svValue, svHazard]
  push_cast
  field_simp
  ring

/-! ### Exact endpoint Nash at every date -/

theorem svQuitPayoff_quitter (t : ℕ) (tail : Payoff Player) :
    quittingRootQuitPayoff boundaryReward tail (svRoots t) quitter =
      svQuitReward quitter := by
  have hactive : IsQuittingActiveRoot ({quitter} : Finset Player)
      (Function.update (svRoots t) quitter (PMF.pure true)) := by
    intro player hplayer
    have hne : player ≠ quitter := by simpa using hplayer
    rw [Function.update_of_ne hne]
    exact svRoots_of_ne t hne
  have hhazard : hazardOfRoot
      (Function.update (svRoots t) quitter (PMF.pure true)) quitter = 1 := by
    simp [hazardOfRoot]
  rw [quittingRootQuitPayoff,
    quittingRootExpectedPayoff_singleton_active boundaryReward tail _ quitter
      quitter hactive, hhazard]
  simp [svQuitReward]

theorem svContinuePayoff_quitter (t : ℕ) (tail : Payoff Player) :
    quittingRootContinuePayoff boundaryReward tail (svRoots t) quitter =
      tail quitter := by
  have hactive : IsQuittingActiveRoot ({quitter} : Finset Player)
      (Function.update (svRoots t) quitter (PMF.pure false)) := by
    intro player hplayer
    have hne : player ≠ quitter := by simpa using hplayer
    rw [Function.update_of_ne hne]
    exact svRoots_of_ne t hne
  have hhazard : hazardOfRoot
      (Function.update (svRoots t) quitter (PMF.pure false)) quitter = 0 := by
    simp [hazardOfRoot]
  rw [quittingRootContinuePayoff,
    quittingRootExpectedPayoff_singleton_active boundaryReward tail _ quitter
      quitter hactive, hhazard]
  ring

theorem svQuitPayoff_spectator (t : ℕ) (tail : Payoff Player) {who : Player}
    (hne : who ≠ quitter) :
    quittingRootQuitPayoff boundaryReward tail (svRoots t) who =
      (1 - svHazard t) *
          boundaryReward ⟨{who}, Finset.singleton_nonempty who⟩ who +
        svHazard t * boundaryReward ⟨{quitter, who}, by simp⟩ who := by
  have hactive : IsQuittingActiveRoot ({quitter, who} : Finset Player)
      (Function.update (svRoots t) who (PMF.pure true)) := by
    intro player hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hplayer
    rw [Function.update_of_ne hplayer.2]
    exact svRoots_of_ne t hplayer.1
  have hfirst : hazardOfRoot
      (Function.update (svRoots t) who (PMF.pure true)) quitter = svHazard t := by
    show ((Function.update (svRoots t) who (PMF.pure true)) quitter true).toReal =
      svHazard t
    rw [Function.update_of_ne (Ne.symm hne)]
    exact hazardOfRoot_svRoots_quitter t
  have hsecond : hazardOfRoot
      (Function.update (svRoots t) who (PMF.pure true)) who = 1 := by
    simp [hazardOfRoot]
  rw [quittingRootQuitPayoff,
    quittingRootExpectedPayoff_pair_active boundaryReward tail _ quitter who who
      (Ne.symm hne) hactive, hfirst, hsecond]
  ring

theorem svContinuePayoff_spectator (t : ℕ) (tail : Payoff Player) {who : Player}
    (hne : who ≠ quitter) :
    quittingRootContinuePayoff boundaryReward tail (svRoots t) who =
      (1 - svHazard t) * tail who + svHazard t * svQuitReward who := by
  have hactive : IsQuittingActiveRoot ({quitter} : Finset Player)
      (Function.update (svRoots t) who (PMF.pure false)) := by
    intro player hplayer
    have hplayerne : player ≠ quitter := by simpa using hplayer
    by_cases hpwho : player = who
    · subst hpwho
      simp
    · rw [Function.update_of_ne hpwho]
      exact svRoots_of_ne t hplayerne
  have hhazard : hazardOfRoot
      (Function.update (svRoots t) who (PMF.pure false)) quitter = svHazard t := by
    show ((Function.update (svRoots t) who (PMF.pure false)) quitter true).toReal =
      svHazard t
    rw [Function.update_of_ne (Ne.symm hne)]
    exact hazardOfRoot_svRoots_quitter t
  rw [quittingRootContinuePayoff,
    quittingRootExpectedPayoff_singleton_active boundaryReward tail _ quitter who
      hactive, hhazard]
  rw [show boundaryReward ⟨{quitter}, Finset.singleton_nonempty quitter⟩ who =
    svQuitReward who from rfl]

theorem svEndpointDifference_quitter (t : ℕ) :
    quittingRootEndpointDifference boundaryReward (svValue (t + 1)) (svRoots t)
      quitter = 0 := by
  rw [quittingRootEndpointDifference, svQuitPayoff_quitter,
    svContinuePayoff_quitter, svValue_quitter, svQuitReward_quitter]
  ring

/-- A spectator's Continue endpoint is the prescribed value itself, so its
endpoint difference is the collision-corrected solo grab minus that value. -/
theorem svEndpointDifference_spectator (t : ℕ) {who : Player}
    (hne : who ≠ quitter) :
    quittingRootEndpointDifference boundaryReward (svValue (t + 1)) (svRoots t)
        who =
      ((1 - svHazard t) *
            boundaryReward ⟨{who}, Finset.singleton_nonempty who⟩ who +
          svHazard t * boundaryReward ⟨{quitter, who}, by simp⟩ who) -
        svValue t who := by
  rw [quittingRootEndpointDifference, svQuitPayoff_spectator _ _ hne,
    svContinuePayoff_spectator _ _ hne, ← svSuccessor, ← svPolicy]

theorem svSpectatorSelfReward (who : Player) :
    boundaryReward ⟨{who}, Finset.singleton_nonempty who⟩ who = 1 :=
  soloReward_self who

theorem svSpectatorPairReward {who : Player} (hne : who ≠ quitter) :
    boundaryReward ⟨{quitter, who}, by simp⟩ who = 1 := by
  rcases spectator_cases who hne with rfl | rfl | rfl <;> rfl

theorem svEndpointDifference_spectator_nonpos (t : ℕ) {who : Player}
    (hne : who ≠ quitter) :
    quittingRootEndpointDifference boundaryReward (svValue (t + 1)) (svRoots t)
      who ≤ 0 := by
  rw [svEndpointDifference_spectator t hne, svSpectatorSelfReward,
    svSpectatorPairReward hne,
    show (1 - svHazard t) * 1 + svHazard t * 1 = 1 by ring, sub_nonpos]
  exact one_le_svValue_spectator t hne

theorem svEndpointNash (t : ℕ) :
    IsεQuittingRootEndpointNash boundaryReward (svValue (t + 1)) 0 (svRoots t) := by
  intro who
  by_cases hwho : who = quitter
  · subst hwho
    rw [svEndpointDifference_quitter]
    constructor <;> simp
  · have hquit : (svRoots t who true).toReal = 0 := by
      rw [svRoots_of_ne t hwho]
      simp
    have hcontinue : (svRoots t who false).toReal = 1 := by
      rw [svRoots_of_ne t hwho]
      simp
    refine ⟨?_, ?_⟩
    · rw [hcontinue, one_mul]
      exact svEndpointDifference_spectator_nonpos t hwho
    · rw [hquit, zero_mul, neg_zero]

/-! ### The conditioned tail -/

/-- **The phantom boundary cancels exactly.**  Conditioning on eventual
absorption returns the constant singleton row `reward {quitter}`. -/
theorem svConditionedValue (t : ℕ) :
    quittingTailConditionedValue svRoots svValue svBoundary t = svQuitReward := by
  funext who
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have h2 : (t : ℝ) + 2 ≠ 0 := by positivity
  rw [quittingTailConditionedValue, svJointSurvivalLimit, svEventualAbsorption,
    svValue]
  field_simp
  ring

theorem svConditionedBound (t : ℕ) (player : Player) :
    |quittingTailConditionedValue svRoots svValue svBoundary t player| ≤
      quittingRewardBound boundaryReward := by
  rw [svConditionedValue]
  exact abs_reward_le_quittingRewardBound boundaryReward _ player

/-! ### The diffuse rescaled root and the owner's endpoint gap -/

/-- The conditioned rescaled root at date `t`: `quitter` quits at rate
`(t + 2)⁻¹`, everyone else still continues purely. -/
def svRescaledRoot (t : ℕ) : Player → PMF Bool :=
  quittingTailDiffuseRescaledRoot svRoots t (svEventualAbsorption_pos t)

theorem svRescaledRoot_of_ne (t : ℕ) {player : Player} (h : player ≠ quitter) :
    svRescaledRoot t player = PMF.pure false :=
  quittingTailDiffuseRescaledRoot_eq_pure_false_of_source_eq_pure_false
    svRoots t player (svEventualAbsorption_pos t) (svRoots_of_ne t h)

theorem svRescaledHazard_quitter (t : ℕ) :
    hazardOfRoot (svRescaledRoot t) quitter = 1 / ((t : ℝ) + 2) := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have h2 : (t : ℝ) + 2 ≠ 0 := by positivity
  have hsource : (svRoots t quitter true).toReal = svHazard t :=
    hazardOfRoot_svRoots_quitter t
  rw [show hazardOfRoot (svRescaledRoot t) quitter =
      quittingTailDiffuseRescaledHazard svRoots t quitter from
    congrFun (hazardOfRoot_quittingTailDiffuseRescaledRoot svRoots t
      (svEventualAbsorption_pos t)) quitter,
    quittingTailDiffuseRescaledHazard, hsource, svEventualAbsorption, svHazard]
  field_simp

theorem svRescaledRoot_active (t : ℕ) :
    IsQuittingActiveRoot ({quitter} : Finset Player) (svRescaledRoot t) := by
  intro player hplayer
  exact svRescaledRoot_of_ne t (by simpa using hplayer)

/-- **The owner's rescaled endpoint gap is exactly `1` at every date.**  The
owner is paid `0` by the quitter's solo exit and `1` by its own, and the
collision row `{quitter, owner}` also pays it `1`. -/
theorem svRescaledEndpointDifference_owner (t : ℕ) :
    quittingRootEndpointDifference boundaryReward svQuitReward
      (svRescaledRoot t) owner = 1 := by
  have hne : owner ≠ quitter := by decide
  have hquitActive : IsQuittingActiveRoot ({quitter, owner} : Finset Player)
      (Function.update (svRescaledRoot t) owner (PMF.pure true)) := by
    intro player hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hplayer
    rw [Function.update_of_ne hplayer.2]
    exact svRescaledRoot_of_ne t hplayer.1
  have hquitFirst : hazardOfRoot
      (Function.update (svRescaledRoot t) owner (PMF.pure true)) quitter =
        1 / ((t : ℝ) + 2) := by
    show ((Function.update (svRescaledRoot t) owner (PMF.pure true)) quitter
      true).toReal = 1 / ((t : ℝ) + 2)
    rw [Function.update_of_ne (Ne.symm hne)]
    exact svRescaledHazard_quitter t
  have hquitSecond : hazardOfRoot
      (Function.update (svRescaledRoot t) owner (PMF.pure true)) owner = 1 := by
    simp [hazardOfRoot]
  have hcontinueActive : IsQuittingActiveRoot ({quitter} : Finset Player)
      (Function.update (svRescaledRoot t) owner (PMF.pure false)) := by
    intro player hplayer
    have hplayerne : player ≠ quitter := by simpa using hplayer
    by_cases hpowner : player = owner
    · subst hpowner
      simp
    · rw [Function.update_of_ne hpowner]
      exact svRescaledRoot_of_ne t hplayerne
  have hcontinueHazard : hazardOfRoot
      (Function.update (svRescaledRoot t) owner (PMF.pure false)) quitter =
        1 / ((t : ℝ) + 2) := by
    show ((Function.update (svRescaledRoot t) owner (PMF.pure false)) quitter
      true).toReal = 1 / ((t : ℝ) + 2)
    rw [Function.update_of_ne (Ne.symm hne)]
    exact svRescaledHazard_quitter t
  rw [quittingRootEndpointDifference, quittingRootQuitPayoff,
    quittingRootExpectedPayoff_pair_active boundaryReward svQuitReward _ quitter
      owner owner (Ne.symm hne) hquitActive, hquitFirst, hquitSecond,
    quittingRootContinuePayoff,
    quittingRootExpectedPayoff_singleton_active boundaryReward svQuitReward _
      quitter owner hcontinueActive, hcontinueHazard]
  rw [show boundaryReward ⟨{owner}, Finset.singleton_nonempty owner⟩ owner =
      (1 : ℝ) from soloReward_self owner,
    show boundaryReward ⟨{quitter, owner}, by simp⟩ owner = (1 : ℝ) from rfl,
    show boundaryReward ⟨{quitter}, Finset.singleton_nonempty quitter⟩ owner =
      (0 : ℝ) from rfl, svQuitReward_owner]
  ring

/-! ### The certified candidate and its schedule -/

/-- **The regime-free certified candidate.**  Every field is discharged by the
explicit solo-hazard tail above; no datum from a terminal exploitability witness enters. -/
def svCandidate : SourceMatchedSnellCandidate boundaryReward where
  roots := svRoots
  value := svValue
  boundary := svBoundary
  face := {quitter}
  owner := owner
  owner_not_mem_face := by decide
  positive := svEventualAbsorption_pos
  mesh_tendsto := svConditionedAbsorptionWeight_tendsto
  policy := svPolicy
  endpoint_nash := svEndpointNash
  conditioned_bound := svConditionedBound

/-- The explicit schedule: selected dates `2 ^ n`, harmonic clock, and the
sharp owner gap `endpoint_eta = 2`. -/
def svSchedule : SourceMatchedSnellSchedule svCandidate where
  time := fun n => 2 ^ n
  theta := fun n => 1 / ((n : ℝ) + 1)
  strictMono := by
    intro m n hmn
    exact Nat.pow_lt_pow_right (by norm_num) hmn
  theta_pos := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    positivity
  theta_le_one := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_one (by positivity)]
    linarith
  theta_tendsto_zero := tendsto_one_div_add_atTop_nhds_zero_nat
  theta_not_summable := by
    exact_mod_cast mt (summable_nat_add_iff 1).1 Real.not_summable_one_div_natCast
  selected_mesh_bound := by
    intro n
    have hmesh : quittingTailConditionedAbsorptionWeight svCandidate.roots (2 ^ n) =
        1 / (((2 : ℕ) ^ n : ℕ) + 2 : ℝ) := svConditionedAbsorptionWeight (2 ^ n)
    rw [hmesh]
    have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [div_pow, one_pow]
    push_cast
    exact one_div_le_one_div_of_le hpow (by linarith)
  endpoint_eta := 2
  endpoint_eta_pos := by norm_num
  selected_endpoint_gap := by
    intro n
    rw [show ((2 : ℝ)) / 2 = 1 by norm_num]
    rw [show quittingTailConditionedValue svCandidate.roots svCandidate.value
        svCandidate.boundary (2 ^ n + 1) = svQuitReward from
      svConditionedValue (2 ^ n + 1)]
    exact le_of_eq (svRescaledEndpointDifference_owner (2 ^ n)).symm
  selected_support := by
    intro n player hplayer
    show player ∈ ({quitter} : Finset Player)
    rw [Finset.mem_singleton]
    by_contra hne
    exact hplayer (svRoots_of_ne (2 ^ n) hne)

theorem svCandidate_face : svCandidate.face = {quitter} := rfl

theorem svCandidate_owner : svCandidate.owner = owner := rfl

/-- **The Solan--Vieille rejection witness.**  A fully certified candidate with
a schedule exists on the Solan--Vieille boundary table, with the honest active
support `{1}` as its face and the preempting player `2` as its owner. -/
theorem sourceMatchedSnellCandidate_solanVieilleBoundary :
    ∃ c : SourceMatchedSnellCandidate boundaryReward,
      Nonempty (SourceMatchedSnellSchedule c) ∧ c.owner = owner ∧
        c.face = {quitter} :=
  ⟨svCandidate, ⟨svSchedule⟩, svCandidate_owner, svCandidate_face⟩

/-- The witness discharges the interface's step by free padding alone: player
`0` is outside the face and is not the owner, so the enlargement branch closes
with no equilibrium and no regime input. -/
theorem sourceMatchedSnellStep_svCandidate :
    SourceMatchedSnellStep svCandidate :=
  sourceMatchedSnellStep_of_not_mem_face svSchedule
    (j := (0 : Player)) (by decide) (by decide)

/-- **The interface is at least as strong as the conjecture here.**  Assuming
`SourceMatchedSnellPurification` for the Solan--Vieille table yields a
uniform-equilibrium payoff for that table.  Whether that table has one is not
decided here. -/
theorem uniformPayoff_solanVieilleBoundary_of_purification
    (hinterface : SourceMatchedSnellPurification (reward := boundaryReward)) :
    ∃ payoff : Payoff Player,
      (quittingGame boundaryReward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformPayoff_of_sourceMatchedSnellCandidate hinterface svCandidate
    ⟨svSchedule⟩

end SourceMatchedSnellCollapse

end GameTheory
