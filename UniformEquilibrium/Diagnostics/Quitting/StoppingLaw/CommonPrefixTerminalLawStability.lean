import UniformEquilibrium.Quitting.Root.CommonPrefixCapStability
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-!
# Terminal-law stability behind an almost-silent finite word

A finite literal root word perturbs every complete terminal-outcome
coordinate by at most twice its total absorption probability.  Consequently
joint survival tending to one transports convergence of complete terminal
laws.  The suffix and word may both vary with the sequence index.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem quittingRootCoalitionMass_le_one_sub_continueMass
    (root : ι → PMF Bool)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingRootCoalitionMass root terminal.val ≤
      1 - quittingStationaryContinueMass root := by
  rw [← quittingRootCoalitionMass_sum_nonempty root]
  apply Finset.single_le_sum
  · intro coalition _
    exact quittingRootCoalitionMass_nonneg root coalition
  · simp [terminal.property.ne_empty]

/-- Every complete outcome coordinate changes by at most twice the
absorption probability of the inserted finite word. -/
theorem abs_quittingTerminalOutcomeMass_literalRootStack_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (profile : (quittingGame reward).BehaviorProfile)
    (outcome : QuittingTerminalOutcome ι) :
    |quittingTerminalOutcomeMass reward
          (quittingLiteralRootStackProfile reward roots profile) outcome -
        quittingTerminalOutcomeMass reward profile outcome| ≤
      2 * (1 - quittingLiteralRootStackJointSurvival roots) := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival]
  | cons root roots ih =>
      let continuation :=
        quittingLiteralRootStackProfile reward roots profile
      let rootContinue := quittingStationaryContinueMass root
      let wordContinue := quittingLiteralRootStackJointSurvival roots
      let tailMass := quittingTerminalOutcomeMass reward profile outcome
      have hroot0 : 0 ≤ rootContinue :=
        quittingStationaryContinueMass_nonneg root
      have hroot1 : rootContinue ≤ 1 :=
        quittingStationaryContinueMass_le_one root
      have hword0 : 0 ≤ wordContinue :=
        quittingLiteralRootStackJointSurvival_nonneg roots
      have hword1 : wordContinue ≤ 1 :=
        quittingLiteralRootStackJointSurvival_le_one roots
      have htail0 : 0 ≤ tailMass :=
        (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1 outcome
      have htail1 : tailMass ≤ 1 := terminalOutcomeMass_le_one
        (quittingTerminalOutcomeMass reward profile)
        (quittingTerminalOutcomeMass_mem_stdSimplex reward profile) outcome
      rw [quittingLiteralRootStackProfile_cons,
        quittingTerminalOutcomeMass_rootThenContinuation]
      cases outcome with
      | none =>
          change |rootContinue *
                quittingTerminalOutcomeMass reward continuation none -
              tailMass| ≤ 2 * (1 - rootContinue * wordContinue)
          have hdecompose :
              rootContinue *
                    quittingTerminalOutcomeMass reward continuation none -
                  tailMass =
                rootContinue *
                    (quittingTerminalOutcomeMass reward continuation none -
                      tailMass) +
                  (rootContinue - 1) * tailMass := by
            ring
          rw [hdecompose]
          calc
            |rootContinue *
                    (quittingTerminalOutcomeMass reward continuation none -
                      tailMass) +
                  (rootContinue - 1) * tailMass| ≤
                |rootContinue *
                    (quittingTerminalOutcomeMass reward continuation none -
                      tailMass)| + |(rootContinue - 1) * tailMass| :=
              abs_add_le _ _
            _ = rootContinue *
                  |quittingTerminalOutcomeMass reward continuation none -
                    tailMass| + (1 - rootContinue) * tailMass := by
              rw [abs_mul, abs_mul, abs_of_nonneg hroot0,
                abs_of_nonneg htail0, abs_of_nonpos (sub_nonpos.mpr hroot1)]
              ring
            _ ≤ rootContinue * (2 * (1 - wordContinue)) +
                  (1 - rootContinue) * tailMass := by
              gcongr
            _ ≤ 2 * (1 - rootContinue * wordContinue) := by
              nlinarith
      | some terminal =>
          let rootMass := quittingRootCoalitionMass root terminal.val
          have hrootMass0 : 0 ≤ rootMass :=
            quittingRootCoalitionMass_nonneg root terminal.val
          have hrootMass1 : rootMass ≤ 1 - rootContinue :=
            quittingRootCoalitionMass_le_one_sub_continueMass root terminal
          have hdecompose :
              rootMass + rootContinue *
                    quittingTerminalOutcomeMass reward continuation
                      (some terminal) - tailMass =
                rootMass +
                  (rootContinue *
                    (quittingTerminalOutcomeMass reward continuation
                      (some terminal) - tailMass) +
                    (rootContinue - 1) * tailMass) := by
            ring
          change |rootMass + rootContinue *
                quittingTerminalOutcomeMass reward continuation
                  (some terminal) - tailMass| ≤ _
          rw [hdecompose]
          calc
            |rootMass +
                  (rootContinue *
                    (quittingTerminalOutcomeMass reward continuation
                      (some terminal) - tailMass) +
                    (rootContinue - 1) * tailMass)| ≤
                |rootMass| +
                  (|rootContinue *
                    (quittingTerminalOutcomeMass reward continuation
                      (some terminal) - tailMass)| +
                    |(rootContinue - 1) * tailMass|) := by
              exact (abs_add_le _ _).trans
                (add_le_add le_rfl (abs_add_le _ _))
            _ = rootMass + rootContinue *
                  |quittingTerminalOutcomeMass reward continuation
                    (some terminal) - tailMass| +
                  (1 - rootContinue) * tailMass := by
              rw [abs_of_nonneg hrootMass0, abs_mul, abs_mul,
                abs_of_nonneg hroot0, abs_of_nonneg htail0,
                abs_of_nonpos (sub_nonpos.mpr hroot1)]
              ring
            _ ≤ rootMass + rootContinue * (2 * (1 - wordContinue)) +
                  (1 - rootContinue) * tailMass := by
              gcongr
            _ ≤ 2 * (1 - rootContinue * wordContinue) := by
              nlinarith

/-- Vanishing absorption in varying finite words transports coordinatewise
convergence of varying complete terminal laws. -/
theorem tendsto_quittingTerminalOutcomeMass_literalRootStack_of_joint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool))
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (law : QuittingTerminalOutcome ι → ℝ)
    (hsurvival : Tendsto (fun rank ↦
      quittingLiteralRootStackJointSurvival (roots rank)) atTop (nhds 1))
    (hlaw : Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward (profiles rank)) atTop (nhds law)) :
    Tendsto (fun rank ↦ quittingTerminalOutcomeMass reward
      (quittingLiteralRootStackProfile reward (roots rank) (profiles rank)))
      atTop (nhds law) := by
  apply tendsto_pi_nhds.mpr
  intro outcome
  have htail := (continuous_apply outcome).tendsto law |>.comp hlaw
  have hgap : Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward
          (quittingLiteralRootStackProfile reward (roots rank)
            (profiles rank)) outcome -
        quittingTerminalOutcomeMass reward (profiles rank) outcome)
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    have hbound : Tendsto (fun rank ↦
        2 * ((1 : ℝ) -
          quittingLiteralRootStackJointSurvival (roots rank)))
        atTop (nhds 0) := by
      have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      simpa using (hone.sub hsurvival).const_mul 2
    exact squeeze_zero (fun _ ↦ abs_nonneg _)
      (fun rank ↦
        abs_quittingTerminalOutcomeMass_literalRootStack_sub_le
          reward (roots rank) (profiles rank) outcome)
      hbound
  have hsum := hgap.add htail
  convert hsum using 1
  · funext rank
    simp only [Function.comp_apply]
    ring
  · simp

end GameTheory
