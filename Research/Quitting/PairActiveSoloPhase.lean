/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.SoloTailExactStructure
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport

/-!
# Pair-active exact roots and the pointwise solo phase

`quittingRootExpectedPayoff_pair_active`
(`UniformEquilibrium/Quitting/Bellman/Finite/ActiveSetSupport.lean`) evaluates
a root supported on two coordinates exactly.  This module reads the two pure
endpoint payoffs off that formula and extracts what exact endpoint Nash says
when *both* coordinates mix strictly.

* **Pair endpoint payoffs** (`quittingRootQuitPayoff_pair_active`,
  `quittingRootContinuePayoff_pair_active`): closed forms in the two singleton
  rows, the collision row, and the declared continuation.
* **Pair indifference identity**
  (`pairActive_indifference`): at an exact endpoint-Nash pair-active root with
  a strictly mixing coordinate, the continuation's displacement above that
  coordinate's own singleton reward, scaled by the partner's survival mass, is
  the partner's hazard times the coordinate's collision increment.  Exact, with
  no asymptotics.
* **Pointwise solo phase**
  (`hazardOfRoot_eq_zero_of_pairActive_of_collisionIncrement_ne_zero`,
  `isQuittingSoloRoot_of_pairActive_of_collisionIncrement_ne_zero`): if in
  addition the continuation already pays the coordinate its own singleton
  reward — the pin that a solo date supplies for free — then the partner's
  hazard vanishes outright on a table where joining the partner's exit changes
  what the coordinate receives, so the root is a solo root at the mixing
  coordinate and the partner surely continues.

The table condition here is `QuittingPairCollisionNondegenerate`, a condition
on collision rows.  It is independent of the zero-freeness of the normalized
solo matrix, which is a condition on singleton rows.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## The collision row in singleton-collision vocabulary -/

omit [Fintype ι] in
/-- The unordered pair row read as the collision reward of the partner's
solo exit. -/
theorem reward_pair_eq_quittingSingletonCollisionReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second : ι) :
    reward ⟨{first, second}, by simp⟩ first =
      quittingSingletonCollisionReward reward second first := by
  unfold quittingSingletonCollisionReward
  congr 1
  rw [Subtype.ext_iff]
  exact Finset.pair_comm first second

/-! ## Endpoint payoffs at a pair-active root -/

/-- The pure-Quit endpoint of one active coordinate at a pair-active root:
it exits alone against the partner's survival mass and collides against the
partner's hazard.  The declared continuation does not enter. -/
theorem quittingRootQuitPayoff_pair_active
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root) :
    quittingRootQuitPayoff reward tail root first =
      (1 - hazardOfRoot root second) * quittingSoloReward reward first first +
        hazardOfRoot root second *
          quittingSingletonCollisionReward reward second first := by
  have hupdate : IsQuittingActiveRoot {first, second}
      (Function.update root first (PMF.pure true)) :=
    isQuittingActiveRoot_update_quit_of_mem hroot (by simp)
  have hfirst : hazardOfRoot (Function.update root first (PMF.pure true))
      first = 1 := by simp [hazardOfRoot]
  have hsecond : hazardOfRoot (Function.update root first (PMF.pure true))
      second = hazardOfRoot root second := by
    simp [hazardOfRoot, Function.update_of_ne (Ne.symm hne)]
  rw [quittingRootQuitPayoff,
    quittingRootExpectedPayoff_pair_active reward tail _ first second first hne
      hupdate,
    hfirst, hsecond,
    reward_pair_eq_quittingSingletonCollisionReward reward first second]
  simp only [quittingSoloReward]
  ring

/-- The pure-Continue endpoint of one active coordinate at a pair-active root:
it receives the partner's singleton row against the partner's hazard and the
declared continuation against the partner's survival mass. -/
theorem quittingRootContinuePayoff_pair_active
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root) :
    quittingRootContinuePayoff reward tail root first =
      hazardOfRoot root second * quittingSoloReward reward second first +
        (1 - hazardOfRoot root second) * tail first := by
  have hupdate : IsQuittingActiveRoot {first, second}
      (Function.update root first (PMF.pure false)) :=
    isQuittingActiveRoot_update_continue hroot first
  have hfirst : hazardOfRoot (Function.update root first (PMF.pure false))
      first = 0 := by simp [hazardOfRoot]
  have hsecond : hazardOfRoot (Function.update root first (PMF.pure false))
      second = hazardOfRoot root second := by
    simp [hazardOfRoot, Function.update_of_ne (Ne.symm hne)]
  rw [quittingRootContinuePayoff,
    quittingRootExpectedPayoff_pair_active reward tail _ first second first hne
      hupdate,
    hfirst, hsecond]
  simp only [quittingSoloReward]
  ring

/-! ## The pair indifference identity -/

/-- The increment `first` collects by joining `second`'s solo exit instead of
receiving it. -/
def quittingPairCollisionIncrement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second : ι) :
    ℝ :=
  quittingSingletonCollisionReward reward second first -
    quittingSoloReward reward second first

/-- **Pair indifference.**  At an exact endpoint-Nash root supported on two
coordinates, a strictly mixing coordinate's continuation displacement above its
own singleton reward, scaled by the partner's survival mass, is exactly the
partner's hazard times the coordinate's collision increment.  This is exact:
no vanishing-hazard expansion is used. -/
theorem pairActive_indifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {tail : Payoff ι}
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hquit : 0 < (root first true).toReal)
    (hcontinue : 0 < (root first false).toReal) :
    (1 - hazardOfRoot root second) *
        (tail first - quittingSoloReward reward first first) =
      hazardOfRoot root second *
        quittingPairCollisionIncrement reward first second := by
  have hzero := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    reward tail root first hnash hcontinue hquit
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_pair_active reward tail hne hroot,
    quittingRootContinuePayoff_pair_active reward tail hne hroot] at hzero
  rw [quittingPairCollisionIncrement]
  linarith

/-- **The pinned pair identity.**  If the continuation already pays the
strictly mixing coordinate its own singleton reward, the partner's hazard times
the collision increment vanishes. -/
theorem hazard_mul_quittingPairCollisionIncrement_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {tail : Payoff ι}
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hquit : 0 < (root first true).toReal)
    (hcontinue : 0 < (root first false).toReal)
    (hpin : tail first = quittingSoloReward reward first first) :
    hazardOfRoot root second *
      quittingPairCollisionIncrement reward first second = 0 := by
  have hidentity := pairActive_indifference reward hne hroot hnash hquit
    hcontinue
  rw [hpin, sub_self, mul_zero] at hidentity
  exact hidentity.symm

/-! ## The pointwise solo phase -/

/-- Joining any other coordinate's solo exit changes what a player receives. -/
def QuittingPairCollisionNondegenerate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ who owner : ι, who ≠ owner →
    quittingPairCollisionIncrement reward who owner ≠ 0

/-- **The partner's hazard vanishes.**  At an exact endpoint-Nash root
supported on two distinct coordinates, once the continuation pins the strictly
mixing coordinate at its own singleton reward and joining the partner's exit
changes what that coordinate receives, the partner quits with probability
zero.

The pin is exactly what a solo date supplies for free
(`IsQuittingSoloRoot.tail_owner_eq_soloReward_of_interior`), and the collision
condition is a condition on the pair's collision row, not on the normalized
solo matrix. -/
theorem hazardOfRoot_eq_zero_of_pairActive_of_collisionIncrement_ne_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {tail : Payoff ι}
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hquit : 0 < (root first true).toReal)
    (hcontinue : 0 < (root first false).toReal)
    (hpin : tail first = quittingSoloReward reward first first)
    (hcollision : quittingPairCollisionIncrement reward first second ≠ 0) :
    hazardOfRoot root second = 0 :=
  (mul_eq_zero.1 (hazard_mul_quittingPairCollisionIncrement_eq_zero reward hne
    hroot hnash hquit hcontinue hpin)).resolve_right hcollision

/-- **Pointwise solo phase.**  A pinned exact endpoint-Nash root supported on
two distinct coordinates, on a pair whose collision increment does not vanish,
is a solo root at the strictly mixing coordinate: every other coordinate,
partner included, continues with certainty.  In particular two coordinates
cannot both mix strictly at such a root. -/
theorem isQuittingSoloRoot_of_pairActive_of_collisionIncrement_ne_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {tail : Payoff ι}
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hroot : IsQuittingActiveRoot {first, second} root)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hquit : 0 < (root first true).toReal)
    (hcontinue : 0 < (root first false).toReal)
    (hpin : tail first = quittingSoloReward reward first first)
    (hcollision : quittingPairCollisionIncrement reward first second ≠ 0) :
    IsQuittingSoloRoot root first := by
  have hzero := hazardOfRoot_eq_zero_of_pairActive_of_collisionIncrement_ne_zero
    reward hne hroot hnash hquit hcontinue hpin hcollision
  have hsecond : root second = PMF.pure false :=
    quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport root
      (by simp [quittingPositiveHazardSupport, hzero])
  intro player hplayer
  by_cases hp : player = second
  · exact hp ▸ hsecond
  · exact hroot player (by simp [hplayer, hp])

/-- **Pointwise solo phase on a collision-nondegenerate table.**  A root
supported on two distinct coordinates, exact endpoint-Nash against a
continuation that pins its strictly mixing coordinate, is a solo root at that
coordinate. -/
theorem isQuittingSoloRoot_of_pairActive_of_collisionNondegenerate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {tail : Payoff ι}
    {root : ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (hnondegenerate : QuittingPairCollisionNondegenerate reward)
    (hroot : IsQuittingActiveRoot {first, second} root)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hquit : 0 < (root first true).toReal)
    (hcontinue : 0 < (root first false).toReal)
    (hpin : tail first = quittingSoloReward reward first first) :
    IsQuittingSoloRoot root first :=
  isQuittingSoloRoot_of_pairActive_of_collisionIncrement_ne_zero reward hne
    hroot hnash hquit hcontinue hpin (hnondegenerate first second hne)

end GameTheory
