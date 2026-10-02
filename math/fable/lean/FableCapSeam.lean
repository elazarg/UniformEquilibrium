/-
The exact first cap seam of a product root.

Raising one continuation-cap coordinate moves the owner's pure Continue
endpoint affinely, with slope the opponents' Continue mass, and leaves the pure
Quit endpoint untouched.  The Quit-minus-Continue endpoint difference therefore
falls by exactly the opponents' Continue mass times the cap rise.

Feeding that displacement into the exact coordinate Nash-defect decomposition
prices the seam exactly.  A coordinate that was exactly Nash against the old cap
and mixes both actions pays its own Quit mass times the opponents' Continue mass
times the rise.  A pure-Quit coordinate pays the positive part of the displaced
difference, with no sign hypothesis on the rise.  A pure-Continue coordinate
never pays more under a nonnegative rise than it paid before.

Everything here concerns one product root read against two continuation caps.
No profile sequence, chronology, absorption ledger, exact-block capacity claim,
or existence of an exact root at the new cap is involved.
-/
import UniformEquilibrium.Quitting.Root.NashDefect
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix
import UniformEquilibrium.Quitting.Stationary.LiveMass
import UniformEquilibrium.Quitting.Stationary.Payoff

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Endpoint displacement under a cap change -/

/-- The pure Continue endpoint reads the continuation cap only at the owner's
own coordinate. -/
theorem fable_quittingRootContinuePayoff_congr_ownCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap cap' : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hcap : cap who = cap' who) :
    quittingRootContinuePayoff reward cap root who =
      quittingRootContinuePayoff reward cap' root who := by
  unfold quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add, hcap]

/-- The pure Continue endpoint is affine in the owner's own cap coordinate, with
linear coefficient the opponents' Continue mass. -/
theorem fable_quittingRootContinuePayoff_capChange
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap cap' : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuePayoff reward cap' root who =
      quittingRootContinuePayoff reward cap root who +
        quittingRootOpponentContinueMass root who * (cap' who - cap who) := by
  have hcap : cap' who =
      Function.update cap who (cap who + (cap' who - cap who)) who := by
    rw [Function.update_self]
    ring
  rw [fable_quittingRootContinuePayoff_congr_ownCap reward cap'
      (Function.update cap who (cap who + (cap' who - cap who))) root who hcap,
    quittingRootContinuePayoff_update_add]

/-- **(2.1).**  Raising the continuation cap lowers the Quit-minus-Continue
endpoint difference by exactly the opponents' Continue mass times the cap rise.
The Quit endpoint is cap-independent; the Continue endpoint is affine. -/
theorem fable_quittingRootEndpointDifference_capChange
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap cap' : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward cap' root who =
      quittingRootEndpointDifference reward cap root who -
        quittingRootOpponentContinueMass root who * (cap' who - cap who) := by
  unfold quittingRootEndpointDifference
  rw [fable_quittingRootContinuePayoff_capChange reward cap cap' root who,
    quittingRootQuitPayoff_continuation_invariant reward cap' cap root who]
  ring

/-- **(2.1), update form.**  The same displacement written against the update
form of the production affinity lemma. -/
theorem fable_quittingRootEndpointDifference_update_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (root : ι → PMF Bool) (who : ι) (delta : ℝ) :
    quittingRootEndpointDifference reward
        (Function.update cap who (cap who + delta)) root who =
      quittingRootEndpointDifference reward cap root who -
        quittingRootOpponentContinueMass root who * delta := by
  rw [fable_quittingRootEndpointDifference_capChange reward cap
      (Function.update cap who (cap who + delta)) root who,
    Function.update_self]
  ring

/-! ## The defect decomposition and its cap-shifted form -/

/-- **(2.2).**  The exact coordinate Nash defect is the root's Continue mass
times the positive part of the endpoint difference, plus its Quit mass times the
positive part of the negated difference.  This is the production decomposition
restated in the note's orientation. -/
theorem fable_quittingRootCoordinateNashDefect_eq_mass_mul_posPart
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCoordinateNashDefect reward cap root who =
      (root who false).toReal *
          max (quittingRootEndpointDifference reward cap root who) 0 +
        (root who true).toReal *
          max (-quittingRootEndpointDifference reward cap root who) 0 :=
  quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart
    reward cap root who

/-- **(2.1) fed into (2.2).**  The coordinate Nash defect at the new cap,
written entirely in the old cap's endpoint difference and the cap rise. -/
theorem fable_quittingRootCoordinateNashDefect_capChange_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap cap' : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCoordinateNashDefect reward cap' root who =
      (root who false).toReal *
          max (quittingRootEndpointDifference reward cap root who -
            quittingRootOpponentContinueMass root who * (cap' who - cap who)) 0 +
        (root who true).toReal *
          max (quittingRootOpponentContinueMass root who * (cap' who - cap who) -
            quittingRootEndpointDifference reward cap root who) 0 := by
  rw [fable_quittingRootCoordinateNashDefect_eq_mass_mul_posPart reward cap'
      root who,
    fable_quittingRootEndpointDifference_capChange reward cap cap' root who,
    neg_sub]

/-! ## Complementarity at a mixed coordinate -/

/-- Complementarity.  A coordinate carrying positive mass on both actions has
zero Nash defect only if its two pure endpoints agree. -/
theorem fable_quittingRootEndpointDifference_eq_zero_of_mixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hcontinuePos : 0 < (root who false).toReal)
    (hquitPos : 0 < (root who true).toReal)
    (hexact : quittingRootCoordinateNashDefect reward cap root who = 0) :
    quittingRootEndpointDifference reward cap root who = 0 := by
  rw [fable_quittingRootCoordinateNashDefect_eq_mass_mul_posPart] at hexact
  have hcontinueTerm : 0 ≤ (root who false).toReal *
      max (quittingRootEndpointDifference reward cap root who) 0 :=
    mul_nonneg hcontinuePos.le (le_max_right _ _)
  have hquitTerm : 0 ≤ (root who true).toReal *
      max (-quittingRootEndpointDifference reward cap root who) 0 :=
    mul_nonneg hquitPos.le (le_max_right _ _)
  have hcontinueZero : (root who false).toReal *
      max (quittingRootEndpointDifference reward cap root who) 0 = 0 := by
    linarith
  have hquitZero : (root who true).toReal *
      max (-quittingRootEndpointDifference reward cap root who) 0 = 0 := by
    linarith
  have hmaxContinue :
      max (quittingRootEndpointDifference reward cap root who) 0 = 0 := by
    rcases mul_eq_zero.mp hcontinueZero with hmass | hmax
    · exact absurd hmass hcontinuePos.ne'
    · exact hmax
  have hmaxQuit :
      max (-quittingRootEndpointDifference reward cap root who) 0 = 0 := by
    rcases mul_eq_zero.mp hquitZero with hmass | hmax
    · exact absurd hmass hquitPos.ne'
    · exact hmax
  have hle : quittingRootEndpointDifference reward cap root who ≤ 0 := by
    have hbound := le_max_left
      (quittingRootEndpointDifference reward cap root who) (0 : ℝ)
    rw [hmaxContinue] at hbound
    exact hbound
  have hge : -quittingRootEndpointDifference reward cap root who ≤ 0 := by
    have hbound := le_max_left
      (-quittingRootEndpointDifference reward cap root who) (0 : ℝ)
    rw [hmaxQuit] at hbound
    exact hbound
  linarith

/-- Complementarity against an exact product root: at a coordinate mixing both
actions, the two pure endpoints of an exactly Nash root agree. -/
theorem fable_quittingRootEndpointDifference_eq_zero_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hcontinuePos : 0 < (root who false).toReal)
    (hquitPos : 0 < (root who true).toReal)
    (hnash : IsεQuittingRootNash reward cap 0 root) :
    quittingRootEndpointDifference reward cap root who = 0 :=
  fable_quittingRootEndpointDifference_eq_zero_of_mixed reward cap root who
    hcontinuePos hquitPos
    ((isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero reward cap root).mp
      hnash who)

/-! ## The exact first seam -/

/-- **(2.3a), the signed seam.**  Let a coordinate be exactly Nash against the
old cap and mix both actions, and let its own cap coordinate move by an
arbitrary signed displacement.  Then its Nash defect against the new cap is the
opponents' Continue mass times the positive part of the displacement charged to
the root's Quit mass, plus the same mass times the positive part of the negated
displacement charged to the root's Continue mass.  A cap rise is exposed only to
the old Quit mass; a cap fall is exposed only to the old Continue mass. -/
theorem fable_quittingRootCoordinateNashDefect_capChange_eq_signedSeam
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap cap' : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hquitPos : 0 < (root who true).toReal)
    (hquitLt : (root who true).toReal < 1)
    (hexact : quittingRootCoordinateNashDefect reward cap root who = 0) :
    quittingRootCoordinateNashDefect reward cap' root who =
      (root who true).toReal * (quittingRootOpponentContinueMass root who *
          max (cap' who - cap who) 0) +
        (root who false).toReal * (quittingRootOpponentContinueMass root who *
          max (cap who - cap' who) 0) := by
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hcontinuePos : 0 < (root who false).toReal := by linarith
  have hzero := fable_quittingRootEndpointDifference_eq_zero_of_mixed
    reward cap root who hcontinuePos hquitPos hexact
  have hmass := quittingRootOpponentContinueMass_nonneg root who
  have hdiff : quittingRootEndpointDifference reward cap' root who =
      -(quittingRootOpponentContinueMass root who * (cap' who - cap who)) := by
    rw [fable_quittingRootEndpointDifference_capChange reward cap cap' root who,
      hzero]
    ring
  rw [fable_quittingRootCoordinateNashDefect_eq_mass_mul_posPart reward cap'
      root who,
    hdiff, neg_neg]
  rcases le_total (cap who) (cap' who) with hsign | hsign
  · have hseam : 0 ≤ quittingRootOpponentContinueMass root who *
        (cap' who - cap who) :=
      mul_nonneg hmass (by linarith)
    rw [max_eq_right (by linarith : -(quittingRootOpponentContinueMass root who *
        (cap' who - cap who)) ≤ 0),
      max_eq_left hseam,
      max_eq_left (by linarith : (0 : ℝ) ≤ cap' who - cap who),
      max_eq_right (by linarith : cap who - cap' who ≤ 0)]
    ring
  · have hfall : 0 ≤ quittingRootOpponentContinueMass root who *
        (cap who - cap' who) :=
      mul_nonneg hmass (by linarith)
    rw [max_eq_left (by linarith : (0 : ℝ) ≤
        -(quittingRootOpponentContinueMass root who * (cap' who - cap who))),
      max_eq_right (by linarith : quittingRootOpponentContinueMass root who *
        (cap' who - cap who) ≤ 0),
      max_eq_right (by linarith : cap' who - cap who ≤ 0),
      max_eq_left (by linarith : (0 : ℝ) ≤ cap who - cap' who)]
    ring

/-- **(2.3), the first seam.**  Let a coordinate be exactly Nash against the old
cap and mix both actions, and let its own cap coordinate weakly rise.  Then its
Nash defect against the new cap is exactly the root's Quit mass times the
opponents' Continue mass times the rise.  This is the nonnegative-displacement
specialization of the signed seam. -/
theorem fable_quittingRootCoordinateNashDefect_capRise_eq_quitMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap cap' : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hquitPos : 0 < (root who true).toReal)
    (hquitLt : (root who true).toReal < 1)
    (hexact : quittingRootCoordinateNashDefect reward cap root who = 0)
    (hrise : cap who ≤ cap' who) :
    quittingRootCoordinateNashDefect reward cap' root who =
      (root who true).toReal *
        (quittingRootOpponentContinueMass root who * (cap' who - cap who)) := by
  rw [fable_quittingRootCoordinateNashDefect_capChange_eq_signedSeam reward cap
      cap' root who hquitPos hquitLt hexact,
    max_eq_left (by linarith : (0 : ℝ) ≤ cap' who - cap who),
    max_eq_right (by linarith : cap who - cap' who ≤ 0)]
  ring

/-- **(2.3a) against an exact root.**  The signed seam, stated against exact
product-root Nash at the old cap. -/
theorem fable_quittingRootCoordinateNashDefect_capChange_eq_signedSeam_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap cap' : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hquitPos : 0 < (root who true).toReal)
    (hquitLt : (root who true).toReal < 1)
    (hnash : IsεQuittingRootNash reward cap 0 root) :
    quittingRootCoordinateNashDefect reward cap' root who =
      (root who true).toReal * (quittingRootOpponentContinueMass root who *
          max (cap' who - cap who) 0) +
        (root who false).toReal * (quittingRootOpponentContinueMass root who *
          max (cap who - cap' who) 0) :=
  fable_quittingRootCoordinateNashDefect_capChange_eq_signedSeam reward cap cap'
    root who hquitPos hquitLt
    ((isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero reward cap root).mp
      hnash who)

/-- **(2.3) against an exact root.**  The same first seam, stated against exact
product-root Nash at the old cap. -/
theorem fable_quittingRootCoordinateNashDefect_capRise_eq_quitMass_mul_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap cap' : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hquitPos : 0 < (root who true).toReal)
    (hquitLt : (root who true).toReal < 1)
    (hnash : IsεQuittingRootNash reward cap 0 root)
    (hrise : cap who ≤ cap' who) :
    quittingRootCoordinateNashDefect reward cap' root who =
      (root who true).toReal *
        (quittingRootOpponentContinueMass root who * (cap' who - cap who)) :=
  fable_quittingRootCoordinateNashDefect_capRise_eq_quitMass_mul reward cap cap'
    root who hquitPos hquitLt
    ((isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero reward cap root).mp
      hnash who) hrise

/-! ## The two pure coordinates -/

/-- **(2.4), a pure-Quit coordinate.**  A coordinate that quits surely pays the
positive part of the displaced endpoint difference at the new cap.  This is an
identity: no sign hypothesis on the cap change is needed. -/
theorem fable_quittingRootCoordinateNashDefect_capChange_of_pureQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap cap' : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hpure : (root who false).toReal = 0) :
    quittingRootCoordinateNashDefect reward cap' root who =
      max (quittingRootOpponentContinueMass root who * (cap' who - cap who) -
        quittingRootEndpointDifference reward cap root who) 0 := by
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hquitOne : (root who true).toReal = 1 := by linarith
  rw [fable_quittingRootCoordinateNashDefect_capChange_eq reward cap cap' root who,
    hpure, hquitOne]
  ring

/-- **(2.4), the pure-Continue complement.**  A coordinate that continues surely
never pays more under a nonnegative cap rise than it paid before, so no positive
seam lower bound follows from a positive cap rise alone. -/
theorem fable_quittingRootCoordinateNashDefect_capRise_le_of_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap cap' : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hpure : (root who true).toReal = 0)
    (hrise : cap who ≤ cap' who) :
    quittingRootCoordinateNashDefect reward cap' root who ≤
      quittingRootCoordinateNashDefect reward cap root who := by
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hcontinueOne : (root who false).toReal = 1 := by linarith
  have hseam : 0 ≤ quittingRootOpponentContinueMass root who *
      (cap' who - cap who) :=
    mul_nonneg (quittingRootOpponentContinueMass_nonneg root who) (by linarith)
  have hmono : max (quittingRootEndpointDifference reward cap root who -
        quittingRootOpponentContinueMass root who * (cap' who - cap who)) 0 ≤
      max (quittingRootEndpointDifference reward cap root who) 0 :=
    max_le_max (by linarith) le_rfl
  rw [fable_quittingRootCoordinateNashDefect_capChange_eq reward cap cap' root who,
    fable_quittingRootCoordinateNashDefect_eq_mass_mul_posPart reward cap root who,
    hpure, hcontinueOne]
  linarith

end GameTheory
