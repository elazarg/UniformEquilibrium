import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalBehavioralAdapter
import MathUE.PMFProduct.Update

/-!
# Product marginal for a private clock kernel

Sampling an original independent child tuple, then changing only one own
clock through a kernel that sees only that original clock, preserves product
independence. This is the missing semantic marginal bridge for the deadline
mixed response; the independent outsider deadline is already internal to its
one-coordinate kernel.
-/

noncomputable section

namespace GameTheory

open _root_.Math Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Inserting the deterministic Never outsider into a child product gives
exactly the quiet parent product law. -/
theorem map_pmfPi_child_quiet
    (childLaws : ι → PMF (Option ℕ)) :
    (pmfPi childLaws).map quietParentClocks =
      pmfPi (quietParentStoppingLaws childLaws) := by
  ext clocks
  rw [PMF.map_apply]
  by_cases hnone : clocks none = none
  · let times : ι → Option ℕ := fun i => clocks (some i)
    have hquiet : quietParentClocks times = clocks := by
      funext player
      cases player with
      | none => exact hnone.symm
      | some i => rfl
    rw [tsum_eq_single times]
    · have hprod : pmfPi childLaws times =
          pmfPi (quietParentStoppingLaws childLaws) clocks := by
        rw [pmfPi_apply, pmfPi_apply, Fintype.prod_option]
        simp only [quietParentStoppingLaws, PMF.pure_apply, hnone,
          ↓reduceIte, one_mul]
        rfl
      split_ifs with h
      · exact hprod
      · exact (h hquiet.symm).elim
    · intro other hother
      have hneq : clocks ≠ quietParentClocks other := by
        intro heq
        apply hother
        funext i
        exact congrFun heq (some i) |>.symm
      simp [hneq]
  · have hneq : ∀ times : ι → Option ℕ,
        clocks ≠ quietParentClocks times := by
      intro times heq
      apply hnone
      rw [heq]
      rfl
    simp [hneq, pmfPi_apply, Fintype.prod_option,
      quietParentStoppingLaws, hnone]

/-- A private one-coordinate stochastic kernel commutes with an independent
product: the resulting law is the product with only that marginal replaced. -/
theorem pmfPi_bind_privateClockKernel
    (laws : ι → PMF (Option ℕ)) (i : ι)
    (kernel : Option ℕ → PMF (Option ℕ)) :
    (pmfPi laws).bind (fun times =>
        (kernel (times i)).map fun newClock => Function.update times i newClock) =
      pmfPi (Function.update laws i ((laws i).bind kernel)) := by
  have hsame : Function.update laws i (laws i) = laws := by
    funext j
    by_cases h : j = i <;> simp [h]
  calc
    (pmfPi laws).bind (fun times =>
        (kernel (times i)).map fun newClock => Function.update times i newClock) =
      ((laws i).bind fun source =>
        (pmfPi (Function.update laws i (PMF.pure source))).bind fun times =>
          (kernel (times i)).map fun newClock =>
            Function.update times i newClock) := by
        conv_lhs => rw [← hsame, pmfPi_update_bind]
        rw [PMF.bind_bind]
    _ = ((laws i).bind fun source =>
        (pmfPi (Function.update laws i (PMF.pure source))).bind fun times =>
          (kernel source).map fun newClock => Function.update times i newClock) := by
        congr 1
        funext source
        apply Math.ProbabilityMassFunction.bind_congr_on_support
        intro times htimes
        have hcoordinate := eq_of_mem_support_pmfPi_update_pure
          laws i source htimes
        rw [hcoordinate]
    _ = ((laws i).bind fun source =>
        (kernel source).bind fun newClock =>
          pmfPi (Function.update laws i (PMF.pure newClock))) := by
        congr 1
        funext source
        simp_rw [show (fun times : ι → Option ℕ =>
            (kernel source).map fun newClock => Function.update times i newClock) =
          (fun times => (kernel source).bind fun newClock =>
            PMF.pure (Function.update times i newClock)) from by
              funext times
              exact (PMF.bind_pure_comp _ _).symm]
        rw [PMF.bind_comm]
        apply congrArg ((kernel source).bind)
        funext newClock
        exact pmfPi_bind_update_pure
          (Function.update laws i (PMF.pure source)) i newClock |>.trans (by
            congr 1
            funext j
            by_cases h : j = i <;> simp [h])
    _ = pmfPi (Function.update laws i ((laws i).bind kernel)) := by
        rw [← PMF.bind_bind]
        exact (pmfPi_update_bind laws i ((laws i).bind kernel)).symm

/-- Mixing the deadline independently and then changing only the selected
child clock has exactly the legal private replacement product marginal. -/
theorem deadlineMixedPrivateReplacement_childProduct
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    (pmfPi childLaws).bind (fun times =>
        outsideLaw.bind fun deadline =>
          (deadlineMixedPrivateClockLaw (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => Function.update times i newClock) =
      pmfPi (Function.update childLaws i
        (deadlineMixedPrivateReplacementLaw (childLaws i) outsideLaw
          advanceWeight withdrawalWeight hadvance hwithdrawal)) := by
  let kernel : Option ℕ → PMF (Option ℕ) := fun source =>
    outsideLaw.bind fun deadline =>
      deadlineMixedPrivateClockLaw source deadline advanceWeight
        withdrawalWeight hadvance hwithdrawal
  have hkernel := pmfPi_bind_privateClockKernel childLaws i kernel
  change (pmfPi childLaws).bind (fun times =>
      outsideLaw.bind fun deadline =>
        (deadlineMixedPrivateClockLaw (times i) deadline
          advanceWeight withdrawalWeight hadvance hwithdrawal).map
            fun newClock => Function.update times i newClock) =
    pmfPi (Function.update childLaws i ((childLaws i).bind kernel))
  calc
    _ = (pmfPi childLaws).bind (fun times =>
          (kernel (times i)).map fun newClock =>
            Function.update times i newClock) := by
        apply congrArg (PMF.bind (pmfPi childLaws))
        funext times
        exact (PMF.map_bind (p := outsideLaw)
          (fun deadline => deadlineMixedPrivateClockLaw (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal)
          (fun newClock => Function.update times i newClock)).symm
    _ = _ := hkernel

/-- The independently mixed private response, embedded in the quiet parent,
has precisely the stopping-law product of the legal one-child replacement. -/
theorem deadlineMixedPrivateReplacement_parentProduct
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    ((pmfPi childLaws).bind (fun times =>
        outsideLaw.bind fun deadline =>
          (deadlineMixedPrivateClockLaw (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => Function.update times i newClock)).map
        quietParentClocks =
      pmfPi (deadlineMixedChildParentStoppingLaws childLaws outsideLaw i
        advanceWeight withdrawalWeight hadvance hwithdrawal) := by
  rw [deadlineMixedPrivateReplacement_childProduct,
    map_pmfPi_child_quiet]
  congr 1
  funext player
  cases player with
  | none => rfl
  | some j =>
      by_cases h : j = i
      · subst j
        simp [deadlineMixedChildParentStoppingLaws,
          quietParentStoppingLaws]
      · simp [deadlineMixedChildParentStoppingLaws,
          quietParentStoppingLaws, h]

end GameTheory
