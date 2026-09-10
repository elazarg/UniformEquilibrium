import MathUE.PMFProduct.Independence
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockStoppingLaw

/-!
# Parent stopping-law pushforwards for the capped-clock coupling
-/

noncomputable section

namespace GameTheory

open Math Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The independent parent source law before quieting or capping: the outsider
draws the deadline and every child draws its prescribed complete clock. -/
def cappedClockParentSourceLaws
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    Option ι → PMF (Option ℕ)
  | none => outsideLaw
  | some i => childLaws i

/-- Parent laws for the quiet lift of the child profile. -/
def quietParentStoppingLaws (childLaws : ι → PMF (Option ℕ)) :
    Option ι → PMF (Option ℕ)
  | none => PMF.pure none
  | some i => childLaws i

/-- Parent laws after child `i` is replaced by its actual compiled capped
clock, while the outsider remains quiet. -/
def cappedChildParentStoppingLaws
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    Option ι → PMF (Option ℕ) :=
  Function.update (quietParentStoppingLaws childLaws) (some i)
    (cappedClockStoppingLaw (childLaws i) outsideLaw)

omit [DecidableEq ι] in
/-- Discarding the independently sampled outsider clock produces exactly the
product stopping law of the quiet parent lift. -/
theorem map_pmfPi_cappedClockParentSourceLaws_quiet
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw)).map
        (fun clocks => quietParentClocks fun i => clocks (some i)) =
      pmfPi (quietParentStoppingLaws childLaws) := by
  let g : (player : Option ι) → Option ℕ → Option ℕ
    | none => fun _ => none
    | some _ => id
  have hpush := pmfPi_push_coordwise
    (cappedClockParentSourceLaws childLaws outsideLaw) g
  change PMF.map (fun clocks => quietParentClocks fun i => clocks (some i))
      (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw)) = _
  have hmap : (fun clocks : Option ι → Option ℕ =>
      quietParentClocks fun i => clocks (some i)) =
      fun clocks player => g player (clocks player) := by
    funext clocks player
    cases player <;> rfl
  rw [hmap]
  change Math.ProbabilityMassFunction.pushforward
      (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw))
        (fun clocks player => g player (clocks player)) = _
  rw [hpush]
  congr 1
  funext player
  cases player with
  | none =>
      change PMF.map (Function.const (Option ℕ) none) outsideLaw = PMF.pure none
      exact PMF.map_const outsideLaw (none : Option ℕ)
  | some j =>
      change PMF.map id (childLaws j) = childLaws j
      exact PMF.map_id (childLaws j)

/-- Applying the sampled outsider deadline to child `i` and then discarding
the outsider produces the independent product with exactly that child's
compiled capped stopping law. -/
theorem map_pmfPi_cappedClockParentSourceLaws_cappedChild
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw)).map
        (fun clocks => cappedChildParentClocks
          (fun j => clocks (some j)) (clocks none) i) =
      pmfPi (cappedChildParentStoppingLaws childLaws outsideLaw i) := by
  let quiet := quietParentStoppingLaws childLaws
  have hsource : cappedClockParentSourceLaws childLaws outsideLaw =
      Function.update quiet none outsideLaw := by
    funext player
    cases player <;> simp [quiet, cappedClockParentSourceLaws,
      quietParentStoppingLaws]
  have hfixed (deadline : Option ℕ) :
      (pmfPi (Function.update quiet none (PMF.pure deadline))).map
          (fun clocks => cappedChildParentClocks
            (fun j => clocks (some j)) (clocks none) i) =
        pmfPi (Function.update quiet (some i)
          ((childLaws i).map fun source =>
            cappedStoppingClock source deadline)) := by
    let g : (player : Option ι) → Option ℕ → Option ℕ
      | none => fun _ => none
      | some j => if j = i then
          fun source => cappedStoppingClock source deadline else id
    have hpush := pmfPi_push_coordwise
      (Function.update quiet none (PMF.pure deadline)) g
    have hpin :
        (pmfPi (Function.update quiet none (PMF.pure deadline))).map
            (fun clocks => Function.update clocks none deadline) =
          pmfPi (Function.update quiet none (PMF.pure deadline)) := by
      calc
        _ = (pmfPi (Function.update quiet none (PMF.pure deadline))).bind
            (fun clocks => PMF.pure
              (Function.update clocks none deadline)) :=
          (PMF.bind_pure_comp _ _).symm
        _ = pmfPi (Function.update
            (Function.update quiet none (PMF.pure deadline)) none
              (PMF.map (fun _ => deadline) (PMF.pure deadline))) :=
          (pmfPi_bind_update_map
            (A := fun _ : Option ι => Option ℕ)
            (Function.update quiet none (PMF.pure deadline)) none
              (fun _ : Option ℕ => deadline))
        _ = _ := by
          congr 1
          funext player
          cases player with
          | none =>
              simp only [Function.update_self]
              change PMF.map (Function.const (Option ℕ) deadline)
                  (PMF.pure deadline) = PMF.pure deadline
              exact PMF.map_const (PMF.pure deadline) deadline
          | some j => simp [quiet, quietParentStoppingLaws]
    change PMF.map (fun clocks => cappedChildParentClocks
        (fun j => clocks (some j)) (clocks none) i)
        (pmfPi (Function.update quiet none (PMF.pure deadline))) = _
    conv_lhs => rw [← hpin, PMF.map_comp]
    rw [show ((fun clocks => cappedChildParentClocks
          (fun j => clocks (some j)) (clocks none) i) ∘
          fun clocks => Function.update clocks none deadline) =
        fun clocks player => g player (clocks player) by
      funext clocks player
      cases player with
      | none => rfl
      | some j =>
          by_cases hji : j = i
          · subst j
            simp [g, cappedChildParentClocks]
          · simp [g, cappedChildParentClocks, hji]]
    change Math.ProbabilityMassFunction.pushforward
        (pmfPi (Function.update quiet none (PMF.pure deadline)))
          (fun clocks player => g player (clocks player)) = _
    rw [hpush]
    congr 1
    funext player
    cases player with
    | none =>
        change PMF.map (Function.const (Option ℕ) none) (PMF.pure deadline) =
          PMF.pure none
        exact PMF.map_const (PMF.pure deadline) (none : Option ℕ)
    | some j =>
        by_cases hji : j = i
        · subst j
          simp [g, quiet, quietParentStoppingLaws,
            Math.ProbabilityMassFunction.pushforward]
        · simp [g, quiet, quietParentStoppingLaws, hji,
            Math.ProbabilityMassFunction.pushforward, PMF.map_id]
  rw [hsource, pmfPi_update_bind]
  simp only [PMF.map_bind, hfixed]
  have hreassociate : (outsideLaw.bind fun deadline =>
      pmfPi (Function.update quiet (some i)
        ((childLaws i).map fun source =>
          cappedStoppingClock source deadline))) =
      outsideLaw.bind fun deadline =>
        (childLaws i).bind fun source =>
          pmfPi (Function.update quiet (some i)
            (PMF.pure (cappedStoppingClock source deadline))) := by
    apply congrArg (PMF.bind outsideLaw)
    funext deadline
    rw [pmfPi_update_bind]
    have hmap : (childLaws i).map
          (fun source => cappedStoppingClock source deadline) =
        (childLaws i).bind (PMF.pure ∘
          fun source => cappedStoppingClock source deadline) :=
      (PMF.bind_pure_comp _ _).symm
    rw [hmap]
    rw [PMF.bind_bind]
    simp
  rw [hreassociate]
  rw [PMF.bind_comm]
  change (childLaws i).bind (fun source => outsideLaw.bind fun deadline =>
      pmfPi (Function.update quiet (some i)
        (PMF.pure (cappedStoppingClock source deadline)))) = _
  have htarget : pmfPi (cappedChildParentStoppingLaws childLaws outsideLaw i) =
      (cappedClockStoppingLaw (childLaws i) outsideLaw).bind
        (fun clock => pmfPi
          (Function.update quiet (some i) (PMF.pure clock))) := by
    unfold cappedChildParentStoppingLaws
    exact pmfPi_update_bind quiet (some i) _
  rw [htarget]
  unfold cappedClockStoppingLaw
  rw [PMF.bind_bind]
  apply congrArg (PMF.bind (childLaws i))
  funext source
  have hmap (source : Option ℕ) : outsideLaw.map (fun deadline =>
        cappedStoppingClock source deadline) =
      outsideLaw.bind (PMF.pure ∘ fun deadline =>
        cappedStoppingClock source deadline) :=
    (PMF.bind_pure_comp _ _).symm
  rw [hmap]
  rw [PMF.bind_bind]
  simp

end GameTheory
