import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialFaceDrift
import UniformEquilibrium.Quitting.Projective.SingletonLCP

/-! # Literal analytic translation of the actual singleton rectangle

The translation is of annotations and functions only. It does not modify the
quitting game, its reward table, or its zero live and Never payoff.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual lower-singleton rectangle with cap `bound + 1`. -/
def quittingSingletonBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) : Set (Payoff ι) :=
  Icc (fun who => quittingSoloReward reward who who) (fun _ => bound + 1)

/-- Literal widths of the actual singleton rectangle. -/
def quittingSingletonBoxWidth
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) : Payoff ι :=
  fun who => bound + 1 - quittingSoloReward reward who who

/-- The analytic translation from the zero-based rectangle to actual annotations. -/
def quittingSingletonBoxTranslate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (point : Payoff ι) : Payoff ι :=
  (fun who => quittingSoloReward reward who who) + point

omit [Fintype ι] [DecidableEq ι] in
theorem quittingSingletonBoxTranslate_mem_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) (point : Payoff ι) :
    quittingSingletonBoxTranslate reward point ∈ quittingSingletonBox reward bound ↔
      point ∈ Icc (0 : Payoff ι) (quittingSingletonBoxWidth reward bound) := by
  constructor
  · intro hpoint
    constructor <;> intro who
    · have h := hpoint.1 who
      change quittingSoloReward reward who who + point who ≥ quittingSoloReward reward who who at h
      change 0 ≤ point who
      linarith
    · have h := hpoint.2 who
      change quittingSoloReward reward who who + point who ≤ bound + 1 at h
      change point who ≤ bound + 1 - quittingSoloReward reward who who
      linarith
  · intro hpoint
    constructor <;> intro who
    · have h := hpoint.1 who
      change quittingSoloReward reward who who ≤ quittingSoloReward reward who who + point who
      change 0 ≤ point who at h
      linarith
    · have h := hpoint.2 who
      change point who ≤ bound + 1 - quittingSoloReward reward who who at h
      change quittingSoloReward reward who who + point who ≤ bound + 1
      linarith

omit [Fintype ι] [DecidableEq ι] in
theorem quittingSingletonBoxWidth_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    ∀ who, 0 < quittingSingletonBoxWidth reward bound who := by
  intro who
  have hsolo : quittingSoloReward reward who who ≤ bound :=
    (le_abs_self _).trans (hreward (quittingSingletonTerminal who) who)
  dsimp [quittingSingletonBoxWidth]
  linarith

omit [Fintype ι] [DecidableEq ι] in
theorem quittingProjectiveLCPMatrix_lt_singletonBoxWidth
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    ∀ receiver owner, quittingProjectiveLCPMatrix reward receiver owner <
      quittingSingletonBoxWidth reward bound receiver := by
  intro receiver owner
  have hentry := (le_abs_self _).trans
    (hreward (quittingProjectiveSingletonTerminal owner) receiver)
  change reward (quittingProjectiveSingletonTerminal owner) receiver -
      quittingSoloReward reward receiver receiver <
    bound + 1 - quittingSoloReward reward receiver receiver
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Translation preserves the actual receiver-row singleton direction exactly. -/
theorem quittingSingletonBoxTranslate_sub_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (point : Payoff ι) (owner : ι) :
    quittingSingletonBoxTranslate reward point - quittingSoloReward reward owner =
      point - fun receiver => quittingProjectiveLCPMatrix reward receiver owner := by
  ext receiver
  change quittingSoloReward reward receiver receiver + point receiver -
      quittingSoloReward reward owner receiver = point receiver -
    (quittingSoloReward reward owner receiver - quittingSoloReward reward receiver receiver)
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The analytic translation preserves all affine combinations with total
coefficient one, including segment endpoints. -/
theorem quittingSingletonBoxTranslate_affine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second : Payoff ι)
    (left right : ℝ) (htotal : left + right = 1) :
    quittingSingletonBoxTranslate reward (left • first + right • second) =
      left • quittingSingletonBoxTranslate reward first +
        right • quittingSingletonBoxTranslate reward second := by
  ext who
  change quittingSoloReward reward who who + (left * first who + right * second who) =
    left * (quittingSoloReward reward who who + first who) +
      right * (quittingSoloReward reward who who + second who)
  have hscaled := congrArg (fun value : ℝ => value * quittingSoloReward reward who who) htotal
  nlinarith

omit [DecidableEq ι] in
theorem hasFDerivAt_quittingSingletonBoxTranslate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (point : Payoff ι) :
    HasFDerivAt (quittingSingletonBoxTranslate reward)
      (ContinuousLinearMap.id ℝ (Payoff ι)) point :=
  (hasFDerivAt_id point).const_add (fun who => quittingSoloReward reward who who)

omit [DecidableEq ι] in
theorem fderiv_quittingSingletonBoxTranslate_comp
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (potential : Payoff ι → ℝ) (point : Payoff ι)
    (hdiff : DifferentiableAt ℝ potential (quittingSingletonBoxTranslate reward point)) :
    fderiv ℝ (potential ∘ quittingSingletonBoxTranslate reward) point =
      fderiv ℝ potential (quittingSingletonBoxTranslate reward point) := by
  have hcomposition := hdiff.hasFDerivAt.comp point
    (hasFDerivAt_quittingSingletonBoxTranslate reward point)
  simpa only [ContinuousLinearMap.comp_id] using hcomposition.fderiv

omit [DecidableEq ι] in
/-- Positive drift on all actual lower faces transfers to all zero-based
lower faces, including every upper-face intersection. -/
theorem quittingSingletonBoxTranslate_positive_face_drift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ quittingSingletonBox reward bound, DifferentiableAt ℝ potential point)
    (hdrift : ∀ point ∈ quittingSingletonBox reward bound, ∀ owner,
      point owner = quittingSoloReward reward owner owner →
      0 < fderiv ℝ potential point (point - quittingSoloReward reward owner)) :
    ∀ point ∈ Icc (0 : Payoff ι) (quittingSingletonBoxWidth reward bound), ∀ owner,
      point owner = 0 →
      0 < fderiv ℝ (potential ∘ quittingSingletonBoxTranslate reward) point
        (point - fun receiver => quittingProjectiveLCPMatrix reward receiver owner) := by
  intro point hpoint owner howner
  have htranslated := (quittingSingletonBoxTranslate_mem_iff reward bound point).mpr hpoint
  rw [fderiv_quittingSingletonBoxTranslate_comp reward potential point
    (hdiff _ htranslated), ← quittingSingletonBoxTranslate_sub_solo reward point owner]
  exact hdrift _ htranslated owner (by change _ + point owner = _; rw [howner, add_zero])

/-- The existing all-exact-root owner supplies unit, hence strictly positive,
drift on the same actual singleton rectangle. No robust strengthening is used. -/
theorem IsQuittingFullExactRootPotential.singletonBox_positive_face_drift
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward (bound + 1) potential)
    (hdiff : ∀ point ∈ quittingSingletonBox reward bound, DifferentiableAt ℝ potential point) :
    ∀ point ∈ quittingSingletonBox reward bound, ∀ owner,
      point owner = quittingSoloReward reward owner owner →
      0 < fderiv ℝ potential point (point - quittingSoloReward reward owner) := by
  intro point hpoint owner howner
  exact zero_lt_one.trans_le (hpotential.singletonFace_drift hreward (by linarith)
    point owner (fun who => ⟨hpoint.1 who, hpoint.2 who⟩) howner
    (fderiv ℝ potential point) (hdiff point hpoint).hasFDerivAt)

end GameTheory
