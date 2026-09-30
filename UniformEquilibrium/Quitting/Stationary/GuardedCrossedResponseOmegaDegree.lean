import MathUE.Topology.AmbientDegreeProperties
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseAmbientDegree

/-!
# The literal guarded-crossed source region

The packet uses the coordinate box `Ω = (-1,2)^n`, with a small closed ball
removed. The radial annulus and this literal source have the same entire
nonzero zero fiber. Excision through their actual intersection identifies
their intrinsic degrees; no enclosure of the closure of Ω in `[-2,2]` is used.
-/

noncomputable section

namespace GameTheory

open Set _root_.Math.Topology _root_.Math.LinearProgramming

variable {n : ℕ}

/-- The packet's literal ambient box, including the original strategy boundary. -/
def quittingCrossedOmega : Set (Fin n → ℝ) :=
  {source | ∀ who, (-1 : ℝ) < source who ∧ source who < 2}

theorem isOpen_quittingCrossedOmega : IsOpen (quittingCrossedOmega (n := n)) := by
  have hopen (who : Fin n) : IsOpen {source : Fin n → ℝ |
      (-1 : ℝ) < source who ∧ source who < 2} :=
    (isOpen_lt continuous_const (continuous_apply who)).inter
      (isOpen_lt (continuous_apply who) continuous_const)
  simpa only [quittingCrossedOmega, ofPred_forall] using isOpen_iInter_of_finite hopen

theorem isBounded_quittingCrossedOmega :
    Bornology.IsBounded (quittingCrossedOmega (n := n)) := by
  have hbox : Bornology.IsBounded
      (Set.pi Set.univ (fun _ : Fin n => Icc (-1 : ℝ) 2)) :=
    Bornology.IsBounded.pi (fun _ => Metric.isBounded_Icc _ _)
  apply hbox.subset
  intro source hsource who _
  exact ⟨(hsource who).1.le, (hsource who).2.le⟩

/-- Remove the locally isolated origin from the packet's literal box. -/
def quittingCrossedOmegaAnnulus (radius : ℝ) : Set (Fin n → ℝ) :=
  quittingCrossedOmega \ Metric.closedBall 0 radius

theorem isOpen_quittingCrossedOmegaAnnulus (radius : ℝ) :
    IsOpen (quittingCrossedOmegaAnnulus (n := n) radius) :=
  isOpen_quittingCrossedOmega.inter Metric.isClosed_closedBall.isOpen_compl

theorem isBounded_quittingCrossedOmegaAnnulus (radius : ℝ) :
    Bornology.IsBounded (quittingCrossedOmegaAnnulus (n := n) radius) :=
  isBounded_quittingCrossedOmega.subset sdiff_subset

/-- Every zero of the actual displacement field is strictly inside Ω. -/
theorem quittingCrossedFixedPointField_zero_mem_omega
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 ≤ height) (hheightOne : height ≤ 1)
    (source : Fin n → ℝ)
    (hzero : quittingCrossedFixedPointField reward first second height source = 0) :
    source ∈ quittingCrossedOmega := by
  have hfixed : quittingCrossedClippedMap reward first second height source = source := by
    exact (sub_eq_zero.mp hzero).symm
  have hbox := quittingCrossedClippedMap_fixed_mem_box
    reward first second height hheight source hfixed
  intro who
  have hceiling : quittingCrossedCeiling first second height who ≤ 1 := by
    unfold quittingCrossedCeiling
    split_ifs <;> linarith
  constructor <;> linarith [(hbox who).1, (hbox who).2]

/-- On the literal packet source, the intrinsic degree of the entire nonzero
crossed fiber is `1 - κ`, without finite-root or regularity hypotheses. -/
theorem exists_quittingCrossedOmegaAnnulus_degree_eq_one_sub_r0Degree
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second)) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 ∧
      (∀ source : Fin n → ℝ, ‖source‖ ≤ radius →
        quittingCrossedClippedMap reward first second height source = source → source = 0) ∧
      ∃ hfrontier : ∀ source ∈ frontier (quittingCrossedOmegaAnnulus (n := n) radius),
        quittingCrossedFixedPointField reward first second height source ≠ 0,
        ({source | quittingCrossedFixedPointField reward first second height source = 0} ∩
          quittingCrossedOmegaAnnulus radius) =
            quittingCrossedNonzeroFixedPointSet reward first second height ∧
        ambientDegree (quittingCrossedFixedPointField reward first second height)
          (quittingCrossedOmegaAnnulus radius) 0
          (isOpen_quittingCrossedOmegaAnnulus radius)
          (isBounded_quittingCrossedOmegaAnnulus radius)
          (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
          hfrontier = 1 - r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 := by
  obtain ⟨radius, hradius, hsmall, hisolation, hradialFrontier, hradialZeros, hdegree⟩ :=
    exists_quittingCrossedAmbientAnnulus_degree_eq_one_sub_r0Degree
      reward first second height hheight hheightOne hR0
  let field := quittingCrossedFixedPointField reward first second height
  let radial := quittingCrossedAmbientAnnulus (n := n) radius
  let omega := quittingCrossedOmegaAnnulus (n := n) radius
  have hopenOmega : IsOpen omega := isOpen_quittingCrossedOmegaAnnulus radius
  have hfixed (source : Fin n → ℝ) (hzero : field source = 0) :
      quittingCrossedClippedMap reward first second height source = source :=
    (sub_eq_zero.mp hzero).symm
  have homega (source : Fin n → ℝ) (hzero : field source = 0) :
      source ∈ quittingCrossedOmega :=
    quittingCrossedFixedPointField_zero_mem_omega
      reward first second height hheight.le hheightOne source hzero
  have hzeros : {source | field source = 0} ∩ omega =
      quittingCrossedNonzeroFixedPointSet reward first second height := by
    ext source
    change (field source = 0 ∧ source ∈ omega) ↔
      (source ≠ 0 ∧ quittingCrossedClippedMap reward first second height source = source)
    constructor
    · rintro ⟨hzero, hsource⟩
      refine ⟨?_, hfixed source hzero⟩
      rintro rfl
      exact hsource.2 (by simpa only [Metric.mem_closedBall, dist_self] using hradius.le)
    · rintro ⟨hnonzero, hsource⟩
      have hzero : field source = 0 := sub_eq_zero.mpr hsource.symm
      refine ⟨hzero, homega source hzero, ?_⟩
      intro hclosed
      have hnorm : ‖source‖ ≤ radius := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hclosed
      exact hnonzero (hisolation source hnorm hsource)
  have hfrontier : ∀ source ∈ frontier omega, field source ≠ 0 := by
    have hout : closure omega ⊆ (Metric.ball 0 radius)ᶜ :=
      closure_minimal (fun _ h hball => h.2 (Metric.ball_subset_closedBall hball))
        Metric.isOpen_ball.isClosed_compl
    intro source hsource hzero
    by_cases hnorm : ‖source‖ ≤ radius
    · have heq := hisolation source hnorm (hfixed source hzero)
      apply hout (frontier_subset_closure hsource)
      simpa only [heq, Metric.mem_ball, dist_self] using hradius
    · have hmem : source ∈ omega := ⟨homega source hzero, by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm⟩
      exact hsource.2 (by rwa [hopenOmega.interior_eq])
  let common := radial ∩ omega
  have hopenCommon : IsOpen common :=
    (isOpen_quittingCrossedAmbientAnnulus radius).inter hopenOmega
  have hradialRetain : ∀ source ∈ radial, field source = 0 → source ∈ common := by
    intro source hsource hzero
    have hnonzero := (Set.ext_iff.mp hradialZeros source).mp ⟨hzero, hsource⟩
    exact ⟨hsource, ((Set.ext_iff.mp hzeros source).mpr hnonzero).2⟩
  have homegaRetain : ∀ source ∈ omega, field source = 0 → source ∈ common := by
    intro source hsource hzero
    have hnonzero := (Set.ext_iff.mp hzeros source).mp ⟨hzero, hsource⟩
    exact ⟨((Set.ext_iff.mp hradialZeros source).mpr hnonzero).2, hsource⟩
  have hradial := ambientDegree_excision field radial common 0
    (isOpen_quittingCrossedAmbientAnnulus radius) (isBounded_quittingCrossedAmbientAnnulus radius)
    (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
    hradialFrontier hopenCommon inter_subset_left hradialRetain
  have homegaDegree := ambientDegree_excision field omega common 0 hopenOmega
    (isBounded_quittingCrossedOmegaAnnulus radius)
    (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
    hfrontier hopenCommon inter_subset_right homegaRetain
  exact ⟨radius, hradius, hsmall, hisolation, hfrontier, hzeros,
    homegaDegree.trans (hradial.symm.trans hdegree)⟩

end GameTheory
