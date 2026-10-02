import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact

/-! # Compact minima and their uniform first-order expansion

The minimizer set retains every old minimizer. Joint continuity of the actual
parameter derivative supplies uniform first-order error, rather than requesting
a uniform differentiability certificate from the caller.
-/

noncomputable section

namespace Math.CompactMinimumEnvelope

open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

def minimum (family : ℝ → X → ℝ) (parameter : ℝ) : ℝ :=
  sInf (family parameter '' univ)

def minimizers (family : ℝ → X → ℝ) (parameter : ℝ) : Set X :=
  {point | family parameter point = minimum family parameter}

omit [TopologicalSpace X] [CompactSpace X] [Nonempty X] in
theorem minimum_eq_of_isMinOn (family : ℝ → X → ℝ) (parameter : ℝ) (point : X)
    (hpoint : IsMinOn (family parameter) univ point) :
    family parameter point = minimum family parameter := by
  have hleast : IsLeast (family parameter '' univ) (family parameter point) := by
    refine ⟨⟨point, mem_univ point, rfl⟩, ?_⟩
    rintro _ ⟨other, hother, rfl⟩
    exact hpoint hother
  exact hleast.csInf_eq.symm

theorem exists_minimizer (family : ℝ → X → ℝ) (parameter : ℝ)
    (hfamily : Continuous (family parameter)) :
    ∃ point, point ∈ minimizers family parameter ∧
      IsMinOn (family parameter) univ point := by
  obtain ⟨point, _, hpoint⟩ :=
    isCompact_univ.exists_isMinOn univ_nonempty hfamily.continuousOn
  exact ⟨point, minimum_eq_of_isMinOn family parameter point hpoint, hpoint⟩

theorem minimum_le (family : ℝ → X → ℝ) (parameter : ℝ)
    (hfamily : Continuous (family parameter)) (point : X) :
    minimum family parameter ≤ family parameter point := by
  obtain ⟨old, hold, hmin⟩ := exists_minimizer family parameter hfamily
  change family parameter old = minimum family parameter at hold
  rw [← hold]
  exact hmin (mem_univ point)

omit [Nonempty X] in
theorem isCompact_minimizers (family : ℝ → X → ℝ) (parameter : ℝ)
    (hfamily : Continuous (family parameter)) : IsCompact (minimizers family parameter) :=
  (isClosed_eq hfamily continuous_const).isCompact

/-- Select from all actual old minima, minimizing the parameter derivative among them. -/
theorem exists_derivative_minimizing_minimizer
    (family derivative : ℝ → X → ℝ) (parameter : ℝ)
    (hfamily : Continuous (family parameter)) (hderivative : Continuous (derivative parameter)) :
    ∃ point ∈ minimizers family parameter,
      ∀ other ∈ minimizers family parameter, derivative parameter point ≤
        derivative parameter other := by
  obtain ⟨old, hold, _⟩ := exists_minimizer family parameter hfamily
  obtain ⟨point, hpoint, hmin⟩ :=
    (isCompact_minimizers family parameter hfamily).exists_isMinOn ⟨old, hold⟩
      hderivative.continuousOn
  exact ⟨point, hpoint, hmin⟩

omit [CompactSpace X] [Nonempty X] in
theorem continuous_parameter_slice (family : ℝ → X → ℝ) (domain : Set ℝ)
    (hdomain : IsOpen domain)
    (hfamily : ContinuousOn (fun pair : ℝ × X => family pair.1 pair.2) (domain ×ˢ univ))
    {parameter : ℝ} (hparameter : parameter ∈ domain) :
    Continuous (family parameter) := by
  apply continuous_iff_continuousAt.mpr
  intro point
  exact (hfamily.continuousAt
    ((hdomain.prod isOpen_univ).mem_nhds ⟨hparameter, mem_univ point⟩)).comp
      (continuousAt_const.prodMk continuousAt_id)

omit [Nonempty X] in
/-- Compactness turns joint derivative continuity into one neighborhood valid for every point. -/
theorem eventually_uniform_derivative_close (derivative : ℝ → X → ℝ) (domain : Set ℝ)
    (hdomain : IsOpen domain)
    (hderivative : ContinuousOn (fun pair : ℝ × X => derivative pair.1 pair.2)
      (domain ×ˢ univ)) {parameter : ℝ} (hparameter : parameter ∈ domain)
    {error : ℝ} (herror : 0 < error) :
    ∀ᶠ time in 𝓝 parameter, ∀ point,
      ‖derivative time point - derivative parameter point‖ < error := by
  have hslice := continuous_parameter_slice derivative domain hdomain hderivative hparameter
  have huniform := isCompact_univ.eventually_forall_of_forall_eventually
    (x₀ := parameter) (P := fun time point =>
      ‖derivative time point - derivative parameter point‖ < error) ?_
  · exact huniform.mono fun time htime point => htime point (mem_univ point)
  · intro point _
    have hfirst := hderivative.continuousAt (x := (parameter, point))
      ((hdomain.prod isOpen_univ).mem_nhds ⟨hparameter, mem_univ point⟩)
    have hsecond : ContinuousAt (fun pair : ℝ × X => derivative parameter pair.2)
        (parameter, point) := hslice.continuousAt.comp continuousAt_snd
    exact (hfirst.sub hsecond).norm.tendsto.eventually
      (Iio_mem_nhds (by simpa using herror))

omit [Nonempty X] in
/-- Uniform Taylor error is derived from joint continuity of the actual first derivative. -/
theorem exists_uniform_first_order_error (family derivative : ℝ → X → ℝ)
    (domain : Set ℝ) (hdomain : IsOpen domain)
    (hderivative : ContinuousOn (fun pair : ℝ × X => derivative pair.1 pair.2)
      (domain ×ˢ univ))
    (hactual : ∀ time ∈ domain, ∀ point,
      HasDerivAt (fun value => family value point) (derivative time point) time)
    {parameter : ℝ} (hparameter : parameter ∈ domain)
    {error : ℝ} (herror : 0 < error) :
    ∃ radius > 0, Metric.ball parameter radius ⊆ domain ∧
      ∀ time ∈ Metric.ball parameter radius, ∀ point,
        ‖family time point - family parameter point -
            derivative parameter point * (time - parameter)‖ ≤ error * ‖time - parameter‖ := by
  have hclose := eventually_uniform_derivative_close derivative domain hdomain hderivative
    hparameter herror
  have hneighborhood := inter_mem (hdomain.mem_nhds hparameter) hclose
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  refine ⟨radius, hradius, fun time htime => (hball htime).1, ?_⟩
  intro time htime point
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun value => family value point - derivative parameter point * value)
    (f' := fun value => derivative value point - derivative parameter point)
    (s := Metric.ball parameter radius)
    (fun value hvalue => ((hactual value (hball hvalue).1 point).sub
      (hasDerivAt_const_mul (x := value) (derivative parameter point))).hasDerivWithinAt)
    (fun value hvalue => ((hball hvalue).2 point).le)
    (convex_ball parameter radius) (Metric.mem_ball_self hradius) htime
  have heq : (family time point - derivative parameter point * time) -
      (family parameter point - derivative parameter point * parameter) =
      family time point - family parameter point -
        derivative parameter point * (time - parameter) := by ring
  simpa only [heq] using hbound

def derivativeMinimum (family derivative : ℝ → X → ℝ) (parameter : ℝ) : ℝ :=
  sInf (derivative parameter '' minimizers family parameter)

/-- Every nearby new minimum has old derivative close to the least old derivative.
The compact neighborhood argument retains the whole old minimizer set. -/
theorem eventually_new_minimizer_derivative_lower_bound
    (family derivative : ℝ → X → ℝ) (domain : Set ℝ) (hdomain : IsOpen domain)
    (hfamily : ContinuousOn (fun pair : ℝ × X => family pair.1 pair.2) (domain ×ˢ univ))
    {parameter : ℝ} (hparameter : parameter ∈ domain)
    (hderivative : Continuous (derivative parameter)) (old : X)
    (hold : old ∈ minimizers family parameter)
    (hleast : ∀ point ∈ minimizers family parameter,
      derivative parameter old ≤ derivative parameter point)
    {error : ℝ} (herror : 0 < error) :
    ∀ᶠ time in 𝓝 parameter, ∀ point,
      IsMinOn (family time) univ point →
        derivative parameter old - error < derivative parameter point := by
  classical
  have hslice := continuous_parameter_slice family domain hdomain hfamily hparameter
  have huniform : ∀ᶠ time in 𝓝 parameter, ∀ point ∈ (univ : Set X),
      family time old < family time point ∨
        derivative parameter old - error < derivative parameter point := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro point _
    by_cases hpoint : point ∈ minimizers family parameter
    · have hstrict : derivative parameter old - error < derivative parameter point := by
        linarith [hleast point hpoint]
      have hderivativeAt : ContinuousAt
          (fun pair : ℝ × X => derivative parameter pair.2) (parameter, point) :=
        hderivative.continuousAt.comp continuousAt_snd
      have hlocal := hderivativeAt.tendsto.eventually
        (Ioi_mem_nhds hstrict)
      exact hlocal.mono fun pair hpair => Or.inr hpair
    · have hstrict : family parameter old < family parameter point := by
        have hvalue := minimum_le family parameter hslice point
        change family parameter point ≠ minimum family parameter at hpoint
        change family parameter old = minimum family parameter at hold
        rw [hold]
        exact lt_of_le_of_ne hvalue hpoint.symm
      have hpointAt := hfamily.continuousAt (x := (parameter, point))
        ((hdomain.prod isOpen_univ).mem_nhds ⟨hparameter, mem_univ point⟩)
      have holdAt : ContinuousAt (fun pair : ℝ × X => family pair.1 old)
          (parameter, point) :=
        (hfamily.continuousAt
          ((hdomain.prod isOpen_univ).mem_nhds ⟨hparameter, mem_univ old⟩)).comp
          (continuousAt_fst.prodMk continuousAt_const)
      have hlocal := (hpointAt.sub holdAt).tendsto.eventually
        (Ioi_mem_nhds (sub_pos.mpr hstrict))
      exact hlocal.mono fun pair hpair => Or.inl (sub_pos.mp hpair)
  filter_upwards [huniform] with time htime
  intro point hpoint
  rcases htime point (mem_univ point) with hgap | hclose
  · exact False.elim ((not_lt_of_ge (hpoint (mem_univ old))) hgap)
  · exact hclose

/-- Quotient bounds use a selected least old derivative, but produce every new minimizer
and all uniform first-order estimates internally. The public theorem selects the old point too. -/
theorem eventually_right_quotient_bounds
    (family derivative : ℝ → X → ℝ) (domain : Set ℝ) (hdomain : IsOpen domain)
    (hfamily : ContinuousOn (fun pair : ℝ × X => family pair.1 pair.2) (domain ×ˢ univ))
    (hderivative : ContinuousOn (fun pair : ℝ × X => derivative pair.1 pair.2)
      (domain ×ˢ univ))
    (hactual : ∀ time ∈ domain, ∀ point,
      HasDerivAt (fun value => family value point) (derivative time point) time)
    {parameter : ℝ} (hparameter : parameter ∈ domain) (old : X)
    (hold : old ∈ minimizers family parameter)
    (hleast : ∀ point ∈ minimizers family parameter,
      derivative parameter old ≤ derivative parameter point)
    {error : ℝ} (herror : 0 < error) :
    ∀ᶠ time in 𝓝 parameter, parameter < time →
      derivative parameter old - 2 * error ≤
        (minimum family time - minimum family parameter) / (time - parameter) ∧
      (minimum family time - minimum family parameter) / (time - parameter) ≤
        derivative parameter old + error := by
  have hderivativeSlice :=
    continuous_parameter_slice derivative domain hdomain hderivative hparameter
  have hnear := eventually_new_minimizer_derivative_lower_bound family derivative domain
    hdomain hfamily hparameter hderivativeSlice old hold hleast herror
  obtain ⟨radius, hradius, hdomainBall, herrorBall⟩ :=
    exists_uniform_first_order_error family derivative domain hdomain hderivative hactual
      hparameter herror
  filter_upwards [hnear, Metric.ball_mem_nhds parameter hradius] with time hnearTime htime
  intro hright
  have hstep : 0 < time - parameter := sub_pos.mpr hright
  have htimeDomain := hdomainBall htime
  have htimeSlice := continuous_parameter_slice family domain hdomain hfamily htimeDomain
  obtain ⟨new, hnew, hnewMin⟩ := exists_minimizer family time htimeSlice
  have hnewDerivative := hnearTime new hnewMin
  have holdError := herrorBall time htime old
  have hnewError := herrorBall time htime new
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hstep] at holdError hnewError
  have holdBounds := abs_le.mp holdError
  have hnewBounds := abs_le.mp hnewError
  have hvalueOld := minimum_le family time htimeSlice old
  have hparameterSlice := continuous_parameter_slice family domain hdomain hfamily hparameter
  have hvalueNew := minimum_le family parameter hparameterSlice new
  change family parameter old = minimum family parameter at hold
  change family time new = minimum family time at hnew
  rw [hold] at holdBounds
  rw [hnew] at hnewBounds
  refine ⟨(le_div_iff₀ hstep).mpr ?_, (div_le_iff₀ hstep).mpr ?_⟩
  · have hscaled := mul_le_mul_of_nonneg_right hnewDerivative.le hstep.le
    nlinarith [hnewBounds.1]
  · nlinarith [holdBounds.2]

/-- The right derivative of the compact minimum envelope is attained at ONE old minimum,
and is the minimum derivative over ALL old minima. No uniqueness is required. -/
theorem exists_right_derivative_minimizer
    (family derivative : ℝ → X → ℝ) (domain : Set ℝ) (hdomain : IsOpen domain)
    (hfamily : ContinuousOn (fun pair : ℝ × X => family pair.1 pair.2) (domain ×ˢ univ))
    (hderivative : ContinuousOn (fun pair : ℝ × X => derivative pair.1 pair.2)
      (domain ×ˢ univ))
    (hactual : ∀ time ∈ domain, ∀ point,
      HasDerivAt (fun value => family value point) (derivative time point) time)
    {parameter : ℝ} (hparameter : parameter ∈ domain) :
    ∃ point ∈ minimizers family parameter,
      derivative parameter point = derivativeMinimum family derivative parameter ∧
      (∀ other ∈ minimizers family parameter,
        derivative parameter point ≤ derivative parameter other) ∧
      HasDerivWithinAt (minimum family) (derivativeMinimum family derivative parameter)
        (Ici parameter) parameter := by
  have hfamilySlice := continuous_parameter_slice family domain hdomain hfamily hparameter
  have hderivativeSlice :=
    continuous_parameter_slice derivative domain hdomain hderivative hparameter
  obtain ⟨point, hpoint, hleast⟩ :=
    exists_derivative_minimizing_minimizer family derivative parameter
      hfamilySlice hderivativeSlice
  have hvalue : derivative parameter point = derivativeMinimum family derivative parameter := by
    have hleastImage : IsLeast (derivative parameter '' minimizers family parameter)
        (derivative parameter point) := by
      refine ⟨⟨point, hpoint, rfl⟩, ?_⟩
      rintro _ ⟨other, hother, rfl⟩
      exact hleast other hother
    exact hleastImage.csInf_eq.symm
  refine ⟨point, hpoint, hvalue, hleast, ?_⟩
  rw [← hvalue, hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ici parameter \ {parameter} = Ioi parameter := by
    ext time
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨hge, hne⟩
      exact lt_of_le_of_ne hge (fun heq => hne heq.symm)
    · intro hlt
      exact ⟨hlt.le, ne_of_gt hlt⟩
  rw [hset]
  apply Metric.tendsto_nhds.mpr
  intro error herror
  have hthird : 0 < error / 3 := by positivity
  have hbounds := eventually_right_quotient_bounds family derivative domain hdomain hfamily
    hderivative hactual hparameter point hpoint hleast hthird
  filter_upwards [hbounds.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with time hboundsTime htime
  obtain ⟨hlower, hupper⟩ := hboundsTime htime
  rw [slope_def_field, Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

end Math.CompactMinimumEnvelope
