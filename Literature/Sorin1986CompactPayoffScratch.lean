import Sorin1986CompactScratch

noncomputable section

namespace Literature.Sorin1986

open GameTheory Set Filter
open scoped BigOperators Topology

namespace SequenceForm

/-- A fixed pure action used only to witness nonemptiness of the realization
polytope. -/
noncomputable def defaultAction (G : FiniteStageGame) (who : G.Player) :
    G.Action who :=
  Classical.choice (inferInstance : Nonempty (G.Action who))

/-- A public history follows the fixed pure strategy of `who`. -/
def FollowsDefault {G : FiniteStageGame} (who : G.Player)
    (h : History G) : Prop :=
  ∀ k, h.2 k who = defaultAction G who

@[simp] theorem followsDefault_empty
    (G : FiniteStageGame) (who : G.Player) :
    FollowsDefault who (emptyHistory G) := by
  intro k
  exact k.elim0

@[simp] theorem followsDefault_snoc_iff
    {G : FiniteStageGame} (who : G.Player)
    (h : History G) (a : JointAction G) :
    FollowsDefault who (snocHistory h a) ↔
      FollowsDefault who h ∧ a who = defaultAction G who := by
  constructor
  · intro hs
    constructor
    · intro k
      have hk := hs (Fin.castSucc k)
      simpa [snocHistory] using hk
    · have hk := hs (Fin.last h.1)
      simpa [snocHistory] using hk
  · rintro ⟨hh, ha⟩ k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simpa [snocHistory] using ha
    · simpa [snocHistory] using hh j

/-- The endpoints of the unit interval. -/
def intervalZero : UnitInterval := ⟨0, by norm_num⟩
def intervalOne : UnitInterval := ⟨1, by norm_num⟩

/-- Indicator valued in the unit interval. -/
noncomputable def intervalIndicator (p : Prop) : UnitInterval :=
  if p then intervalOne else intervalZero

@[simp] theorem intervalIndicator_true {p : Prop} (hp : p) :
    (intervalIndicator p : ℝ) = 1 := by
  simp [intervalIndicator, hp, intervalOne]

@[simp] theorem intervalIndicator_false {p : Prop} (hp : ¬p) :
    (intervalIndicator p : ℝ) = 0 := by
  simp [intervalIndicator, hp, intervalZero]

/-- The realization plan of the fixed pure strategy. -/
noncomputable def defaultRawRealizationPlan
    (G : FiniteStageGame) (who : G.Player) :
    RawRealizationPlan G who :=
  (fun h => intervalIndicator (FollowsDefault who h),
    fun h a => intervalIndicator
      (FollowsDefault who h ∧ a = defaultAction G who))

private theorem defaultRawRealizationPlan_valid
    (G : FiniteStageGame) (who : G.Player) :
    (defaultRawRealizationPlan G who).Valid := by
  classical
  constructor
  · simp [defaultRawRealizationPlan]
  constructor
  · intro h
    by_cases hh : FollowsDefault who h
    · simp [defaultRawRealizationPlan, hh, intervalIndicator,
        intervalOne, intervalZero]
    · simp [defaultRawRealizationPlan, hh, intervalIndicator,
        intervalOne, intervalZero]
  · intro h a
    simp [defaultRawRealizationPlan, followsDefault_snoc_iff,
      intervalIndicator, intervalOne, intervalZero]

/-- A canonical pure realization plan. -/
noncomputable def defaultRealizationPlan
    (G : FiniteStageGame) (who : G.Player) :
    RealizationPlan G who :=
  ⟨defaultRawRealizationPlan G who,
    defaultRawRealizationPlan_valid G who⟩

instance {G : FiniteStageGame} {who : G.Player} :
    Nonempty (RealizationPlan G who) :=
  ⟨defaultRealizationPlan G who⟩

/-- A profile of sequence-form realization plans. -/
abbrev RealizationProfile (G : FiniteStageGame) :=
  ∀ who, RealizationPlan G who

/-- Realization weight of one player's action sequence at a public history. -/
def actionWeight {G : FiniteStageGame} {who : G.Player}
    (plan : RealizationPlan G who) (h : History G)
    (a : G.Action who) : ℝ :=
  plan.1.2 h a

/-- Probability of a public history under a realization-plan profile. -/
def historyMass {G : FiniteStageGame}
    (profile : RealizationProfile G) (h : History G) : ℝ :=
  ∏ who, (profile who).1.1 h

/-- Probability of a public history followed by one joint action. -/
def actionMass {G : FiniteStageGame}
    (profile : RealizationProfile G) (h : History G)
    (a : JointAction G) : ℝ :=
  ∏ who, actionWeight (profile who) h (a who)

@[fun_prop] theorem continuous_historyMass (G : FiniteStageGame)
    (h : History G) :
    Continuous fun profile : RealizationProfile G => historyMass profile h := by
  classical
  fun_prop

@[fun_prop] theorem continuous_actionMass (G : FiniteStageGame)
    (h : History G) (a : JointAction G) :
    Continuous fun profile : RealizationProfile G => actionMass profile h a := by
  classical
  fun_prop

theorem historyMass_nonneg {G : FiniteStageGame}
    (profile : RealizationProfile G) (h : History G) :
    0 ≤ historyMass profile h := by
  classical
  exact Finset.prod_nonneg fun who _ => (profile who).1.1 h |>.2.1

theorem actionMass_nonneg {G : FiniteStageGame}
    (profile : RealizationProfile G) (h : History G)
    (a : JointAction G) :
    0 ≤ actionMass profile h a := by
  classical
  exact Finset.prod_nonneg fun who _ =>
    ((profile who).1.2 h (a who)).2.1

end SequenceForm

end Literature.Sorin1986
