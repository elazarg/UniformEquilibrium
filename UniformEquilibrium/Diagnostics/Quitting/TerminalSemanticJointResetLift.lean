/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Probability.FinitePMF
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# Exact joint-reset lift of terminal semantic prefixes

A finite quitting root has one coupled joint action.  Recording, for the
prescribed payoff block and for every envelope coordinate, whether that action
retains the tail or resets it to a terminal reward gives a finite reset mode.
The induced finite law reproduces the terminal semantic prefix exactly.

The same construction transports an arbitrary law on reset modes.  Projection
to semantic pairs then commutes with the transition.  This is a representation
theorem only: it supplies no positive-debt invariant for the reachable law
space.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A terminal label is a nonempty quitting coalition. -/
abbrev QuittingTerminalLabel (ι : Type) [Fintype ι] :=
  {S : Finset ι // S.Nonempty}

/-- The terminal label selected by a pure joint action, or `none` when every
player continues. -/
def quittingTerminalLabel (action : ι → Bool) : Option (QuittingTerminalLabel ι) :=
  if h : (quittingQuitters action).Nonempty then
    some ⟨quittingQuitters action, h⟩
  else none

/-- Read a terminal label against a tail payoff. -/
def quittingTerminalLabelValue
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (tail : Payoff ι) (label : Option (QuittingTerminalLabel ι)) : Payoff ι :=
  match label with
  | none => tail
  | some S => reward S

omit [DecidableEq ι] in
@[simp]
theorem quittingTerminalLabelValue_label
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (tail : Payoff ι) (action : ι → Bool) (who : ι) :
    quittingTerminalLabelValue reward tail (quittingTerminalLabel action) who =
      quittingRootPayoff reward tail action who := by
  unfold quittingTerminalLabel quittingTerminalLabelValue quittingRootPayoff
  split <;> rfl

/-- A reset mode either retains or resets the whole prescribed-payoff block,
and independently retains or resets each envelope coordinate.  A single mode
does not assert simultaneous realizability of the counterfactual coordinates.
-/
structure QuittingJointResetMode (ι : Type) [Fintype ι] where
  payoff : Option (QuittingTerminalLabel ι)
  cap : ι → Option (QuittingTerminalLabel ι)

omit [DecidableEq ι] in
theorem QuittingJointResetMode.eq_of_fields
    {first second : QuittingJointResetMode ι}
    (hpayoff : first.payoff = second.payoff)
    (hcap : ∀ who, first.cap who = second.cap who) : first = second := by
  rcases first with ⟨firstPayoff, firstCap⟩
  rcases second with ⟨secondPayoff, secondCap⟩
  dsimp only at hpayoff hcap
  subst secondPayoff
  have hfunction : firstCap = secondCap := funext hcap
  subst secondCap
  rfl

instance : Fintype (QuittingJointResetMode ι) :=
  Fintype.ofEquiv
    (Option (QuittingTerminalLabel ι) ×
      (ι → Option (QuittingTerminalLabel ι)))
    { toFun := fun pair => ⟨pair.1, pair.2⟩
      invFun := fun mode => (mode.payoff, mode.cap)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Apply a reset mode to a semantic pair. -/
def QuittingJointResetMode.apply
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (mode : QuittingJointResetMode ι)
    (pair : QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  (quittingTerminalLabelValue reward pair.1 mode.payoff,
    fun who => quittingTerminalLabelValue reward pair.2 (mode.cap who) who)

/-- Outer composition of reset modes: an outer reset overwrites an inner
label, while an outer identity retains it. -/
def QuittingJointResetMode.comp
    (outer inner : QuittingJointResetMode ι) : QuittingJointResetMode ι where
  payoff := outer.payoff.orElse fun _ => inner.payoff
  cap := fun who => (outer.cap who).orElse fun _ => inner.cap who

omit [DecidableEq ι] in
@[simp]
theorem QuittingJointResetMode.apply_comp
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (outer inner : QuittingJointResetMode ι)
    (pair : QuittingTerminalSemanticPair ι) :
    (outer.comp inner).apply reward pair =
      outer.apply reward (inner.apply reward pair) := by
  apply Prod.ext
  · funext who
    cases h : outer.payoff <;>
      simp [QuittingJointResetMode.apply, QuittingJointResetMode.comp,
        quittingTerminalLabelValue, h]
  · funext who
    cases h : outer.cap who <;>
      simp [QuittingJointResetMode.apply, QuittingJointResetMode.comp,
        quittingTerminalLabelValue, h]

/-- The identity reset mode. -/
def quittingJointResetIdentity : QuittingJointResetMode ι where
  payoff := none
  cap := fun _ => none

omit [DecidableEq ι] in
@[simp]
theorem QuittingJointResetMode.identity_comp
    (mode : QuittingJointResetMode ι) :
    quittingJointResetIdentity.comp mode = mode := by
  apply QuittingJointResetMode.eq_of_fields
  · rfl
  · intro who
    rfl

omit [DecidableEq ι] in
@[simp]
theorem QuittingJointResetMode.comp_identity
    (mode : QuittingJointResetMode ι) :
    mode.comp quittingJointResetIdentity = mode := by
  apply QuittingJointResetMode.eq_of_fields
  · cases h : mode.payoff <;>
      simp [QuittingJointResetMode.comp, quittingJointResetIdentity, h]
  · intro who
    cases h : mode.cap who <;>
      simp [QuittingJointResetMode.comp, quittingJointResetIdentity, h]

omit [DecidableEq ι] in
theorem QuittingJointResetMode.comp_assoc
    (outer middle inner : QuittingJointResetMode ι) :
    (outer.comp middle).comp inner = outer.comp (middle.comp inner) := by
  apply QuittingJointResetMode.eq_of_fields
  · cases houter : outer.payoff <;> cases hmiddle : middle.payoff <;>
      simp [QuittingJointResetMode.comp, houter, hmiddle]
  · intro who
    cases houter : outer.cap who <;> cases hmiddle : middle.cap who <;>
      simp [QuittingJointResetMode.comp, houter, hmiddle]

/-- Semantic coordinates reset by a mode. `none` denotes the prescribed-payoff
block and `some who` denotes player `who`'s envelope coordinate. -/
def QuittingJointResetMode.resetSupport
    (mode : QuittingJointResetMode ι) : Finset (Option ι) := by
  classical
  exact Finset.univ.filter fun coordinate =>
    match coordinate with
    | none => mode.payoff.isSome
    | some who => (mode.cap who).isSome

omit [DecidableEq ι] in
@[simp]
theorem QuittingJointResetMode.resetSupport_identity :
    (quittingJointResetIdentity : QuittingJointResetMode ι).resetSupport = ∅ := by
  ext coordinate
  cases coordinate <;>
    simp [QuittingJointResetMode.resetSupport, quittingJointResetIdentity]

/-- Outer composition resets exactly the union of the coordinates reset by
either factor. -/
theorem QuittingJointResetMode.resetSupport_comp
    (outer inner : QuittingJointResetMode ι) :
    (outer.comp inner).resetSupport =
      outer.resetSupport ∪ inner.resetSupport := by
  ext coordinate
  cases coordinate with
  | none =>
      cases houter : outer.payoff <;>
        simp [QuittingJointResetMode.resetSupport,
          QuittingJointResetMode.comp, houter]
  | some who =>
      cases houter : outer.cap who <;>
        simp [QuittingJointResetMode.resetSupport,
          QuittingJointResetMode.comp, houter]

omit [DecidableEq ι] in
@[simp]
theorem quittingJointResetIdentity_apply
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) :
    (quittingJointResetIdentity : QuittingJointResetMode ι).apply reward pair = pair := by
  rfl

omit [DecidableEq ι] in
@[simp]
theorem QuittingJointResetMode.comp_self
    (mode : QuittingJointResetMode ι) : mode.comp mode = mode := by
  apply QuittingJointResetMode.eq_of_fields
  · change mode.payoff.orElse (fun _ => mode.payoff) = mode.payoff
    cases mode.payoff <;> rfl
  · intro who
    change (mode.cap who).orElse (fun _ => mode.cap who) = mode.cap who
    cases mode.cap who <;> rfl

omit [DecidableEq ι] in
/-- Reset modes form a left-regular band under outer composition. -/
theorem QuittingJointResetMode.comp_comp_self
    (outer inner : QuittingJointResetMode ι) :
    (outer.comp inner).comp outer = outer.comp inner := by
  apply QuittingJointResetMode.eq_of_fields
  · change (outer.payoff.orElse (fun _ => inner.payoff)).orElse
        (fun _ => outer.payoff) =
      outer.payoff.orElse (fun _ => inner.payoff)
    cases outer.payoff <;> cases inner.payoff <;> rfl
  · intro who
    change ((outer.cap who).orElse (fun _ => inner.cap who)).orElse
        (fun _ => outer.cap who) =
      (outer.cap who).orElse (fun _ => inner.cap who)
    cases outer.cap who <;> cases inner.cap who <;> rfl

/-- One pure coupled action, with a global endpoint selector, produces one
joint reset mode. `true` selects the forced-Quit endpoint. -/
def quittingElementaryJointReset
    (selector : ι → Bool) (action : ι → Bool) : QuittingJointResetMode ι where
  payoff := quittingTerminalLabel action
  cap := fun who =>
    quittingTerminalLabel (Function.update action who (selector who))

/-- The finite independent joint-action law of one product root. -/
def quittingJointActionLaw (root : ι → PMF Bool) : FinDist (ι → Bool) :=
  FinDist.pi fun who => _root_.Math.Probability.finDistOfPMF (root who)

omit [DecidableEq ι] in
private theorem quittingJointActionLaw_toPMF
    (root : ι → PMF Bool) :
    (quittingJointActionLaw root).toPMF = pmfPi root := by
  apply PMF.ext
  intro action
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).1
  rw [← FinDist.prob_def]
  unfold quittingJointActionLaw
  rw [FinDist.prob_pi]
  simp only [_root_.Math.Probability.finDistOfPMF, FinDist.prob_def]
  rw [pmfPi_apply, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun _ _ => rfl

omit [DecidableEq ι] in
private theorem quittingJointActionLaw_expect
    (root : ι → PMF Bool) (observable : (ι → Bool) → ℝ) :
    (quittingJointActionLaw root).expect observable =
      Math.Probability.expect (pmfPi root) observable := by
  change Math.Probability.expect (quittingJointActionLaw root).toPMF observable = _
  rw [quittingJointActionLaw_toPMF]

/-- Forcing one coordinate of the coupled action law is the product law with
that coordinate replaced by the corresponding point mass. -/
theorem quittingJointActionLaw_map_update
    (root : ι → PMF Bool) (who : ι) (choice : Bool) :
    (quittingJointActionLaw root).map
        (fun action => Function.update action who choice) =
      quittingJointActionLaw (Function.update root who (PMF.pure choice)) := by
  let relabel : (player : ι) → Bool → Bool := fun player =>
    if player = who then fun _ => choice else id
  have hfactor :
      (fun player => FinDist.map (relabel player)
        (_root_.Math.Probability.finDistOfPMF (root player))) =
        fun player => _root_.Math.Probability.finDistOfPMF
          ((Function.update root who (PMF.pure choice)) player) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [show relabel who = fun _ => choice by simp [relabel]]
      rw [FinDist.map_const]
      simp
    · rw [show relabel player = id by simp [relabel, hplayer], FinDist.map_id]
      simp [hplayer]
  have htuple :
      (fun action player => relabel player (action player)) =
        fun action => Function.update action who choice := by
    funext action player
    by_cases hplayer : player = who
    · subst player
      simp [relabel]
    · simp [relabel, hplayer]
  unfold quittingJointActionLaw
  calc
    FinDist.map (fun action => Function.update action who choice)
        (FinDist.pi fun player =>
          _root_.Math.Probability.finDistOfPMF (root player)) =
      FinDist.map (fun action player => relabel player (action player))
        (FinDist.pi fun player =>
          _root_.Math.Probability.finDistOfPMF (root player)) := by rw [htuple]
    _ = FinDist.pi (fun player => FinDist.map (relabel player)
        (_root_.Math.Probability.finDistOfPMF (root player))) :=
      (FinDist.pi_map relabel _).symm
    _ = FinDist.pi (fun player => _root_.Math.Probability.finDistOfPMF
        ((Function.update root who (PMF.pure choice)) player)) := by rw [hfactor]

private theorem expect_pmfPi_update_pure
    (root : ι → PMF Bool) (who : ι) (choice : Bool)
    (observable : (ι → Bool) → ℝ) :
    Math.Probability.expect
        (pmfPi (Function.update root who (PMF.pure choice))) observable =
      Math.Probability.expect (pmfPi root)
        (fun action => observable (Function.update action who choice)) := by
  rw [← pmfPi_bind_update_pure root who choice,
    Math.Probability.expect_bind]
  simp

omit [DecidableEq ι] in
theorem quittingTerminalLabel_eq_none_iff
    (action : ι → Bool) :
    quittingTerminalLabel action = none ↔
      action = (quittingAllContinueAction : ι → Bool) := by
  unfold quittingTerminalLabel
  by_cases hnonempty : (quittingQuitters action).Nonempty
  · rw [dif_pos hnonempty]
    simp only [Option.some_ne_none, false_iff]
    intro hcontinue
    subst action
    simp [quittingQuitters, quittingAllContinueAction] at hnonempty
  · rw [dif_neg hnonempty]
    constructor
    · intro _
      funext who
      unfold quittingAllContinueAction
      cases hchoice : action who with
      | false => rfl
      | true =>
          exfalso
          apply hnonempty
          rw [quittingQuitters_nonempty_iff]
          exact ⟨who, hchoice⟩
    · intro _
      rfl

omit [DecidableEq ι] in
/-- The reset action has no payoff label exactly with the ordinary
all-Continue root mass. -/
theorem quittingJointActionLaw_prob_terminalLabel_none
    (root : ι → PMF Bool) :
    (quittingJointActionLaw root).probOf
        {action | quittingTerminalLabel action = none} =
      quittingStationaryContinueMass root := by
  have hevent :
      {action : ι → Bool | quittingTerminalLabel action = none} =
        {quittingAllContinueAction} := by
    ext action
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff,
      quittingTerminalLabel_eq_none_iff]
  rw [hevent, FinDist.probOf_singleton, FinDist.prob_def,
    quittingJointActionLaw_toPMF]
  rfl

/-- The no-reset probability of one envelope coordinate is zero under a
forced-Quit selection and is the opponents' Continue mass under a
forced-Continue selection. -/
theorem quittingJointActionLaw_prob_capLabel_none
    (root : ι → PMF Bool) (selector : ι → Bool) (who : ι) :
    (quittingJointActionLaw root).probOf {action |
        quittingTerminalLabel
          (Function.update action who (selector who)) = none} =
      if selector who then 0 else quittingRootOpponentContinueMass root who := by
  calc
    (quittingJointActionLaw root).probOf {action |
        quittingTerminalLabel
          (Function.update action who (selector who)) = none} =
      ((quittingJointActionLaw root).map
        (fun action => Function.update action who (selector who))).probOf
          {action | quittingTerminalLabel action = none} := by
        rw [FinDist.probOf_map]
        apply congrArg (quittingJointActionLaw root).probOf
        ext action
        rfl
    _ = quittingStationaryContinueMass
        (Function.update root who (PMF.pure (selector who))) := by
      rw [quittingJointActionLaw_map_update,
        quittingJointActionLaw_prob_terminalLabel_none]
    _ = if selector who then 0 else
        quittingRootOpponentContinueMass root who := by
      by_cases hselector : selector who
      · rw [if_pos hselector, hselector]
        unfold quittingStationaryContinueMass
        rw [pmfPi_apply, ENNReal.toReal_prod,
          Finset.prod_eq_zero (Finset.mem_univ who)]
        simp [quittingAllContinueAction]
      · rw [if_neg hselector]
        have hfalse : selector who = false := Bool.eq_false_of_not_eq_true hselector
        rw [hfalse]
        rfl

/-- Expected application of one elementary joint reset. -/
def quittingJointResetStep
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (root : ι → PMF Bool) (selector : ι → Bool)
    (pair : QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  (fun who => (quittingJointActionLaw root).expect fun action =>
      (quittingElementaryJointReset selector action).apply reward pair |>.1 who,
    fun who => (quittingJointActionLaw root).expect fun action =>
      (quittingElementaryJointReset selector action).apply reward pair |>.2 who)

private theorem quittingJointResetStep_payoff
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (root : ι → PMF Bool) (selector : ι → Bool)
    (pair : QuittingTerminalSemanticPair ι) (who : ι) :
    (quittingJointResetStep reward root selector pair).1 who =
      quittingRootSuccessorPayoff reward pair.1 root who := by
  change (quittingJointActionLaw root).expect (fun action =>
      quittingTerminalLabelValue reward pair.1
        (quittingTerminalLabel action) who) = _
  rw [quittingJointActionLaw_expect]
  simp only [quittingTerminalLabelValue_label]
  rfl

private theorem quittingRootQuitPayoff_tail_irrel
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitPayoff reward first root who =
      quittingRootQuitPayoff reward second root who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_update_pure root who true,
    expect_pmfPi_update_pure root who true]
  apply congrArg (Math.Probability.expect (pmfPi root))
  funext action
  have hnonempty :
      (quittingQuitters (Function.update action who true)).Nonempty := by
    rw [quittingQuitters_nonempty_iff]
    refine ⟨who, ?_⟩
    simp
  simp only [quittingRootPayoff, hnonempty, dite_true]

private theorem quittingJointResetStep_cap
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (root : ι → PMF Bool) (selector : ι → Bool)
    (pair : QuittingTerminalSemanticPair ι) (who : ι) :
    (quittingJointResetStep reward root selector pair).2 who =
      if selector who then
        quittingRootQuitPayoff reward
          (Function.update pair.1 who (pair.2 who)) root who
      else
        quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who := by
  change (quittingJointActionLaw root).expect (fun action =>
      quittingTerminalLabelValue reward pair.2
        (quittingTerminalLabel
          (Function.update action who (selector who))) who) = _
  rw [quittingJointActionLaw_expect]
  by_cases hselector : selector who
  · rw [if_pos hselector]
    rw [hselector]
    rw [← expect_pmfPi_update_pure root who true
      (fun action => quittingTerminalLabelValue reward pair.2
        (quittingTerminalLabel action) who)]
    simp only [quittingTerminalLabelValue_label]
    exact quittingRootQuitPayoff_tail_irrel reward pair.2
      (Function.update pair.1 who (pair.2 who)) root who
  · rw [if_neg hselector]
    have hfalse : selector who = false := Bool.eq_false_of_not_eq_true hselector
    rw [hfalse]
    rw [← expect_pmfPi_update_pure root who false
      (fun action => quittingTerminalLabelValue reward pair.2
        (quittingTerminalLabel action) who)]
    simp only [quittingTerminalLabelValue_label]
    unfold quittingRootContinuePayoff quittingRootExpectedPayoff
    apply congrArg (Math.Probability.expect
      (pmfPi (Function.update root who (PMF.pure false))))
    funext action
    unfold quittingRootPayoff
    split
    · rfl
    · simp

/-- A selector chooses a maximizing endpoint at every player coordinate. -/
def IsQuittingJointResetSelector
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι)
    (selector : ι → Bool) : Prop :=
  ∀ who,
    if selector who then
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who ≤
        quittingRootQuitPayoff reward pair.1 root who
    else
      quittingRootQuitPayoff reward pair.1 root who ≤
        quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who

/-- A canonical global maximizing selector, resolving endpoint ties toward
forced Quit. -/
def quittingMaxJointResetSelector
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι) : ι → Bool :=
  fun who => decide
    (quittingRootContinuePayoff reward
        (Function.update pair.1 who (pair.2 who)) root who ≤
      quittingRootQuitPayoff reward pair.1 root who)

theorem isQuittingJointResetSelector_max
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι) :
    IsQuittingJointResetSelector reward root pair
      (quittingMaxJointResetSelector reward root pair) := by
  intro who
  unfold quittingMaxJointResetSelector
  by_cases hmax : quittingRootContinuePayoff reward
      (Function.update pair.1 who (pair.2 who)) root who ≤
    quittingRootQuitPayoff reward pair.1 root who
  · simp [hmax]
  · simp [hmax, le_of_not_ge hmax]

/-- A maximizing global selector makes the expected joint reset exactly the
terminal semantic prefix. -/
theorem quittingJointResetStep_eq_semanticPrefix
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (root : ι → PMF Bool) (selector : ι → Bool)
    (pair : QuittingTerminalSemanticPair ι)
    (hselector : IsQuittingJointResetSelector reward root pair selector) :
    quittingJointResetStep reward root selector pair =
      quittingTerminalSemanticPrefix reward root pair := by
  apply Prod.ext
  · funext who
    exact quittingJointResetStep_payoff reward root selector pair who
  · funext who
    rw [quittingJointResetStep_cap]
    unfold quittingTerminalSemanticPrefix
    dsimp only
    by_cases hchoice : selector who
    · rw [if_pos hchoice]
      rw [quittingRootQuitPayoff_tail_irrel reward
        (Function.update pair.1 who (pair.2 who)) pair.1]
      have hmax := hselector who
      simp [hchoice] at hmax
      exact (max_eq_left hmax).symm
    · rw [if_neg hchoice]
      have hmax := hselector who
      simp [hchoice] at hmax
      exact (max_eq_right hmax).symm

/-- The canonical maximizing selector gives the semantic prefix without any
additional hypothesis. -/
theorem quittingJointResetStep_max_eq_semanticPrefix
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι) :
    quittingJointResetStep reward root
        (quittingMaxJointResetSelector reward root pair) pair =
      quittingTerminalSemanticPrefix reward root pair :=
  quittingJointResetStep_eq_semanticPrefix reward root _ pair
    (isQuittingJointResetSelector_max reward root pair)

/-! ## Law-level transition -/

/-- Project a finite reset-mode law to its expected terminal semantic pair. -/
def quittingJointResetProjection
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι)
    (law : FinDist (QuittingJointResetMode ι)) :
    QuittingTerminalSemanticPair ι :=
  (fun who => law.expect fun mode => (mode.apply reward anchor).1 who,
    fun who => law.expect fun mode => (mode.apply reward anchor).2 who)

omit [DecidableEq ι] in
@[simp]
theorem quittingJointResetProjection_pure_identity
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι) :
    quittingJointResetProjection reward anchor
        (FinDist.pure (quittingJointResetIdentity : QuittingJointResetMode ι)) =
      anchor := by
  apply Prod.ext <;> funext who <;>
    simp [quittingJointResetProjection]

/-- Tag every reset mode with one coupled joint-action draw. -/
def quittingJointResetTaggedLaw
    (root : ι → PMF Bool) (law : FinDist (QuittingJointResetMode ι)) :
    FinDist (QuittingJointResetMode ι × (ι → Bool)) :=
  law.bind fun mode =>
    (quittingJointActionLaw root).map fun action => (mode, action)

omit [DecidableEq ι] in
/-- The tagged law has exactly the product point masses. -/
theorem quittingJointResetTaggedLaw_prob
    (root : ι → PMF Bool) (law : FinDist (QuittingJointResetMode ι))
    (mode : QuittingJointResetMode ι) (action : ι → Bool) :
    (quittingJointResetTaggedLaw root law).prob (mode, action) =
      law.prob mode * (quittingJointActionLaw root).prob action := by
  exact FinDist.prob_bind_map_prod law
    (fun _ => quittingJointActionLaw root) mode action

/-- Apply the elementary reset outside each mode in a tagged law. -/
def quittingJointResetTransition
    (root : ι → PMF Bool) (selector : ι → Bool)
    (law : FinDist (QuittingJointResetMode ι)) :
    FinDist (QuittingJointResetMode ι) :=
  (quittingJointResetTaggedLaw root law).map fun tagged =>
    (quittingElementaryJointReset selector tagged.2).comp tagged.1

/-- One transition retains the payoff anchor exactly when both the sampled
action and the incoming mode retain it. -/
theorem quittingJointResetTransition_payoffIdentityMass
    (root : ι → PMF Bool) (selector : ι → Bool)
    (law : FinDist (QuittingJointResetMode ι)) :
    (quittingJointResetTransition root selector law).probOf
        {mode | mode.payoff = none} =
      quittingStationaryContinueMass root *
        law.probOf {mode | mode.payoff = none} := by
  rw [← FinDist.expect_indicator_eq_probOf]
  unfold quittingJointResetTransition quittingJointResetTaggedLaw
  rw [FinDist.expect_map, FinDist.expect_bind]
  simp_rw [FinDist.expect_map]
  calc
    law.expect (fun mode => (quittingJointActionLaw root).expect fun action =>
        if ((quittingElementaryJointReset selector action).comp mode) ∈
            {mode | mode.payoff = none} then 1 else 0) =
      law.expect (fun mode =>
        (if mode ∈ {mode | mode.payoff = none} then 1 else 0) *
          quittingStationaryContinueMass root) := by
        apply FinDist.expect_congr
        intro mode _
        by_cases hmode : mode.payoff = none
        · have hrelabel :
              (quittingJointActionLaw root).expect (fun action =>
                if ((quittingElementaryJointReset selector action).comp mode) ∈
                    {mode | mode.payoff = none} then 1 else 0) =
              (quittingJointActionLaw root).expect (fun action =>
                if action ∈ {action | quittingTerminalLabel action = none}
                  then 1 else 0) := by
              apply FinDist.expect_congr
              intro action _
              simp [QuittingJointResetMode.comp, hmode,
                quittingElementaryJointReset]
          rw [hrelabel]
          rw [FinDist.expect_indicator_eq_probOf,
            quittingJointActionLaw_prob_terminalLabel_none]
          simp [hmode]
        · have hzero :
              (quittingJointActionLaw root).expect (fun action =>
                if ((quittingElementaryJointReset selector action).comp mode) ∈
                    {mode | mode.payoff = none} then 1 else 0) =
              (quittingJointActionLaw root).expect (fun _ => (0 : ℝ)) := by
              apply FinDist.expect_congr
              intro action _
              simp [QuittingJointResetMode.comp, hmode,
                quittingElementaryJointReset]
          rw [hzero]
          simp [hmode]
    _ = law.expect
        (fun mode => if mode ∈ {mode | mode.payoff = none} then 1 else 0) *
          quittingStationaryContinueMass root :=
      FinDist.expect_mul_const law _ _
    _ = law.probOf {mode | mode.payoff = none} *
          quittingStationaryContinueMass root := by
      rw [FinDist.expect_indicator_eq_probOf]
    _ = quittingStationaryContinueMass root *
          law.probOf {mode | mode.payoff = none} := mul_comm _ _

/-- One transition retains envelope coordinate `who` exactly when the sampled
forced endpoint and the incoming mode both retain it. -/
theorem quittingJointResetTransition_capIdentityMass
    (root : ι → PMF Bool) (selector : ι → Bool)
    (law : FinDist (QuittingJointResetMode ι)) (who : ι) :
    (quittingJointResetTransition root selector law).probOf
        {mode | mode.cap who = none} =
      (if selector who then 0 else quittingRootOpponentContinueMass root who) *
        law.probOf {mode | mode.cap who = none} := by
  rw [← FinDist.expect_indicator_eq_probOf]
  unfold quittingJointResetTransition quittingJointResetTaggedLaw
  rw [FinDist.expect_map, FinDist.expect_bind]
  simp_rw [FinDist.expect_map]
  let retained := if selector who then 0 else
    quittingRootOpponentContinueMass root who
  calc
    law.expect (fun mode => (quittingJointActionLaw root).expect fun action =>
        if ((quittingElementaryJointReset selector action).comp mode) ∈
            {mode | mode.cap who = none} then 1 else 0) =
      law.expect (fun mode =>
        (if mode ∈ {mode | mode.cap who = none} then 1 else 0) * retained) := by
        apply FinDist.expect_congr
        intro mode _
        by_cases hmode : mode.cap who = none
        · have hrelabel :
              (quittingJointActionLaw root).expect (fun action =>
                if ((quittingElementaryJointReset selector action).comp mode) ∈
                    {mode | mode.cap who = none} then 1 else 0) =
              (quittingJointActionLaw root).expect (fun action =>
                if action ∈ {action | quittingTerminalLabel
                    (Function.update action who (selector who)) = none}
                  then 1 else 0) := by
              apply FinDist.expect_congr
              intro action _
              simp [QuittingJointResetMode.comp, hmode,
                quittingElementaryJointReset]
          rw [hrelabel]
          rw [FinDist.expect_indicator_eq_probOf,
            quittingJointActionLaw_prob_capLabel_none]
          simp [retained, hmode]
        · have hzero :
              (quittingJointActionLaw root).expect (fun action =>
                if ((quittingElementaryJointReset selector action).comp mode) ∈
                    {mode | mode.cap who = none} then 1 else 0) =
              (quittingJointActionLaw root).expect (fun _ => (0 : ℝ)) := by
              apply FinDist.expect_congr
              intro action _
              simp [QuittingJointResetMode.comp, hmode,
                quittingElementaryJointReset]
          rw [hzero]
          simp [retained, hmode]
    _ = law.expect
        (fun mode => if mode ∈ {mode | mode.cap who = none} then 1 else 0) *
          retained := FinDist.expect_mul_const law _ _
    _ = law.probOf {mode | mode.cap who = none} * retained := by
      rw [FinDist.expect_indicator_eq_probOf]
    _ = retained * law.probOf {mode | mode.cap who = none} := mul_comm _ _
    _ = (if selector who then 0 else
          quittingRootOpponentContinueMass root who) *
        law.probOf {mode | mode.cap who = none} := rfl

/-- The reset-mode law after a finite chronology of roots and global
selectors, starting from the identity mode. -/
def quittingJointResetChronology
    (roots : ℕ → ι → PMF Bool) (selectors : ℕ → ι → Bool) :
    ℕ → FinDist (QuittingJointResetMode ι)
  | 0 => FinDist.pure quittingJointResetIdentity
  | time + 1 => quittingJointResetTransition (roots time) (selectors time)
      (quittingJointResetChronology roots selectors time)

@[simp]
theorem quittingJointResetChronology_zero
    (roots : ℕ → ι → PMF Bool) (selectors : ℕ → ι → Bool) :
    quittingJointResetChronology roots selectors 0 =
      FinDist.pure quittingJointResetIdentity := rfl

theorem quittingJointResetChronology_succ
    (roots : ℕ → ι → PMF Bool) (selectors : ℕ → ι → Bool) (time : ℕ) :
    quittingJointResetChronology roots selectors (time + 1) =
      quittingJointResetTransition (roots time) (selectors time)
        (quittingJointResetChronology roots selectors time) := rfl

/-- The payoff block retains its anchor through a chronology with exactly the
product of the all-Continue root masses. -/
theorem quittingJointResetChronology_payoffIdentityMass
    (roots : ℕ → ι → PMF Bool) (selectors : ℕ → ι → Bool)
    (horizon : ℕ) :
      (quittingJointResetChronology roots selectors horizon).probOf
          {mode | mode.payoff = none} =
        ∏ time ∈ Finset.range horizon,
          quittingStationaryContinueMass (roots time) := by
  classical
  induction horizon with
  | zero =>
      rw [quittingJointResetChronology_zero]
      rw [FinDist.probOf_pure_self]
      · simp
      · simp [quittingJointResetIdentity]
  | succ horizon ih =>
      rw [quittingJointResetChronology_succ,
        quittingJointResetTransition_payoffIdentityMass,
        ih,
        Finset.prod_range_succ]
      ring

/-- Envelope coordinate `who` retains its anchor exactly through the product
of its forced-Continue opponent-survival factors; any forced-Quit selector
kills the product. -/
theorem quittingJointResetChronology_capIdentityMass
    (roots : ℕ → ι → PMF Bool) (selectors : ℕ → ι → Bool) (who : ι)
    (horizon : ℕ) :
      (quittingJointResetChronology roots selectors horizon).probOf
          {mode | mode.cap who = none} =
        ∏ time ∈ Finset.range horizon,
          if selectors time who then 0
          else quittingRootOpponentContinueMass (roots time) who := by
  classical
  induction horizon with
  | zero =>
      rw [quittingJointResetChronology_zero]
      rw [FinDist.probOf_pure_self]
      · simp
      · simp [quittingJointResetIdentity]
  | succ horizon ih =>
      rw [quittingJointResetChronology_succ,
        quittingJointResetTransition_capIdentityMass,
        ih,
        Finset.prod_range_succ]
      ring

omit [DecidableEq ι] in
private theorem expect_payoff_apply_comp
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι)
    (law : FinDist (QuittingJointResetMode ι))
    (outer : QuittingJointResetMode ι) (who : ι) :
    law.expect (fun inner => (outer.comp inner).apply reward anchor |>.1 who) =
      (outer.apply reward
        (quittingJointResetProjection reward anchor law)).1 who := by
  cases h : outer.payoff <;>
    simp [QuittingJointResetMode.apply, QuittingJointResetMode.comp,
      quittingJointResetProjection, quittingTerminalLabelValue, h]

omit [DecidableEq ι] in
private theorem expect_cap_apply_comp
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι)
    (law : FinDist (QuittingJointResetMode ι))
    (outer : QuittingJointResetMode ι) (who : ι) :
    law.expect (fun inner => (outer.comp inner).apply reward anchor |>.2 who) =
      (outer.apply reward
        (quittingJointResetProjection reward anchor law)).2 who := by
  cases h : outer.cap who <;>
    simp [QuittingJointResetMode.apply, QuittingJointResetMode.comp,
      quittingJointResetProjection, quittingTerminalLabelValue, h]

/-- Projection commutes exactly with one joint-reset transition.  This is the
law-level semiconjugacy; no selector optimality is needed. -/
theorem quittingJointResetProjection_transition
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (selector : ι → Bool)
    (law : FinDist (QuittingJointResetMode ι)) :
    quittingJointResetProjection reward anchor
        (quittingJointResetTransition root selector law) =
      quittingJointResetStep reward root selector
        (quittingJointResetProjection reward anchor law) := by
  apply Prod.ext
  · funext who
    change (quittingJointResetTransition root selector law).expect
        (fun mode => (mode.apply reward anchor).1 who) = _
    rw [quittingJointResetTransition, FinDist.expect_map]
    unfold quittingJointResetTaggedLaw
    rw [FinDist.expect_bind]
    simp_rw [FinDist.expect_map]
    rw [FinDist.expect_comm]
    apply FinDist.expect_congr
    intro action _
    exact expect_payoff_apply_comp reward anchor law
      (quittingElementaryJointReset selector action) who
  · funext who
    change (quittingJointResetTransition root selector law).expect
        (fun mode => (mode.apply reward anchor).2 who) = _
    rw [quittingJointResetTransition, FinDist.expect_map]
    unfold quittingJointResetTaggedLaw
    rw [FinDist.expect_bind]
    simp_rw [FinDist.expect_map]
    rw [FinDist.expect_comm]
    apply FinDist.expect_congr
    intro action _
    exact expect_cap_apply_comp reward anchor law
      (quittingElementaryJointReset selector action) who

/-- A maximizing selector turns the law transition into the exact terminal
semantic prefix after projection. -/
theorem quittingJointResetProjection_transition_eq_semanticPrefix
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (selector : ι → Bool)
    (law : FinDist (QuittingJointResetMode ι))
    (hselector : IsQuittingJointResetSelector reward root
      (quittingJointResetProjection reward anchor law) selector) :
    quittingJointResetProjection reward anchor
        (quittingJointResetTransition root selector law) =
      quittingTerminalSemanticPrefix reward root
        (quittingJointResetProjection reward anchor law) := by
  rw [quittingJointResetProjection_transition]
  exact quittingJointResetStep_eq_semanticPrefix reward root selector _ hselector

/-- Choosing the canonical maximizing selector at the projected state makes
one law transition exactly the semantic prefix. -/
theorem quittingJointResetProjection_transition_max_eq_semanticPrefix
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (law : FinDist (QuittingJointResetMode ι)) :
    let pair := quittingJointResetProjection reward anchor law
    quittingJointResetProjection reward anchor
        (quittingJointResetTransition root
          (quittingMaxJointResetSelector reward root pair) law) =
      quittingTerminalSemanticPrefix reward root pair := by
  dsimp only
  rw [quittingJointResetProjection_transition,
    quittingJointResetStep_max_eq_semanticPrefix]

/-- Projection of a finite chronology obeys the joint-reset step recursion. -/
theorem quittingJointResetProjection_chronology_succ
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι)
    (roots : ℕ → ι → PMF Bool) (selectors : ℕ → ι → Bool) (time : ℕ) :
    quittingJointResetProjection reward anchor
        (quittingJointResetChronology roots selectors (time + 1)) =
      quittingJointResetStep reward (roots time) (selectors time)
        (quittingJointResetProjection reward anchor
          (quittingJointResetChronology roots selectors time)) := by
  rw [quittingJointResetChronology_succ,
    quittingJointResetProjection_transition]

/-- If the displayed selector maximizes at the projected state, the next
finite chronology point is the exact terminal semantic prefix. -/
theorem quittingJointResetProjection_chronology_succ_eq_semanticPrefix
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι)
    (roots : ℕ → ι → PMF Bool) (selectors : ℕ → ι → Bool) (time : ℕ)
    (hselector : IsQuittingJointResetSelector reward (roots time)
      (quittingJointResetProjection reward anchor
        (quittingJointResetChronology roots selectors time))
      (selectors time)) :
    quittingJointResetProjection reward anchor
        (quittingJointResetChronology roots selectors (time + 1)) =
      quittingTerminalSemanticPrefix reward (roots time)
        (quittingJointResetProjection reward anchor
          (quittingJointResetChronology roots selectors time)) := by
  rw [quittingJointResetProjection_chronology_succ]
  exact quittingJointResetStep_eq_semanticPrefix reward _ _ _ hselector

/-! ## Linear observables -/

omit [DecidableEq ι] in
private theorem expect_labelValue_sub
    {Mode : Type} (law : FinDist Mode)
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (first second : Payoff ι)
    (label : Mode → Option (QuittingTerminalLabel ι)) (who : ι) :
    law.expect (fun mode =>
        quittingTerminalLabelValue reward first (label mode) who) -
      law.expect (fun mode =>
        quittingTerminalLabelValue reward second (label mode) who) =
      law.probOf {mode | label mode = none} * (first who - second who) := by
  classical
  rw [← FinDist.expect_sub]
  calc
    law.expect (fun mode =>
        quittingTerminalLabelValue reward first (label mode) who -
          quittingTerminalLabelValue reward second (label mode) who) =
      law.expect (fun mode =>
        (if mode ∈ {mode | label mode = none} then 1 else 0) *
          (first who - second who)) := by
      apply FinDist.expect_congr
      intro mode _
      by_cases hnone : label mode = none
      · simp [quittingTerminalLabelValue, hnone]
      · obtain ⟨S, hS⟩ := Option.ne_none_iff_exists'.mp hnone
        simp [quittingTerminalLabelValue, hS]
    _ = law.expect
        (fun mode => if mode ∈ {mode | label mode = none} then 1 else 0) *
          (first who - second who) :=
      FinDist.expect_mul_const law _ _
    _ = law.probOf {mode | label mode = none} *
          (first who - second who) := by
      rw [FinDist.expect_indicator_eq_probOf]

omit [DecidableEq ι] in
/-- Payoff-anchor dependence is exactly the mass of modes that retain the
whole payoff block. -/
theorem quittingJointResetProjection_payoff_sub
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (first second : QuittingTerminalSemanticPair ι)
    (law : FinDist (QuittingJointResetMode ι)) (who : ι) :
    (quittingJointResetProjection reward first law).1 who -
        (quittingJointResetProjection reward second law).1 who =
      law.probOf {mode | mode.payoff = none} *
        (first.1 who - second.1 who) := by
  exact expect_labelValue_sub law reward first.1 second.1
    (fun mode => mode.payoff) who

omit [DecidableEq ι] in
/-- One envelope coordinate depends on its anchor exactly through the mass of
modes that retain that coordinate. -/
theorem quittingJointResetProjection_cap_sub
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (first second : QuittingTerminalSemanticPair ι)
    (law : FinDist (QuittingJointResetMode ι)) (who : ι) :
    (quittingJointResetProjection reward first law).2 who -
        (quittingJointResetProjection reward second law).2 who =
      law.probOf {mode | mode.cap who = none} *
        (first.2 who - second.2 who) := by
  exact expect_labelValue_sub law reward first.2 second.2
    (fun mode => mode.cap who) who

/-- The payoff-anchor sensitivity after a finite chronology is the product of
the displayed all-Continue root masses. -/
theorem quittingJointResetChronology_projection_payoff_sub
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (first second : QuittingTerminalSemanticPair ι)
    (roots : ℕ → ι → PMF Bool) (selectors : ℕ → ι → Bool)
    (horizon : ℕ) (who : ι) :
    (quittingJointResetProjection reward first
          (quittingJointResetChronology roots selectors horizon)).1 who -
        (quittingJointResetProjection reward second
          (quittingJointResetChronology roots selectors horizon)).1 who =
      (∏ time ∈ Finset.range horizon,
          quittingStationaryContinueMass (roots time)) *
        (first.1 who - second.1 who) := by
  rw [quittingJointResetProjection_payoff_sub,
    quittingJointResetChronology_payoffIdentityMass]

/-- The envelope-anchor sensitivity after a finite chronology is the product
of the selected forced-Continue factors; one forced-Quit selection makes it
zero. -/
theorem quittingJointResetChronology_projection_cap_sub
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (first second : QuittingTerminalSemanticPair ι)
    (roots : ℕ → ι → PMF Bool) (selectors : ℕ → ι → Bool)
    (horizon : ℕ) (who : ι) :
    (quittingJointResetProjection reward first
          (quittingJointResetChronology roots selectors horizon)).2 who -
        (quittingJointResetProjection reward second
          (quittingJointResetChronology roots selectors horizon)).2 who =
      (∏ time ∈ Finset.range horizon,
          if selectors time who then 0
          else quittingRootOpponentContinueMass (roots time) who) *
        (first.2 who - second.2 who) := by
  rw [quittingJointResetProjection_cap_sub,
    quittingJointResetChronology_capIdentityMass]

omit [DecidableEq ι] in
/-- Total semantic debt is the expectation of the modewise total debt. -/
theorem sum_quittingTerminalSemanticDebt_projection
    (reward : QuittingTerminalLabel ι → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι)
    (law : FinDist (QuittingJointResetMode ι)) :
    (∑ who, quittingTerminalSemanticDebt
        (quittingJointResetProjection reward anchor law) who) =
      law.expect fun mode =>
        ∑ who, quittingTerminalSemanticDebt (mode.apply reward anchor) who := by
  simp only [quittingTerminalSemanticDebt, quittingJointResetProjection]
  simp_rw [← FinDist.expect_sub]
  exact FinDist.expect_sum_comm law fun who mode =>
    (mode.apply reward anchor).2 who - (mode.apply reward anchor).1 who

end GameTheory
