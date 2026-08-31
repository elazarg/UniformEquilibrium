/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CapDebtBellmanReduction
import UniformEquilibrium.Quitting.Root.NashExistence

/-!
# Four-profile descendant slices

This module packages four simultaneous terminal semantic/law coordinates into a
compact prefix orbit. Two positive debt-relative passports and one zero-debt
observer define a closed normalized slice. Response debt attains a minimum on
that slice, and exact cap--Nash prefix closure makes every exact root at a
positive-debt minimizer literally all Continue.

The construction is conditional on a supplied convergent four-profile family.
It does not attach that family to a quitting-game source, select a minimum
carrier point, or provide chronology, renewal, or a uniform-equilibrium result.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

section Generic

abbrev QuittingFourProfileResponseDecoration (ι : Type) [Fintype ι] :=
  (QuittingTerminalSemanticLawPoint ι ×
    QuittingTerminalSemanticLawPoint ι) ×
  (QuittingTerminalSemanticLawPoint ι ×
    QuittingTerminalSemanticLawPoint ι)

namespace QuittingFourProfileResponseDecoration

def response (point : QuittingFourProfileResponseDecoration ι) := point.1.1
def sibling (point : QuittingFourProfileResponseDecoration ι) := point.1.2
def replacement (point : QuittingFourProfileResponseDecoration ι) := point.2.1
def source (point : QuittingFourProfileResponseDecoration ι) := point.2.2

def responseDebt (point : QuittingFourProfileResponseDecoration ι) : ℝ :=
  quittingTerminalSemanticDebtSum point.response.1

def observerDebt (point : QuittingFourProfileResponseDecoration ι)
    (observer : ι) : ℝ :=
  quittingTerminalSemanticDebt point.response.1 observer

def signedAtom (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingFourProfileResponseDecoration ι)
    (terminal : {S : Finset ι // S.Nonempty}) (observer : ι) : ℝ :=
  (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
    ((point.response.2 (some terminal) - point.sibling.2 (some terminal)) *
      reward terminal observer)

def actualGain (point : QuittingFourProfileResponseDecoration ι)
    (mover : ι) : ℝ :=
  point.replacement.1.1 mover - point.source.1.1 mover

omit [DecidableEq ι] in
theorem continuous_responseDebt :
    Continuous (responseDebt : QuittingFourProfileResponseDecoration ι → ℝ) := by
  unfold responseDebt response
  exact continuous_quittingTerminalSemanticDebtSum.comp
    (continuous_fst.comp (continuous_fst.comp continuous_fst))

omit [DecidableEq ι] in
theorem continuous_observerDebt (observer : ι) :
    Continuous (fun point : QuittingFourProfileResponseDecoration ι =>
      point.observerDebt observer) := by
  unfold observerDebt response
  exact (continuous_quittingTerminalSemanticDebt observer).comp
    (continuous_fst.comp (continuous_fst.comp continuous_fst))

omit [DecidableEq ι] in
theorem continuous_signedAtom
    (terminal : {S : Finset ι // S.Nonempty}) (observer : ι) :
    Continuous (fun point : QuittingFourProfileResponseDecoration ι =>
      point.signedAtom reward terminal observer) := by
  unfold signedAtom response sibling
  fun_prop

omit [DecidableEq ι] in
theorem continuous_actualGain (mover : ι) :
    Continuous (fun point : QuittingFourProfileResponseDecoration ι =>
      point.actualGain mover) := by
  unfold actualGain replacement source
  fun_prop

end QuittingFourProfileResponseDecoration

structure QuittingFourProfileResponseFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  responseProfile : ℕ → (quittingGame reward).BehaviorProfile
  siblingProfile : ℕ → (quittingGame reward).BehaviorProfile
  replacementProfile : ℕ → (quittingGame reward).BehaviorProfile
  sourceProfile : ℕ → (quittingGame reward).BehaviorProfile
  terminal : {S : Finset ι // S.Nonempty}
  observer : ι
  mover : ι

namespace QuittingFourProfileResponseFamily

variable (family : QuittingFourProfileResponseFamily reward)

/-- Reindex all four literal profiles along one shared rank map. -/
def reindex (subseq : ℕ → ℕ) : QuittingFourProfileResponseFamily reward where
  responseProfile n := family.responseProfile (subseq n)
  siblingProfile n := family.siblingProfile (subseq n)
  replacementProfile n := family.replacementProfile (subseq n)
  sourceProfile n := family.sourceProfile (subseq n)
  terminal := family.terminal
  observer := family.observer
  mover := family.mover

def lawPoint (profile : (quittingGame reward).BehaviorProfile) :
    QuittingTerminalSemanticLawPoint ι :=
  (quittingTerminalSemanticPair reward profile,
    quittingTerminalOutcomeMass reward profile)

def baseDecoration (rank : ℕ) : QuittingFourProfileResponseDecoration ι :=
  ((lawPoint (reward := reward) (family.responseProfile rank),
      lawPoint (reward := reward) (family.siblingProfile rank)),
    (lawPoint (reward := reward) (family.replacementProfile rank),
      lawPoint (reward := reward) (family.sourceProfile rank)))

@[simp] theorem baseDecoration_reindex (subseq : ℕ → ℕ) (rank : ℕ) :
    baseDecoration (family := family.reindex subseq) rank =
      baseDecoration (family := family) (subseq rank) := rfl

def prefixLawPoint (root : ι → PMF Bool)
    (point : QuittingTerminalSemanticLawPoint ι) :
    QuittingTerminalSemanticLawPoint ι :=
  (quittingTerminalSemanticPrefix reward root point.1,
    quittingTerminalOutcomeLawPrefix root point.2)

def prefixMap (root : ι → PMF Bool)
    (point : QuittingFourProfileResponseDecoration ι) :
    QuittingFourProfileResponseDecoration ι :=
  ((prefixLawPoint (reward := reward) root point.response,
      prefixLawPoint (reward := reward) root point.sibling),
    (prefixLawPoint (reward := reward) root point.replacement,
      prefixLawPoint (reward := reward) root point.source))

def rawDecoration (rank : ℕ) : List (ι → PMF Bool) →
    QuittingFourProfileResponseDecoration ι
  | [] => baseDecoration (family := family) rank
  | root :: roots => prefixMap (reward := reward) root
      (rawDecoration rank roots)

@[simp] theorem rawDecoration_nil (rank : ℕ) :
    rawDecoration (family := family) rank [] =
      baseDecoration (family := family) rank := rfl

@[simp] theorem rawDecoration_cons (root : ι → PMF Bool) (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    rawDecoration (family := family) rank (root :: roots) =
      prefixMap (reward := reward) root
        (rawDecoration (family := family) rank roots) := rfl

theorem prefixMap_signedAtom (root : ι → PMF Bool)
    (point : QuittingFourProfileResponseDecoration ι) :
    (prefixMap (reward := reward) root point).signedAtom reward
        family.terminal family.observer =
      quittingStationaryContinueMass root *
        point.signedAtom reward family.terminal family.observer := by
  unfold QuittingFourProfileResponseDecoration.signedAtom prefixMap prefixLawPoint
    QuittingFourProfileResponseDecoration.response
    QuittingFourProfileResponseDecoration.sibling
    quittingTerminalOutcomeLawPrefix
  ring

theorem prefixMap_actualGain (root : ι → PMF Bool)
    (point : QuittingFourProfileResponseDecoration ι) :
    (prefixMap (reward := reward) root point).actualGain family.mover =
      quittingStationaryContinueMass root *
        point.actualGain family.mover := by
  unfold QuittingFourProfileResponseDecoration.actualGain prefixMap prefixLawPoint
    QuittingFourProfileResponseDecoration.replacement
    QuittingFourProfileResponseDecoration.source
    quittingTerminalSemanticPrefix
  rw [quittingRootSuccessorPayoff_sub_eq_continueMass_mul]

theorem continuous_prefixLawPoint (root : ι → PMF Bool) :
    Continuous (prefixLawPoint (reward := reward) root) := by
  exact ((continuous_quittingTerminalSemanticPrefix reward root).comp
    continuous_fst).prodMk
      ((continuous_quittingTerminalOutcomeLawPrefix root).comp continuous_snd)

theorem continuous_prefixMap (root : ι → PMF Bool) :
    Continuous (prefixMap (reward := reward) root) := by
  exact (((continuous_prefixLawPoint (reward := reward) root).comp
      (continuous_fst.comp continuous_fst)).prodMk
    ((continuous_prefixLawPoint (reward := reward) root).comp
      (continuous_snd.comp continuous_fst))).prodMk
    (((continuous_prefixLawPoint (reward := reward) root).comp
      (continuous_fst.comp continuous_snd)).prodMk
    ((continuous_prefixLawPoint (reward := reward) root).comp
      (continuous_snd.comp continuous_snd)))

def rawPrefixOrbit : Set (QuittingFourProfileResponseDecoration ι) :=
  {point | ∃ rank roots, rawDecoration (family := family) rank roots = point}

def prefixOrbitCarrier : Set (QuittingFourProfileResponseDecoration ι) :=
  closure (rawPrefixOrbit (family := family))

theorem prefixMap_mem_carrier (root : ι → PMF Bool)
    {point : QuittingFourProfileResponseDecoration ι}
    (hpoint : point ∈ prefixOrbitCarrier (family := family)) :
    prefixMap (reward := reward) root point ∈
      prefixOrbitCarrier (family := family) := by
  unfold prefixOrbitCarrier at hpoint ⊢
  apply map_mem_closure (continuous_prefixMap (reward := reward) root) hpoint
  rintro candidate ⟨rank, roots, rfl⟩
  exact ⟨rank, root :: roots, rfl⟩

/-- Fourfold compact joint semantic/law ambient carrier. -/
def prefixOrbitAmbient : Set (QuittingFourProfileResponseDecoration ι) :=
  (quittingTerminalSemanticLawCarrier reward ×ˢ
      quittingTerminalSemanticLawCarrier reward) ×ˢ
    (quittingTerminalSemanticLawCarrier reward ×ˢ
      quittingTerminalSemanticLawCarrier reward)

theorem prefixOrbitAmbient_isCompact :
    IsCompact (prefixOrbitAmbient (reward := reward)) := by
  exact ((quittingTerminalSemanticLawCarrier_isCompact reward).prod
    (quittingTerminalSemanticLawCarrier_isCompact reward)).prod
      ((quittingTerminalSemanticLawCarrier_isCompact reward).prod
        (quittingTerminalSemanticLawCarrier_isCompact reward))

theorem prefixMap_mem_ambient (root : ι → PMF Bool)
    {point : QuittingFourProfileResponseDecoration ι}
    (hpoint : point ∈ prefixOrbitAmbient (reward := reward)) :
    prefixMap (reward := reward) root point ∈
      prefixOrbitAmbient (reward := reward) := by
  exact ⟨⟨quittingTerminalSemanticLawPrefix_mem_carrier reward root
      point.response hpoint.1.1,
    quittingTerminalSemanticLawPrefix_mem_carrier reward root
      point.sibling hpoint.1.2⟩,
    ⟨quittingTerminalSemanticLawPrefix_mem_carrier reward root
      point.replacement hpoint.2.1,
    quittingTerminalSemanticLawPrefix_mem_carrier reward root
      point.source hpoint.2.2⟩⟩

theorem rawDecoration_mem_ambient (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    rawDecoration (family := family) rank roots ∈
      prefixOrbitAmbient (reward := reward) := by
  induction roots with
  | nil =>
      exact ⟨⟨quittingTerminalSemanticLawPoint_mem_carrier reward
          (family.responseProfile rank),
        quittingTerminalSemanticLawPoint_mem_carrier reward
          (family.siblingProfile rank)⟩,
        ⟨quittingTerminalSemanticLawPoint_mem_carrier reward
          (family.replacementProfile rank),
        quittingTerminalSemanticLawPoint_mem_carrier reward
          (family.sourceProfile rank)⟩⟩
  | cons root roots ih =>
      rw [rawDecoration_cons]
      exact prefixMap_mem_ambient (reward := reward) root ih

theorem prefixOrbitCarrier_isCompact :
    IsCompact (prefixOrbitCarrier (family := family)) := by
  apply (prefixOrbitAmbient_isCompact (reward := reward)).of_isClosed_subset
    isClosed_closure
  apply closure_minimal
  · rintro point ⟨rank, roots, rfl⟩
    exact rawDecoration_mem_ambient family rank roots
  · exact (prefixOrbitAmbient_isCompact (reward := reward)).isClosed

theorem prefixOrbitCarrier_subset_ambient :
    prefixOrbitCarrier (family := family) ⊆
      prefixOrbitAmbient (reward := reward) := by
  apply closure_minimal
  · rintro point ⟨rank, roots, rfl⟩
    exact rawDecoration_mem_ambient family rank roots
  · exact (prefixOrbitAmbient_isCompact (reward := reward)).isClosed

/-- The response semantic coordinate of every closed descendant is a genuine
terminal semantic carrier point. -/
theorem response_semantic_mem_carrier
    {point : QuittingFourProfileResponseDecoration ι}
    (hpoint : point ∈ prefixOrbitCarrier (family := family)) :
    point.response.1 ∈ quittingTerminalSemanticCarrier reward := by
  have hambient := prefixOrbitCarrier_subset_ambient family hpoint
  exact terminalSemanticLawCarrier_fst_mem_carrier point.response hambient.1.1

/-- Closed four-profile descendant slice carrying zero observer debt and two
debt-relative positive passports. -/
def normalizedDescendantSlice (atomDensity gainDensity : ℝ) :
    Set (QuittingFourProfileResponseDecoration ι) :=
  prefixOrbitCarrier (family := family) ∩
    {point | point.observerDebt family.observer = 0 ∧
      atomDensity * point.responseDebt ≤
        point.signedAtom reward family.terminal family.observer ∧
      gainDensity * point.responseDebt ≤ point.actualGain family.mover}

theorem normalizedDescendantSlice_isClosed
    (atomDensity gainDensity : ℝ) :
    IsClosed (normalizedDescendantSlice family atomDensity gainDensity) := by
  have hobserver : IsClosed
      {point : QuittingFourProfileResponseDecoration ι |
        point.observerDebt family.observer = 0} :=
    isClosed_eq
      (QuittingFourProfileResponseDecoration.continuous_observerDebt
        family.observer) continuous_const
  have hatom : IsClosed
      {point : QuittingFourProfileResponseDecoration ι |
        atomDensity * point.responseDebt ≤
          point.signedAtom reward family.terminal family.observer} :=
    isClosed_le (continuous_const.mul
      QuittingFourProfileResponseDecoration.continuous_responseDebt)
        (QuittingFourProfileResponseDecoration.continuous_signedAtom
          (reward := reward) family.terminal family.observer)
  have hgain : IsClosed
      {point : QuittingFourProfileResponseDecoration ι |
        gainDensity * point.responseDebt ≤ point.actualGain family.mover} :=
    isClosed_le (continuous_const.mul
      QuittingFourProfileResponseDecoration.continuous_responseDebt)
        (QuittingFourProfileResponseDecoration.continuous_actualGain family.mover)
  exact isClosed_closure.inter (hobserver.inter (hatom.inter hgain))

theorem normalizedDescendantSlice_isCompact
    (atomDensity gainDensity : ℝ) :
    IsCompact (normalizedDescendantSlice family atomDensity gainDensity) := by
  apply (prefixOrbitCarrier_isCompact family).of_isClosed_subset
    (normalizedDescendantSlice_isClosed family atomDensity gainDensity)
  intro point hpoint
  exact hpoint.1

/-- Exact cap-debt account on the response coordinate of the fourfold
prefix action. -/
theorem prefixMap_responseDebt_eq_continueMass_mul_add_capDefect
    (root : ι → PMF Bool)
    (point : QuittingFourProfileResponseDecoration ι) :
    (prefixMap (reward := reward) root point).responseDebt =
      quittingStationaryContinueMass root * point.responseDebt +
        quittingRootTotalNashDefect reward point.response.1.2 root := by
  exact quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect
    reward point.response.1 root

/-- Exact cap--Nash prefixing scales the selected observer's response debt. -/
theorem prefixMap_observerDebt_eq_continueMass_mul_of_isZeroNash
    (root : ι → PMF Bool)
    (point : QuittingFourProfileResponseDecoration ι)
    (hnash : IsεQuittingRootNash reward point.response.1.2 0 root) :
    (prefixMap (reward := reward) root point).observerDebt family.observer =
      quittingStationaryContinueMass root *
        point.observerDebt family.observer := by
  exact quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
    point.response.1 root family.observer hnash

/-- Exact cap--Nash prefixing preserves the homogeneous four-profile slice. -/
theorem prefixMap_mem_normalizedDescendantSlice_of_isZeroNash
    (atomDensity gainDensity : ℝ)
    (point : QuittingFourProfileResponseDecoration ι)
    (hpoint : point ∈
      normalizedDescendantSlice family atomDensity gainDensity)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward point.response.1.2 0 root) :
    prefixMap (reward := reward) root point ∈
      normalizedDescendantSlice family atomDensity gainDensity := by
  rcases hpoint with ⟨hcarrier, hobserver, hatom, hgain⟩
  have hdefect : quittingRootTotalNashDefect reward point.response.1.2 root = 0 :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward point.response.1.2 root).1 hnash
  have hdebt : (prefixMap (reward := reward) root point).responseDebt =
      quittingStationaryContinueMass root * point.responseDebt := by
    rw [prefixMap_responseDebt_eq_continueMass_mul_add_capDefect
      (reward := reward),
      hdefect, add_zero]
  have hcontinue := quittingStationaryContinueMass_nonneg root
  refine ⟨prefixMap_mem_carrier family root hcarrier, ?_, ?_, ?_⟩
  · rw [prefixMap_observerDebt_eq_continueMass_mul_of_isZeroNash
      family root point hnash, hobserver, mul_zero]
  · rw [hdebt, prefixMap_signedAtom family]
    calc
      atomDensity *
          (quittingStationaryContinueMass root * point.responseDebt) =
          quittingStationaryContinueMass root *
            (atomDensity * point.responseDebt) := by ring
      _ ≤ quittingStationaryContinueMass root *
          point.signedAtom reward family.terminal family.observer :=
        mul_le_mul_of_nonneg_left hatom hcontinue
  · rw [hdebt, prefixMap_actualGain family]
    calc
      gainDensity *
          (quittingStationaryContinueMass root * point.responseDebt) =
          quittingStationaryContinueMass root *
            (gainDensity * point.responseDebt) := by ring
      _ ≤ quittingStationaryContinueMass root * point.actualGain family.mover :=
        mul_le_mul_of_nonneg_left hgain hcontinue

/-- A simultaneous four-profile limit carrying both positive passports. -/
structure ConvergentFourProfilePassport where
  limit : QuittingFourProfileResponseDecoration ι
  tendsto_base : Tendsto (baseDecoration (family := family)) atTop (nhds limit)
  observerDebt_eq_zero : limit.observerDebt family.observer = 0
  responseDebt_pos : 0 < limit.responseDebt
  signedAtom_pos : 0 < limit.signedAtom reward family.terminal family.observer
  actualGain_pos : 0 < limit.actualGain family.mover

namespace ConvergentFourProfilePassport

theorem limit_mem_prefixOrbitCarrier
    (passport : ConvergentFourProfilePassport family) :
    passport.limit ∈ prefixOrbitCarrier (family := family) := by
  rw [prefixOrbitCarrier, mem_closure_iff_seq_limit]
  refine ⟨baseDecoration (family := family), ?_, passport.tendsto_base⟩
  intro rank
  exact ⟨rank, [], (rawDecoration_nil family rank).symm⟩

theorem limit_mem_normalizedDescendantSlice
    (passport : ConvergentFourProfilePassport family)
    (atomDensity gainDensity : ℝ)
    (hatom : atomDensity * passport.limit.responseDebt <
      passport.limit.signedAtom reward family.terminal family.observer)
    (hgain : gainDensity * passport.limit.responseDebt <
      passport.limit.actualGain family.mover) :
    passport.limit ∈
      normalizedDescendantSlice family atomDensity gainDensity := by
  exact ⟨passport.limit_mem_prefixOrbitCarrier, passport.observerDebt_eq_zero,
    hatom.le, hgain.le⟩

end ConvergentFourProfilePassport

/-- Response debt attains a minimum on every nonempty four-profile slice. -/
theorem exists_minimum_normalizedDescendantSlice
    (atomDensity gainDensity : ℝ)
    (hnonempty :
      (normalizedDescendantSlice family atomDensity gainDensity).Nonempty) :
    ∃ point ∈ normalizedDescendantSlice family atomDensity gainDensity,
      ∀ candidate ∈ normalizedDescendantSlice family atomDensity gainDensity,
        point.responseDebt ≤ candidate.responseDebt := by
  exact (normalizedDescendantSlice_isCompact family atomDensity gainDensity)
    |>.exists_isMinOn hnonempty
      QuittingFourProfileResponseDecoration.continuous_responseDebt.continuousOn

/-- Every exact root at a positive-debt slice minimizer is all Continue. -/
theorem minimum_normalizedDescendantSlice_exactRoot_eq_allContinue
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (atomDensity gainDensity : ℝ)
    (point : QuittingFourProfileResponseDecoration ι)
    (hpoint : point ∈
      normalizedDescendantSlice family atomDensity gainDensity)
    (hmin : ∀ candidate ∈
      normalizedDescendantSlice family atomDensity gainDensity,
      point.responseDebt ≤ candidate.responseDebt)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward point.response.1.2 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  have hresponseCarrier := response_semantic_mem_carrier family hpoint.1
  have hpointPos : 0 < point.responseDebt :=
    hminimum_pos.trans_le (hminimum point.response.1 hresponseCarrier)
  have hprefixed :=
    prefixMap_mem_normalizedDescendantSlice_of_isZeroNash family
      atomDensity gainDensity point hpoint root hnash
  have hminimal := hmin (prefixMap (reward := reward) root point) hprefixed
  have hdefect : quittingRootTotalNashDefect reward point.response.1.2 root = 0 :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward point.response.1.2 root).1 hnash
  rw [prefixMap_responseDebt_eq_continueMass_mul_add_capDefect
    (reward := reward),
    hdefect, add_zero] at hminimal
  have hcontinueLe := quittingStationaryContinueMass_le_one root
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    nlinarith
  funext player
  simpa only [quittingAllContinueRoot] using
    eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue player

/-- Correspondence form: the exact cap--Nash fibre at the minimizer consists
of the all-Continue root alone. -/
theorem minimum_normalizedDescendantSlice_isZeroNash_iff_allContinue
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (atomDensity gainDensity : ℝ)
    (point : QuittingFourProfileResponseDecoration ι)
    (hpoint : point ∈
      normalizedDescendantSlice family atomDensity gainDensity)
    (hmin : ∀ candidate ∈
      normalizedDescendantSlice family atomDensity gainDensity,
      point.responseDebt ≤ candidate.responseDebt)
    (root : ι → PMF Bool) :
    IsεQuittingRootNash reward point.response.1.2 0 root ↔
      root = (quittingAllContinueRoot : ι → PMF Bool) := by
  constructor
  · exact minimum_normalizedDescendantSlice_exactRoot_eq_allContinue family
      minimum hminimum hminimum_pos atomDensity gainDensity point hpoint hmin root
  · intro hroot
    obtain ⟨selected, hselected⟩ :=
      exists_isZeroQuittingRootNash (reward := reward) point.response.1.2
    have hselectedEq :=
      minimum_normalizedDescendantSlice_exactRoot_eq_allContinue family
        minimum hminimum hminimum_pos atomDensity gainDensity point hpoint hmin
          selected hselected
    rw [hroot, ← hselectedEq]
    exact hselected

/-- A supplied common four-profile cluster yields a slice minimizer, whose
response debt either equals the global minimum or is strictly larger with a
unique all-Continue exact-root correspondence. -/
theorem exists_minimum_normalizedDescendantSlice_eq_or_strict_inert
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (passport : ConvergentFourProfilePassport family)
    (atomDensity gainDensity : ℝ)
    (hatom : atomDensity * passport.limit.responseDebt <
      passport.limit.signedAtom reward family.terminal family.observer)
    (hgain : gainDensity * passport.limit.responseDebt <
      passport.limit.actualGain family.mover) :
    ∃ point ∈ normalizedDescendantSlice family atomDensity gainDensity,
      (∀ candidate ∈
        normalizedDescendantSlice family atomDensity gainDensity,
        point.responseDebt ≤ candidate.responseDebt) ∧
      quittingTerminalSemanticDebtSum minimum ≤ point.responseDebt ∧
      (point.responseDebt = quittingTerminalSemanticDebtSum minimum ∨
        quittingTerminalSemanticDebtSum minimum < point.responseDebt ∧
          ∀ root : ι → PMF Bool,
            IsεQuittingRootNash reward point.response.1.2 0 root ↔
              root = (quittingAllContinueRoot : ι → PMF Bool)) := by
  have hlimit :=
    ConvergentFourProfilePassport.limit_mem_normalizedDescendantSlice
      family passport atomDensity gainDensity hatom hgain
  obtain ⟨point, hpoint, hmin⟩ :=
    exists_minimum_normalizedDescendantSlice family atomDensity gainDensity
      ⟨passport.limit, hlimit⟩
  have hresponseCarrier := response_semantic_mem_carrier family hpoint.1
  have hlower : quittingTerminalSemanticDebtSum minimum ≤ point.responseDebt :=
    hminimum point.response.1 hresponseCarrier
  refine ⟨point, hpoint, hmin, hlower, ?_⟩
  rcases hlower.eq_or_lt with heq | hlt
  · exact Or.inl heq.symm
  · exact Or.inr ⟨hlt, fun root =>
      minimum_normalizedDescendantSlice_isZeroNash_iff_allContinue family
        minimum hminimum hminimum_pos atomDensity gainDensity point hpoint hmin
          root⟩

end QuittingFourProfileResponseFamily

end Generic

end GameTheory
