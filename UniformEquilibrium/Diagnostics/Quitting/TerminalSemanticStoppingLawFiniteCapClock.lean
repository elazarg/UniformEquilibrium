/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFiniteSplice

/-!
# Finite-cap clock classification for stopping laws

This module classifies exactly when the universal finite-splice error vanishes.
It identifies the two-zero-Never threshold for maximal pair-deleted survival and
records the finite-sentinel form used by later cap constructions.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-! ## Two sharp sufficient conditions -/

/-- Without a `Never` atom, the finite-splice error always vanishes. -/
theorem tendsto_quittingFiniteSpliceError_zero_of_neverMass_zero
    (roots : ℕ → ι → PMF Bool) (mover : ι) (hazard : ℕ → PMF Bool)
    (hnever : quittingHazardNeverMass hazard = 0) :
    Tendsto (fun cutoff =>
      quittingFiniteSpliceError roots mover hazard cutoff)
      atTop (nhds 0) := by
  simpa [quittingFiniteSpliceError, hnever] using
    tendsto_quittingHazardLateFiniteMass_zero hazard

/-- A possibly positive `Never` atom is harmless when the maximal
pair-deleted survival clock vanishes. -/
theorem tendsto_quittingFiniteSpliceError_zero_of_pairDeleted
    (roots : ℕ → ι → PMF Bool) (mover : ι) (hazard : ℕ → PMF Bool)
    (hclock : Tendsto (fun cutoff =>
      quittingMaxPairDeletedSurvivalWeight roots mover 0 cutoff)
      atTop (nhds 0)) :
    Tendsto (fun cutoff =>
      quittingFiniteSpliceError roots mover hazard cutoff)
      atTop (nhds 0) := by
  have hlate := tendsto_quittingHazardLateFiniteMass_zero hazard
  have hconst : Tendsto
      (fun _ : ℕ => quittingHazardNeverMass hazard) atTop
      (nhds (quittingHazardNeverMass hazard)) := tendsto_const_nhds
  have hcemetery : Tendsto (fun cutoff =>
      quittingHazardNeverMass hazard *
        quittingMaxPairDeletedSurvivalWeight roots mover 0 cutoff)
      atTop (nhds 0) := by
    simpa using hconst.mul hclock
  simpa [quittingFiniteSpliceError] using hlate.add hcemetery

/-! ## Finite sentinels kill pair-deleted clocks -/

omit [Nontrivial ι] in
/-- A sure quitter distinct from both deleted coordinates kills the
corresponding pair-deleted survival clock at every horizon containing that
row. -/
theorem quittingPairDeletedSurvivalWeight_eq_zero_of_sure_other
    (roots : ℕ → ι → PMF Bool) (mover observer sentinel : ι)
    (hsentinelMover : sentinel ≠ mover)
    (hsentinelObserver : sentinel ≠ observer)
    (sureTime fuel : ℕ) (hsureTime : sureTime < fuel)
    (hsure : roots sureTime sentinel = PMF.pure true) :
    quittingPairDeletedSurvivalWeight roots mover observer 0 fuel = 0 := by
  unfold quittingPairDeletedSurvivalWeight quittingOpponentSurvivalWeight
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hsureTime)
  simp only [Nat.zero_add]
  unfold quittingFixedOpponentsContinueMass
  let forcedRoot := Function.update
    (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard
      sureTime) mover (PMF.pure false)
  have hsureRoot : QuittingRootHasSureQuitter forcedRoot := by
    refine ⟨sentinel, ?_⟩
    dsimp [forcedRoot]
    unfold quittingRootSequenceUpdate quittingAlwaysContinueHazard
    rw [Function.update_of_ne hsentinelMover,
      Function.update_of_ne hsentinelObserver, hsure]
  have hmass :=
    (quittingRootHasSureQuitter_iff_allContinue_mass_zero forcedRoot).mp
      hsureRoot
  unfold quittingStationaryContinueMass
  change ((pmfPi forcedRoot (fun _ => false)).toReal) = 0
  rw [hmass]
  simp

omit [Nontrivial ι] in
/-- The complementary sharpness fact: if everyone outside the deleted
mover/observer pair continues surely, then the pair-deleted clock is exactly
one at every finite horizon.  Actions of the two deleted players themselves
cannot change this clock. -/
theorem quittingPairDeletedSurvivalWeight_eq_one_of_others_continue
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (start fuel : ℕ)
    (hcontinue : ∀ time player, player ≠ mover → player ≠ observer →
      roots time player = PMF.pure false) :
    quittingPairDeletedSurvivalWeight roots mover observer start fuel = 1 := by
  unfold quittingPairDeletedSurvivalWeight quittingOpponentSurvivalWeight
  apply Finset.prod_eq_one
  intro offset _
  unfold quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_eq_one
  intro player _
  by_cases hplayerMover : player = mover
  · subst player
    simp
  by_cases hplayerObserver : player = observer
  · subst player
    simp [quittingRootSequenceUpdate, quittingAlwaysContinueHazard,
      hplayerMover]
  · simp [quittingRootSequenceUpdate, quittingAlwaysContinueHazard,
      hplayerMover, hplayerObserver,
      hcontinue (start + offset) player hplayerMover hplayerObserver]

/-- One sentinel is genuinely insufficient for the uniform-over-observers
clock estimate.  If every player outside the mover/sentinel pair continues
surely, choosing the sentinel itself as observer deletes the only possible
absorber, and the maximum pair-deleted clock remains exactly one. -/
theorem quittingMaxPairDeletedSurvivalWeight_eq_one_of_single_sentinel
    (roots : ℕ → ι → PMF Bool) (mover sentinel : ι)
    (hmoverSentinel : mover ≠ sentinel) (start fuel : ℕ)
    (hcontinue : ∀ time player, player ≠ mover → player ≠ sentinel →
      roots time player = PMF.pure false) :
    quittingMaxPairDeletedSurvivalWeight roots mover start fuel = 1 := by
  apply le_antisymm
  · exact quittingMaxPairDeletedSurvivalWeight_le_one
      roots mover start fuel
  · rw [← quittingPairDeletedSurvivalWeight_eq_one_of_others_continue
      roots mover sentinel start fuel hcontinue]
    exact quittingPairDeletedSurvivalWeight_le_max
      roots mover sentinel hmoverSentinel start fuel

omit [Nontrivial ι] in
/-- Any player which survives both deletions bounds the pair-deleted clock by
its own survival curve.  This is the quantitative, nonsure version of the
finite-sentinel zero lemma. -/
theorem quittingPairDeletedSurvivalWeight_le_hazardSurvival_of_other
    (roots : ℕ → ι → PMF Bool) (mover observer sentinel : ι)
    (hsentinelMover : sentinel ≠ mover)
    (hsentinelObserver : sentinel ≠ observer) (fuel : ℕ) :
    quittingPairDeletedSurvivalWeight roots mover observer 0 fuel ≤
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots sentinel) fuel := by
  unfold quittingPairDeletedSurvivalWeight
  have h :=
    quittingOpponentSurvivalWeight_le_quittingHazardSurvival_ownHazard
      (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
      hsentinelMover fuel
  have hhazard : quittingRootSequenceOwnHazard
      (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
        sentinel = quittingRootSequenceOwnHazard roots sentinel := by
    funext time
    unfold quittingRootSequenceOwnHazard quittingRootSequenceUpdate
    exact Function.update_of_ne hsentinelObserver _ _
  rwa [hhazard] at h

omit [Nontrivial ι] in
/-- Exact product geometry of the deleted clock: after forcing the mover and
observer to Continue, joint survival is the product of the individual
survival curves of that twice-deleted root sequence. -/
theorem quittingPairDeletedSurvivalWeight_eq_prod_hazardSurvival
    (roots : ℕ → ι → PMF Bool) (mover observer : ι) (fuel : ℕ) :
    quittingPairDeletedSurvivalWeight roots mover observer 0 fuel =
      ∏ player, quittingHazardSurvival
        (quittingRootSequenceOwnHazard
          (quittingRootSequenceUpdate
            (quittingRootSequenceUpdate roots observer
              quittingAlwaysContinueHazard)
            mover quittingAlwaysContinueHazard)
          player) fuel := by
  unfold quittingPairDeletedSurvivalWeight
    quittingOpponentSurvivalWeight quittingFixedOpponentsContinueMass
  simp only [Nat.zero_add,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingHazardSurvival_eq_prod, quittingRootSequenceOwnHazard,
    quittingRootSequenceUpdate, quittingAlwaysContinueHazard]
  rw [Finset.prod_comm]

omit [Nontrivial ι] in
/-- Passing the finite product identity to the limit identifies terminal
pair-deleted survival with the product of the individual cemetery masses in
the twice-deleted root sequence. -/
theorem quittingPairDeletedSurvivalLimit_eq_prod_neverMass
    (roots : ℕ → ι → PMF Bool) (mover observer : ι) :
    quittingPairDeletedSurvivalLimit roots mover observer 0 =
      ∏ player, quittingHazardNeverMass
        (quittingRootSequenceOwnHazard
          (quittingRootSequenceUpdate
            (quittingRootSequenceUpdate roots observer
              quittingAlwaysContinueHazard)
            mover quittingAlwaysContinueHazard)
          player) := by
  let deletedRoots :=
    quittingRootSequenceUpdate
      (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
      mover quittingAlwaysContinueHazard
  have hproduct : Tendsto (fun fuel =>
      ∏ player, quittingHazardSurvival
        (quittingRootSequenceOwnHazard deletedRoots player) fuel)
      atTop (nhds (∏ player, quittingHazardNeverMass
        (quittingRootSequenceOwnHazard deletedRoots player))) := by
    apply tendsto_finsetProd Finset.univ
    intro player _
    exact tendsto_quittingHazardSurvival_neverMass
      (quittingRootSequenceOwnHazard deletedRoots player)
  have hweight : Tendsto (fun fuel =>
      quittingPairDeletedSurvivalWeight roots mover observer 0 fuel)
      atTop (nhds (∏ player, quittingHazardNeverMass
        (quittingRootSequenceOwnHazard deletedRoots player))) := by
    simpa [deletedRoots,
      quittingPairDeletedSurvivalWeight_eq_prod_hazardSurvival] using hproduct
  exact tendsto_nhds_unique
    (tendsto_quittingPairDeletedSurvivalLimit roots mover observer 0)
    hweight

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
@[simp] theorem quittingHazardNeverMass_alwaysContinue :
    quittingHazardNeverMass quittingAlwaysContinueHazard = 1 := by
  have hconstant : ∀ fuel,
      quittingHazardSurvival quittingAlwaysContinueHazard fuel = 1 := by
    intro fuel
    simp [quittingHazardSurvival_eq_prod, quittingAlwaysContinueHazard]
  have htends : Tendsto
      (quittingHazardSurvival quittingAlwaysContinueHazard)
      atTop (nhds 1) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) using 1
    funext fuel
    exact hconstant fuel
  exact tendsto_nhds_unique
    (tendsto_quittingHazardSurvival_neverMass quittingAlwaysContinueHazard)
    htends

omit [Nontrivial ι] in
/-- Exact zero-pattern classification for one deleted clock.  Its terminal
survival is zero exactly when some player outside the deleted mover/observer
pair has zero cemetery mass. -/
theorem quittingPairDeletedSurvivalLimit_eq_zero_iff
    (roots : ℕ → ι → PMF Bool) (mover observer : ι) :
    quittingPairDeletedSurvivalLimit roots mover observer 0 = 0 ↔
      ∃ sentinel, sentinel ≠ mover ∧ sentinel ≠ observer ∧
        quittingHazardNeverMass
          (quittingRootSequenceOwnHazard roots sentinel) = 0 := by
  let deletedRoots :=
    quittingRootSequenceUpdate
      (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
      mover quittingAlwaysContinueHazard
  have horiginal : ∀ player, player ≠ mover → player ≠ observer →
      quittingRootSequenceOwnHazard deletedRoots player =
        quittingRootSequenceOwnHazard roots player := by
    intro player hplayerMover hplayerObserver
    funext time
    simp [deletedRoots, quittingRootSequenceOwnHazard,
      quittingRootSequenceUpdate, Function.update_of_ne hplayerMover,
      Function.update_of_ne hplayerObserver]
  have hmoverHazard : quittingRootSequenceOwnHazard deletedRoots mover =
      quittingAlwaysContinueHazard := by
    funext time
    simp [deletedRoots, quittingRootSequenceOwnHazard,
      quittingRootSequenceUpdate]
  have hobserverHazard : quittingRootSequenceOwnHazard deletedRoots observer =
      quittingAlwaysContinueHazard := by
    by_cases hobserverMover : observer = mover
    · simpa [hobserverMover] using hmoverHazard
    · funext time
      simp [deletedRoots, quittingRootSequenceOwnHazard,
        quittingRootSequenceUpdate, Function.update_of_ne hobserverMover]
  rw [quittingPairDeletedSurvivalLimit_eq_prod_neverMass]
  change (∏ player ∈ Finset.univ,
    quittingHazardNeverMass
      (quittingRootSequenceOwnHazard deletedRoots player)) = 0 ↔ _
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨sentinel, hsentinel⟩
    have hsentinelMover : sentinel ≠ mover := by
      intro heq
      subst sentinel
      rw [hmoverHazard, quittingHazardNeverMass_alwaysContinue] at hsentinel
      norm_num at hsentinel
    have hsentinelObserver : sentinel ≠ observer := by
      intro heq
      subst sentinel
      rw [hobserverHazard, quittingHazardNeverMass_alwaysContinue] at hsentinel
      norm_num at hsentinel
    refine ⟨sentinel, hsentinelMover, hsentinelObserver, ?_⟩
    rwa [horiginal sentinel hsentinelMover hsentinelObserver] at hsentinel
  · rintro ⟨sentinel, hsentinelMover, hsentinelObserver, hsentinel⟩
    refine ⟨sentinel, ?_⟩
    rwa [horiginal sentinel hsentinelMover hsentinelObserver]

omit [Nontrivial ι] in
theorem quittingPairDeletedSurvivalLimit_nonneg
    (roots : ℕ → ι → PMF Bool) (mover observer : ι) :
    0 ≤ quittingPairDeletedSurvivalLimit roots mover observer 0 := by
  unfold quittingPairDeletedSurvivalLimit
  exact quittingOpponentSurvivalLimit_nonneg _ _ _

/-- A specified observer's terminal deleted clock lies below the maximum over
all observers distinct from the mover. -/
theorem quittingPairDeletedSurvivalLimit_le_max
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (hmoverObserver : mover ≠ observer) :
    quittingPairDeletedSurvivalLimit roots mover observer 0 ≤
      quittingMaxPairDeletedSurvivalLimit roots mover 0 := by
  unfold quittingMaxPairDeletedSurvivalLimit
  exact Finset.le_sup'
    (fun who => quittingPairDeletedSurvivalLimit roots mover who 0)
    (Finset.mem_erase.mpr
      ⟨hmoverObserver.symm, Finset.mem_univ observer⟩)

/-- **Exact finite zero-pattern classification.**  A mover's maximal terminal
pair-deleted clock vanishes exactly when at least two distinct *other*
players have zero Never mass.  Thus the useful occupation geometry is a
finite support pattern, and its bootstrap threshold really is two. -/
theorem quittingMaxPairDeletedSurvivalLimit_eq_zero_iff_two_zeroNever
    (roots : ℕ → ι → PMF Bool) (mover : ι) :
    quittingMaxPairDeletedSurvivalLimit roots mover 0 = 0 ↔
      ∃ first second,
        first ≠ second ∧ first ≠ mover ∧ second ≠ mover ∧
        quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots first) = 0 ∧
          quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots second) = 0 := by
  constructor
  · intro hmax
    obtain ⟨observer, hobserverMover⟩ : ∃ observer : ι,
        observer ≠ mover := exists_ne mover
    have hobserverClock :
        quittingPairDeletedSurvivalLimit roots mover observer 0 = 0 := by
      apply le_antisymm
      · calc
          quittingPairDeletedSurvivalLimit roots mover observer 0 ≤
              quittingMaxPairDeletedSurvivalLimit roots mover 0 :=
            quittingPairDeletedSurvivalLimit_le_max
              roots mover observer hobserverMover.symm
          _ = 0 := hmax
      · exact quittingPairDeletedSurvivalLimit_nonneg roots mover observer
    obtain ⟨first, hfirstMover, _hfirstObserver, hfirstNever⟩ :=
      (quittingPairDeletedSurvivalLimit_eq_zero_iff
        roots mover observer).mp hobserverClock
    have hfirstClock :
        quittingPairDeletedSurvivalLimit roots mover first 0 = 0 := by
      apply le_antisymm
      · calc
          quittingPairDeletedSurvivalLimit roots mover first 0 ≤
              quittingMaxPairDeletedSurvivalLimit roots mover 0 :=
            quittingPairDeletedSurvivalLimit_le_max
              roots mover first hfirstMover.symm
          _ = 0 := hmax
      · exact quittingPairDeletedSurvivalLimit_nonneg roots mover first
    obtain ⟨second, hsecondMover, hsecondFirst, hsecondNever⟩ :=
      (quittingPairDeletedSurvivalLimit_eq_zero_iff
        roots mover first).mp hfirstClock
    exact ⟨first, second, hsecondFirst.symm, hfirstMover, hsecondMover,
      hfirstNever, hsecondNever⟩
  · rintro ⟨first, second, hfirstSecond, hfirstMover, hsecondMover,
      hfirstNever, hsecondNever⟩
    apply le_antisymm
    · unfold quittingMaxPairDeletedSurvivalLimit
      apply Finset.sup'_le
      intro observer _hobserver
      by_cases hobserverFirst : observer = first
      · apply le_of_eq
        apply (quittingPairDeletedSurvivalLimit_eq_zero_iff
          roots mover observer).mpr
        refine ⟨second, hsecondMover, ?_, hsecondNever⟩
        exact fun h => hfirstSecond (hobserverFirst.symm.trans h.symm)
      · apply le_of_eq
        apply (quittingPairDeletedSurvivalLimit_eq_zero_iff
          roots mover observer).mpr
        exact ⟨first, hfirstMover, (fun h => hobserverFirst h.symm),
          hfirstNever⟩
    · exact quittingMaxPairDeletedSurvivalLimit_nonneg roots mover 0

/-- Two distinct zero-Never opponents already kill a mover's maximal
pair-deleted clock asymptotically; they need not first be converted to literal
sure-Quit rows. -/
theorem tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_zeroNever
    (roots : ℕ → ι → PMF Bool) (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (hneverFirst : quittingHazardNeverMass
      (quittingRootSequenceOwnHazard roots first) = 0)
    (hneverSecond : quittingHazardNeverMass
      (quittingRootSequenceOwnHazard roots second) = 0) :
    Tendsto (fun fuel =>
      quittingMaxPairDeletedSurvivalWeight roots mover 0 fuel)
      atTop (nhds 0) := by
  let firstSurvival := fun fuel => quittingHazardSurvival
    (quittingRootSequenceOwnHazard roots first) fuel
  let secondSurvival := fun fuel => quittingHazardSurvival
    (quittingRootSequenceOwnHazard roots second) fuel
  have hfirst : Tendsto firstSurvival atTop (nhds 0) := by
    simpa [firstSurvival, hneverFirst] using
      tendsto_quittingHazardSurvival_neverMass
        (quittingRootSequenceOwnHazard roots first)
  have hsecond : Tendsto secondSurvival atTop (nhds 0) := by
    simpa [secondSurvival, hneverSecond] using
      tendsto_quittingHazardSurvival_neverMass
        (quittingRootSequenceOwnHazard roots second)
  apply squeeze_zero
    (quittingMaxPairDeletedSurvivalWeight_nonneg roots mover 0)
    (fun fuel => ?_)
    (by simpa using hfirst.add hsecond)
  unfold quittingMaxPairDeletedSurvivalWeight
  apply Finset.sup'_le
  intro observer _
  by_cases hobserverFirst : observer = first
  · calc
      quittingPairDeletedSurvivalWeight roots mover observer 0 fuel ≤
          secondSurvival fuel := by
        apply quittingPairDeletedSurvivalWeight_le_hazardSurvival_of_other
          roots mover observer second hsecondMover
        exact fun h => hfirstSecond (hobserverFirst.symm.trans h.symm)
      _ ≤ firstSurvival fuel + secondSurvival fuel := by
        exact le_add_of_nonneg_left
          (quittingHazardSurvival_nonneg _ fuel)
  · calc
      quittingPairDeletedSurvivalWeight roots mover observer 0 fuel ≤
          firstSurvival fuel := by
        apply quittingPairDeletedSurvivalWeight_le_hazardSurvival_of_other
          roots mover observer first hfirstMover
        exact fun h => hobserverFirst h.symm
      _ ≤ firstSurvival fuel + secondSurvival fuel := by
        exact le_add_of_nonneg_right
          (quittingHazardSurvival_nonneg _ fuel)

/-- Equivalent convergence form of the exact two-zero-Never clock
classification. -/
theorem tendsto_quittingMaxPairDeletedSurvivalWeight_zero_iff_two_zeroNever
    (roots : ℕ → ι → PMF Bool) (mover : ι) :
    Tendsto (fun fuel =>
      quittingMaxPairDeletedSurvivalWeight roots mover 0 fuel)
        atTop (nhds 0) ↔
      ∃ first second,
        first ≠ second ∧ first ≠ mover ∧ second ≠ mover ∧
        quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots first) = 0 ∧
          quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots second) = 0 := by
  constructor
  · intro hzero
    have hlimit : quittingMaxPairDeletedSurvivalLimit roots mover 0 = 0 :=
      tendsto_nhds_unique
        (tendsto_quittingMaxPairDeletedSurvivalLimit roots mover 0) hzero
    exact
      (quittingMaxPairDeletedSurvivalLimit_eq_zero_iff_two_zeroNever
        roots mover).mp hlimit
  · rintro ⟨first, second, hfirstSecond, hfirstMover, hsecondMover,
      hfirstNever, hsecondNever⟩
    exact
      tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_zeroNever
        roots mover first second hfirstSecond hfirstMover hsecondMover
          hfirstNever hsecondNever

/-- **Exact finite classification of the explicit cap criterion.**  The
finite-splice error tends to zero exactly in one of two zero-pattern regimes:
the moved law has no cemetery atom, or two distinct other coordinates have no
cemetery atom.  This is an exact equivalence for the universal splice bound,
not a necessity claim for payoff-specific cancellations. -/
theorem tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern
    (roots : ℕ → ι → PMF Bool) (mover : ι)
    (hazard : ℕ → PMF Bool) :
    Tendsto (quittingFiniteSpliceError roots mover hazard)
        atTop (nhds 0) ↔
      quittingHazardNeverMass hazard = 0 ∨
        ∃ first second,
          first ≠ second ∧ first ≠ mover ∧ second ≠ mover ∧
          quittingHazardNeverMass
              (quittingRootSequenceOwnHazard roots first) = 0 ∧
            quittingHazardNeverMass
              (quittingRootSequenceOwnHazard roots second) = 0 := by
  constructor
  · intro hzero
    have hterminal :=
      tendsto_quittingFiniteSpliceError_terminal roots mover hazard
    have hproduct : quittingHazardNeverMass hazard *
        quittingMaxPairDeletedSurvivalLimit roots mover 0 = 0 :=
      tendsto_nhds_unique hterminal hzero
    rcases mul_eq_zero.mp hproduct with hnever | hclock
    · exact Or.inl hnever
    · exact Or.inr
        ((quittingMaxPairDeletedSurvivalLimit_eq_zero_iff_two_zeroNever
          roots mover).mp hclock)
  · rintro (hnever | ⟨first, second, hfirstSecond, hfirstMover,
      hsecondMover, hfirstNever, hsecondNever⟩)
    · exact tendsto_quittingFiniteSpliceError_zero_of_neverMass_zero
        roots mover hazard hnever
    · exact tendsto_quittingFiniteSpliceError_zero_of_pairDeleted
        roots mover hazard
          (tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_zeroNever
            roots mover first second hfirstSecond hfirstMover hsecondMover
              hfirstNever hsecondNever)

/-- Globally, every coordinate satisfies the universal finite-cap criterion
exactly when the profile contains at least two distinct zero-Never
coordinates.  This packages the three bootstrap classes `0`, `1`, and `≥ 2`.-/
theorem all_quittingFiniteSpliceError_tendsto_zero_iff_two_zeroNever
    (roots : ℕ → ι → PMF Bool) :
    (∀ mover, Tendsto
      (quittingFiniteSpliceError roots mover
        (quittingRootSequenceOwnHazard roots mover))
      atTop (nhds 0)) ↔
      ∃ first second,
        first ≠ second ∧
        quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots first) = 0 ∧
          quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots second) = 0 := by
  constructor
  · intro hall
    let mover : ι := Classical.choice (inferInstance : Nonempty ι)
    obtain ⟨other, hotherMover⟩ : ∃ other : ι, other ≠ mover :=
      exists_ne mover
    rcases (tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern
      roots mover (quittingRootSequenceOwnHazard roots mover)).mp
        (hall mover) with hmoverNever | htwo
    · rcases (tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern
        roots other (quittingRootSequenceOwnHazard roots other)).mp
          (hall other) with hotherNever | htwoOther
      · exact ⟨mover, other, hotherMover.symm, hmoverNever, hotherNever⟩
      · obtain ⟨first, second, hfirstSecond, _hfirstOther,
            _hsecondOther, hfirstNever, hsecondNever⟩ := htwoOther
        exact ⟨first, second, hfirstSecond, hfirstNever, hsecondNever⟩
    · obtain ⟨first, second, hfirstSecond, _hfirstMover,
          _hsecondMover, hfirstNever, hsecondNever⟩ := htwo
      exact ⟨first, second, hfirstSecond, hfirstNever, hsecondNever⟩
  · rintro ⟨first, second, hfirstSecond, hfirstNever, hsecondNever⟩
    intro mover
    apply (tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern
      roots mover (quittingRootSequenceOwnHazard roots mover)).mpr
    by_cases hmoverFirst : mover = first
    · left
      simpa [hmoverFirst] using hfirstNever
    by_cases hmoverSecond : mover = second
    · left
      simpa [hmoverSecond] using hsecondNever
    · right
      exact ⟨first, second, hfirstSecond, Ne.symm hmoverFirst,
        Ne.symm hmoverSecond, hfirstNever, hsecondNever⟩

/-- Two distinct finite sure-quit sentinels, both different from the reset
mover, kill the maximum pair-deleted clock: deleting one observer can erase at
most one sentinel. -/
theorem quittingMaxPairDeletedSurvivalWeight_eq_zero_of_two_sentinels
    (roots : ℕ → ι → PMF Bool) (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (firstTime secondTime fuel : ℕ)
    (hfirstFuel : firstTime < fuel) (hsecondFuel : secondTime < fuel)
    (hfirst : roots firstTime first = PMF.pure true)
    (hsecond : roots secondTime second = PMF.pure true) :
    quittingMaxPairDeletedSurvivalWeight roots mover 0 fuel = 0 := by
  apply le_antisymm
  · unfold quittingMaxPairDeletedSurvivalWeight
    apply Finset.sup'_le
    intro observer _hobserver
    by_cases hobserverFirst : observer = first
    · apply le_of_eq
      apply quittingPairDeletedSurvivalWeight_eq_zero_of_sure_other
        roots mover observer second hsecondMover
      · exact fun h => hfirstSecond (hobserverFirst.symm.trans h.symm)
      · exact hsecondFuel
      · exact hsecond
    · apply le_of_eq
      apply quittingPairDeletedSurvivalWeight_eq_zero_of_sure_other
        roots mover observer first hfirstMover
      · exact fun h => hobserverFirst h.symm
      · exact hfirstFuel
      · exact hfirst
  · exact quittingMaxPairDeletedSurvivalWeight_nonneg roots mover 0 fuel

/-- The two-sentinel maximum clock is eventually identically zero. -/
theorem tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_sentinels
    (roots : ℕ → ι → PMF Bool) (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (firstTime secondTime : ℕ)
    (hfirst : roots firstTime first = PMF.pure true)
    (hsecond : roots secondTime second = PMF.pure true) :
    Tendsto (fun fuel =>
      quittingMaxPairDeletedSurvivalWeight roots mover 0 fuel)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max firstTime secondTime + 1, fun fuel hfuel => ?_⟩
  have hfirstFuel : firstTime < fuel := by omega
  have hsecondFuel : secondTime < fuel := by omega
  rw [quittingMaxPairDeletedSurvivalWeight_eq_zero_of_two_sentinels
    roots mover first second hfirstSecond hfirstMover hsecondMover
      firstTime secondTime fuel hfirstFuel hsecondFuel hfirst hsecond]
  simpa using hε

end GameTheory
