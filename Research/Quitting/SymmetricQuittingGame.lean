/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Fully symmetric quitting games have a uniform-equilibrium payoff

A quitting table is *fully symmetric* when relabelling the players leaves it
unchanged: `r_{π i}(π S) = r_i(S)` for every permutation `π`.  Equivalently,
`r_i(S)` depends only on the size of `S` and on whether `i` belongs to it.

Such a game always has an exact stationary equilibrium, hence a
uniform-equilibrium payoff.  Either no player has a profitable solo exit, in
which case the empty exit set is already a sure exit set, or some player does,
and enlarging a coalition whose members all strictly prefer it to being left
behind must terminate at a sure exit set.  The proof produces the witness by
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`, so the
equilibrium payoff is the exit reward of the located coalition.
-/

noncomputable section

namespace GameTheory

open StochasticGame QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Relabelling coalitions -/

omit [Fintype ι] in
/-- A set is invariant under a transposition of two points that lie on the
same side of it. -/
theorem Finset.image_swap_self_of_mem_iff
    {T : Finset ι} {first second : ι} (hside : first ∈ T ↔ second ∈ T) :
    T.image (Equiv.swap first second) = T := by
  have hinvariant : ∀ x : ι, Equiv.swap first second x ∈ T ↔ x ∈ T := by
    intro x
    rcases eq_or_ne x first with rfl | hfirst
    · rw [Equiv.swap_apply_left]
      exact ⟨fun h => hside.mpr h, fun h => hside.mp h⟩
    · rcases eq_or_ne x second with rfl | hsecond
      · rw [Equiv.swap_apply_right]
        exact ⟨fun h => hside.mp h, fun h => hside.mpr h⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hfirst hsecond]
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (hinvariant x).mpr hx
  · rw [Finset.card_image_of_injective _ (Equiv.injective _)]

/-- **Coalitions of equal size are relabellings of one another**, and the
relabelling may be prescribed at one point on each side, provided that point
lies inside both coalitions or outside both. -/
theorem exists_perm_image_eq_of_card_eq_of_mem_iff
    {S T : Finset ι} {i j : ι} (hcard : S.card = T.card)
    (hmemIff : i ∈ S ↔ j ∈ T) :
    ∃ π : Equiv.Perm ι, S.image π = T ∧ π i = j := by
  classical
  have hinside : Fintype.card {x : ι // x ∈ S} = Fintype.card {x : ι // x ∈ T} := by
    simpa using hcard
  have houtside :
      Fintype.card {x : ι // ¬ x ∈ S} = Fintype.card {x : ι // ¬ x ∈ T} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hinside]
  set inside := Fintype.equivOfCardEq hinside with hinsideDef
  set outside := Fintype.equivOfCardEq houtside with houtsideDef
  set base : Equiv.Perm ι :=
    (Equiv.sumCompl (· ∈ S)).symm.trans
      ((inside.sumCongr outside).trans (Equiv.sumCompl (· ∈ T))) with hbase
  have hforward : ∀ x : ι, x ∈ S → base x ∈ T := by
    intro x hx
    have hstep : base x = ((inside ⟨x, hx⟩ : {y : ι // y ∈ T}) : ι) := by
      rw [hbase]
      simp [Equiv.sumCompl_symm_apply_of_pos hx]
    rw [hstep]
    exact (inside ⟨x, hx⟩).2
  have hbackward : ∀ x : ι, x ∉ S → base x ∉ T := by
    intro x hx
    have hstep : base x = ((outside ⟨x, hx⟩ : {y : ι // ¬ y ∈ T}) : ι) := by
      rw [hbase]
      simp [Equiv.sumCompl_symm_apply_of_neg hx]
    rw [hstep]
    exact (outside ⟨x, hx⟩).2
  have hbaseImage : S.image base = T := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact hforward x hx
    · rw [Finset.card_image_of_injective _ base.injective, hcard]
  have hside : base i ∈ T ↔ j ∈ T := by
    constructor
    · intro hbaseMem
      refine hmemIff.mp ?_
      by_contra hnot
      exact hbackward i hnot hbaseMem
    · intro hj
      exact hforward i (hmemIff.mpr hj)
  refine ⟨base.trans (Equiv.swap (base i) j), ?_, ?_⟩
  · rw [show S.image (base.trans (Equiv.swap (base i) j)) =
        (S.image base).image (Equiv.swap (base i) j) by
      rw [Finset.image_image]; rfl]
    rw [hbaseImage, Finset.image_swap_self_of_mem_iff hside]
  · exact Equiv.swap_apply_left _ _

/-! ## Symmetry of a quitting table -/

/-- **Full symmetry.**  Relabelling the players by any permutation leaves the
table unchanged.  The extended convention `r_i(∅) = 0` of `quittingSetReward`
makes the empty coalition an automatic instance. -/
def IsQuittingPermutationSymmetric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (π : Equiv.Perm ι) (S : Finset ι) (i : ι),
    quittingSetReward reward (S.image π) (π i) = quittingSetReward reward S i

/-- **The cardinality form of symmetry.**  A player's reward depends only on
the size of the quitting coalition and on whether that player belongs to
it. -/
def IsQuittingCardinalSymmetric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (S T : Finset ι) (i j : ι), S.card = T.card → (i ∈ S ↔ j ∈ T) →
    quittingSetReward reward S i = quittingSetReward reward T j

omit [Fintype ι] in
/-- Full symmetry stated on nonempty coalitions, as `r_{π i}(π S) = r_i(S)`,
gives the extended form. -/
theorem isQuittingPermutationSymmetric_of_forall_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsymmetric : ∀ (π : Equiv.Perm ι) (S : Finset ι) (hS : S.Nonempty) (i : ι),
      reward ⟨S.image π, Finset.image_nonempty.mpr hS⟩ (π i) = reward ⟨S, hS⟩ i) :
    IsQuittingPermutationSymmetric reward := by
  intro π S i
  by_cases hS : S.Nonempty
  · rw [quittingSetReward_of_nonempty reward (Finset.image_nonempty.mpr hS),
      quittingSetReward_of_nonempty reward hS]
    exact hsymmetric π S hS i
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp [quittingSetReward]

/-- Permutation symmetry is the cardinality form. -/
theorem isQuittingCardinalSymmetric_of_permutationSymmetric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsymmetric : IsQuittingPermutationSymmetric reward) :
    IsQuittingCardinalSymmetric reward := by
  intro S T i j hcard hmemIff
  obtain ⟨π, himage, happly⟩ :=
    exists_perm_image_eq_of_card_eq_of_mem_iff hcard hmemIff
  have hstep := hsymmetric π S i
  rw [himage, happly] at hstep
  exact hstep.symm

/-! ## Locating a sure exit set -/

/-- **The enlargement step.**  A coalition every member of which strictly
prefers the coalition to being left behind is either a sure exit set already,
or can be enlarged by one strictly tempted outsider without losing that
property.  Since the player type is finite, the enlargement terminates. -/
theorem exists_isQuittingSureExitSet_of_forall_member_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsymmetric : IsQuittingCardinalSymmetric reward) :
    ∀ (fuel : ℕ) (E : Finset ι), Fintype.card ι - E.card ≤ fuel →
      (∀ member ∈ E, quittingSetReward reward (E.erase member) member <
        quittingSetReward reward E member) →
      ∃ F : Finset ι, IsQuittingSureExitSet reward F := by
  intro fuel
  induction fuel with
  | zero =>
      intro E hfuel hmember
      by_cases houtsider : ∀ outsider ∉ E,
          quittingSetReward reward (insert outsider E) outsider ≤
            quittingSetReward reward E outsider
      · exact ⟨E, fun m hm => (hmember m hm).le, houtsider⟩
      · push Not at houtsider
        obtain ⟨outsider, hout, -⟩ := houtsider
        have hlt : E.card < Fintype.card ι := by
          have hsub : E ⊂ Finset.univ :=
            Finset.ssubset_univ_iff.mpr fun heq => hout (heq ▸ Finset.mem_univ outsider)
          simpa using Finset.card_lt_card hsub
        omega
  | succ fuel ih =>
      intro E hfuel hmember
      by_cases houtsider : ∀ outsider ∉ E,
          quittingSetReward reward (insert outsider E) outsider ≤
            quittingSetReward reward E outsider
      · exact ⟨E, fun m hm => (hmember m hm).le, houtsider⟩
      · push Not at houtsider
        obtain ⟨outsider, hout, hgain⟩ := houtsider
        have hcardInsert : (insert outsider E).card = E.card + 1 :=
          Finset.card_insert_of_notMem hout
        refine ih (insert outsider E) (by omega) ?_
        intro member hmem
        rcases eq_or_ne member outsider with rfl | hne
        · rwa [Finset.erase_insert hout]
        · have hmemE : member ∈ E := (Finset.mem_insert.mp hmem).resolve_left hne
          have hnotSelf : outsider ∉ E.erase member :=
            fun h => hout (Finset.mem_of_mem_erase h)
          have herase : (insert outsider E).erase member =
              insert outsider (E.erase member) := by
            rw [Finset.erase_insert_of_ne hne.symm]
          have hleftCard : (insert outsider (E.erase member)).card = E.card := by
            rw [Finset.card_insert_of_notMem hnotSelf,
              Finset.card_erase_of_mem hmemE]
            have : 1 ≤ E.card := Finset.card_pos.mpr ⟨member, hmemE⟩
            omega
          have hleft : quittingSetReward reward
              (insert outsider (E.erase member)) member =
            quittingSetReward reward E outsider := by
            refine hsymmetric _ _ _ _ hleftCard ?_
            constructor
            · intro hcontra
              rcases Finset.mem_insert.mp hcontra with heq | hin
              · exact absurd heq hne
              · exact absurd (Finset.mem_erase.mp hin).1 (by simp)
            · intro hcontra
              exact absurd hcontra hout
          have hright : quittingSetReward reward (insert outsider E) member =
              quittingSetReward reward (insert outsider E) outsider := by
            refine hsymmetric _ _ _ _ rfl ?_
            exact ⟨fun _ => Finset.mem_insert_self outsider E,
              fun _ => Finset.mem_insert_of_mem hmemE⟩
          rw [herase, hleft, hright]
          exact hgain

/-- **Every fully symmetric finite quitting game has a sure exit set.** -/
theorem exists_isQuittingSureExitSet_of_cardinalSymmetric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsymmetric : IsQuittingCardinalSymmetric reward) :
    ∃ E : Finset ι, IsQuittingSureExitSet reward E := by
  by_cases hsolo : ∀ who : ι, quittingSetReward reward {who} who ≤ 0
  · refine ⟨∅, fun member hmember => absurd hmember (Finset.notMem_empty member),
      fun outsider _ => ?_⟩
    simpa [quittingSetReward] using hsolo outsider
  · push Not at hsolo
    obtain ⟨who, hwho⟩ := hsolo
    refine exists_isQuittingSureExitSet_of_forall_member_lt reward hsymmetric
      (Fintype.card ι) {who} (by omega) ?_
    intro member hmember
    obtain rfl := Finset.mem_singleton.mp hmember
    simpa [quittingSetReward] using hwho

/-- **Every fully symmetric finite quitting game has a uniform-equilibrium
payoff**, namely the exit reward of a symmetric sure exit set. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_cardinalSymmetric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsymmetric : IsQuittingCardinalSymmetric reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨E, hE⟩ :=
    exists_isQuittingSureExitSet_of_cardinalSymmetric reward hsymmetric
  exact ⟨quittingSetReward reward E,
    isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward hE⟩

/-- **The permutation form.**  Every finite quitting game whose table is
invariant under all player permutations has a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_permutationSymmetric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsymmetric : IsQuittingPermutationSymmetric reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_cardinalSymmetric reward
    (isQuittingCardinalSymmetric_of_permutationSymmetric reward hsymmetric)

end GameTheory
