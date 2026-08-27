/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FinFourCoalitionCycle

/-!
# Ordered one-coordinate cycles on four players

This file develops structural, edge-free infrastructure for the finite-four
cycle theorem.  It does not enumerate edge masks: the cardinality bound uses
the pair/triple bipartition, and the finite pair-family classification records
the star-or-triangle alternatives.  The ordered-cycle geometry, including the
universal coalition, is proved from the word interface below.  Period two is
admitted as an injective cyclic word, traversing one undirected edge twice;
ordinary simple graph cycles conventionally exclude this case.
-/

namespace MathUE.FinFourCoalitionCycle

def isTriple (c : CoalitionCode) : Prop := 6 ≤ c.val ∧ c.val < 10

instance (c : CoalitionCode) : Decidable (isTriple c) := by
  unfold isTriple
  infer_instance

def tripleCodes : Finset CoalitionCode := {6, 7, 8, 9}

theorem isTriple_iff_mem_tripleCodes (c : CoalitionCode) :
    isTriple c ↔ c ∈ tripleCodes := by
  fin_cases c <;> decide

theorem adjacent_triple_xor (c d : CoalitionCode)
    (h : oneCoordinateAdjacent c d) :
    isTriple c ↔ ¬isTriple d := by
  fin_cases c <;> fin_cases d <;>
    first
    | decide
    | exfalso
      revert h
      decide

def cycleNext' (period : Nat) (period_pos : 0 < period) (i : Fin period) :
    Fin period :=
  ⟨(i.val + 1) % period, Nat.mod_lt _ period_pos⟩

theorem cycleNext'_injective (period : Nat) (period_pos : 0 < period) :
    Function.Injective (cycleNext' period period_pos) := by
  intro i j h
  apply Fin.ext
  have h' := congrArg Fin.val h
  dsimp [cycleNext'] at h'
  have hi : i.val + 1 ≤ period := by omega
  have hj : j.val + 1 ≤ period := by omega
  by_cases hil : i.val + 1 < period
  · have hi' : (i.val + 1) % period = i.val + 1 := Nat.mod_eq_of_lt hil
    by_cases hjl : j.val + 1 < period
    · have hj' : (j.val + 1) % period = j.val + 1 := Nat.mod_eq_of_lt hjl
      omega
    · have hj' : j.val + 1 = period := by omega
      rw [hj', Nat.mod_self] at h'
      omega
  · have hi' : i.val + 1 = period := by omega
    by_cases hjl : j.val + 1 < period
    · have hj' : (j.val + 1) % period = j.val + 1 := Nat.mod_eq_of_lt hjl
      rw [hi', Nat.mod_self] at h'
      omega
    · have hj' : j.val + 1 = period := by omega
      omega

theorem cycleNext'_bijective (period : Nat) (period_pos : 0 < period) :
    Function.Bijective (cycleNext' period period_pos) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨cycleNext'_injective period period_pos, rfl⟩

theorem cycleNext'_two_step_ne (period : Nat) (period_ge_three : 3 ≤ period)
    (i : Fin period) :
    cycleNext' period (by omega)
        (cycleNext' period (by omega) i) ≠ i := by
  intro h
  have h' := congrArg Fin.val h
  dsimp [cycleNext'] at h'
  have hi : i.val + 1 ≤ period := by omega
  by_cases hfirst : i.val + 1 < period
  · rw [Nat.mod_eq_of_lt hfirst] at h'
    have hsecond : i.val + 2 ≤ period := by omega
    by_cases hwrap : i.val + 2 < period
    · rw [Nat.mod_eq_of_lt hwrap] at h'
      omega
    · have : i.val + 2 = period := by omega
      rw [this, Nat.mod_self] at h'
      omega
  · have : i.val + 1 = period := by omega
    rw [this, Nat.mod_self] at h'
    have : (1 : Nat) < period := by omega
    rw [Nat.mod_eq_of_lt this] at h'
    omega

structure OrderedBooleanCycle where
  period : Nat
  period_pos : 0 < period
  vertex : Fin period → CoalitionCode
  vertex_injective : Function.Injective vertex
  adjacent : ∀ i,
    oneCoordinateAdjacent (vertex i)
      (vertex (cycleNext' period period_pos i))

theorem orderedBooleanCycle_card_le_eight
    (cycle : OrderedBooleanCycle) : cycle.period ≤ 8 := by
  let t : Finset (Fin cycle.period) :=
    Finset.univ.filter (fun i => isTriple (cycle.vertex i))
  let n : Finset (Fin cycle.period) :=
    Finset.univ.filter (fun i => ¬isTriple (cycle.vertex i))
  have htn : t.card = n.card := by
    apply Finset.card_bijective (cycleNext' cycle.period cycle.period_pos)
      (cycleNext'_bijective cycle.period cycle.period_pos)
    intro i
    simp only [t, n, Finset.mem_filter, Finset.mem_univ, true_and]
    exact adjacent_triple_xor _ _ (cycle.adjacent i)
  have hdisjoint : Disjoint t n := by
    apply Finset.disjoint_left.2
    intro i hi hj
    exact (Finset.mem_filter.1 hj).2 (Finset.mem_filter.1 hi).2
  have hunion : t ∪ n = Finset.univ := by
    ext i
    simp only [t, n, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨fun _ => trivial, fun _ => Classical.em _⟩
  have hsum : t.card + n.card = cycle.period := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
    simp
  have ht_le : t.card ≤ 4 := by
    let image := t.image cycle.vertex
    have himage : image.card = t.card := by
      exact Finset.card_image_of_injective _ cycle.vertex_injective
    have hsubset : image ⊆ tripleCodes := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
      exact (isTriple_iff_mem_tripleCodes _).1 (Finset.mem_filter.1 hi).2
    rw [← himage]
    exact (Finset.card_le_card hsubset).trans_eq (by decide)
  omega

def pairCode (i : Fin 6) : CoalitionCode := ⟨i.val, by omega⟩

theorem pairCode_card (i : Fin 6) :
    (coalitionSet (pairCode i)).card = 2 := by
  revert i
  decide

theorem pairCode_injective : Function.Injective pairCode := by
  intro a b h
  apply Fin.ext
  have hh : (pairCode a).val = (pairCode b).val := congrArg Fin.val h
  simpa [pairCode] using hh

theorem adjacent_pair_target_is_triple (i : Fin 6) (d : CoalitionCode)
    (h : oneCoordinateAdjacent (pairCode i) d) : isTriple d := by
  revert d i
  decide

theorem adjacent_symmetric (c d : CoalitionCode)
    (h : oneCoordinateAdjacent c d) :
    oneCoordinateAdjacent d c := by
  revert d c
  decide

def pairNeighbors (i : Fin 6) : Finset CoalitionCode :=
  Finset.univ.filter (oneCoordinateAdjacent (pairCode i))

theorem pairNeighbors_card (i : Fin 6) : (pairNeighbors i).card = 2 := by
  revert i
  decide

theorem pairNeighbors_eq_of_mem_distinct (i : Fin 6) (x y : CoalitionCode)
    (hx : x ∈ pairNeighbors i) (hy : y ∈ pairNeighbors i) (hxy : x ≠ y) :
    pairNeighbors i = {x, y} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  · rw [pairNeighbors_card, Finset.card_pair hxy]

theorem nontriple_nonuniversal_is_pair (c : CoalitionCode)
    (hc : ¬isTriple c) (hu : c ≠ 10) :
    ∃ i : Fin 6, c = pairCode i := by
  revert c
  decide

theorem ordered_period_one_impossible (v : Fin 1 → CoalitionCode)
    (hadj : ∀ i, oneCoordinateAdjacent (v i)
      (v (cycleNext' 1 (by omega) i))) : False := by
  revert v
  decide

theorem adjacent_pair_subset_of_triple (i : Fin 6) (d : CoalitionCode)
    (hd : isTriple d) (h : oneCoordinateAdjacent (pairCode i) d) :
    coalitionSet (pairCode i) ⊆ coalitionSet d := by
  revert d i
  decide

theorem adjacent_pair_contains_player (i : Fin 6) (d : CoalitionCode)
    (p : Player) (hpi : p ∈ coalitionSet (pairCode i))
    (h : oneCoordinateAdjacent (pairCode i) d) :
    p ∈ coalitionSet d := by
  have hd := adjacent_pair_target_is_triple i d h
  exact (adjacent_pair_subset_of_triple i d hd h) hpi

theorem adjacent_pair_transition_unique (a b : Fin 6) (d e : CoalitionCode)
    (hab : a ≠ b)
    (hd : oneCoordinateAdjacent (pairCode a) d ∧
      oneCoordinateAdjacent (pairCode b) d)
    (he : oneCoordinateAdjacent (pairCode a) e ∧
      oneCoordinateAdjacent (pairCode b) e) :
    d = e := by
  revert e d b a
  decide

def PairFamilyIntersecting6 (s : Finset (Fin 6)) : Prop :=
  ∀ c ∈ s, ∀ d ∈ s, c ≠ d →
    ¬Disjoint (coalitionSet (pairCode c)) (coalitionSet (pairCode d))

instance (s : Finset (Fin 6)) : Decidable (PairFamilyIntersecting6 s) := by
  unfold PairFamilyIntersecting6
  infer_instance

def PairFamilyStar6 (s : Finset (Fin 6)) : Prop :=
  ∃ p : Player, ∀ c ∈ s, p ∈ coalitionSet (pairCode c)

instance (s : Finset (Fin 6)) : Decidable (PairFamilyStar6 s) := by
  unfold PairFamilyStar6
  infer_instance

def PairFamilyTriangle6 (s : Finset (Fin 6)) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ¬Disjoint (coalitionSet (pairCode a))
        (coalitionSet (pairCode b)) ∧
      ¬Disjoint (coalitionSet (pairCode a))
        (coalitionSet (pairCode c)) ∧
      ¬Disjoint (coalitionSet (pairCode b))
        (coalitionSet (pairCode c)) ∧
      ¬PairFamilyStar6 {a, b, c}

instance (s : Finset (Fin 6)) : Decidable (PairFamilyTriangle6 s) := by
  unfold PairFamilyTriangle6
  infer_instance

def PairFamilyExactTriangle6 (s : Finset (Fin 6)) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ s = {a, b, c} ∧
      ¬Disjoint (coalitionSet (pairCode a))
        (coalitionSet (pairCode b)) ∧
      ¬Disjoint (coalitionSet (pairCode a))
        (coalitionSet (pairCode c)) ∧
      ¬Disjoint (coalitionSet (pairCode b))
        (coalitionSet (pairCode c)) ∧
      ¬PairFamilyStar6 {a, b, c}

instance (s : Finset (Fin 6)) : Decidable (PairFamilyExactTriangle6 s) := by
  unfold PairFamilyExactTriangle6
  infer_instance

def TriangleIndices6 (a b c : Fin 6) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    ¬Disjoint (coalitionSet (pairCode a))
      (coalitionSet (pairCode b)) ∧
    ¬Disjoint (coalitionSet (pairCode a))
      (coalitionSet (pairCode c)) ∧
    ¬Disjoint (coalitionSet (pairCode b))
      (coalitionSet (pairCode c)) ∧
    ¬PairFamilyStar6 {a, b, c}

instance (a b c : Fin 6) : Decidable (TriangleIndices6 a b c) := by
  unfold TriangleIndices6
  infer_instance

theorem triangle_common_triple (a b c : Fin 6)
    (h : TriangleIndices6 a b c) :
    ∃ d : CoalitionCode, ∀ i ∈ ({a, b, c} : Finset (Fin 6)),
      oneCoordinateAdjacent (pairCode i) d := by
  revert c b a
  decide

theorem pair_family_star_or_triangle6 (s : Finset (Fin 6))
    (hi : PairFamilyIntersecting6 s) :
    PairFamilyStar6 s ∨ PairFamilyTriangle6 s := by
  revert s
  decide

theorem pair_family_star_or_exact_triangle6 (s : Finset (Fin 6))
    (hi : PairFamilyIntersecting6 s) :
    PairFamilyStar6 s ∨ PairFamilyExactTriangle6 s := by
  revert s
  decide

theorem triangle_indices_cases (a b c : Fin 6)
    (h : TriangleIndices6 a b c) :
    ({a, b, c} : Finset (Fin 6)) = {0, 1, 3} ∨
    ({a, b, c} : Finset (Fin 6)) = {0, 2, 4} ∨
    ({a, b, c} : Finset (Fin 6)) = {1, 2, 5} ∨
    ({a, b, c} : Finset (Fin 6)) = {3, 4, 5} := by
  revert c b a
  decide

def orderedVertexSupport (cycle : OrderedBooleanCycle) : Finset CoalitionCode :=
  Finset.univ.image cycle.vertex

def orderedPairSupport (cycle : OrderedBooleanCycle) : Finset (Fin 6) :=
  Finset.univ.filter (fun p =>
      pairCode p ∈ orderedVertexSupport cycle)

noncomputable def cyclePrev (cycle : OrderedBooleanCycle) (i : Fin cycle.period) :
    Fin cycle.period :=
  Classical.choose (cycleNext'_bijective cycle.period cycle.period_pos |>.2 i)

theorem cycleNext'_prev (cycle : OrderedBooleanCycle) (i : Fin cycle.period) :
    cycleNext' cycle.period cycle.period_pos (cyclePrev cycle i) = i := by
  exact Classical.choose_spec
    (cycleNext'_bijective cycle.period cycle.period_pos |>.2 i)

theorem cyclePrev_ne_next (cycle : OrderedBooleanCycle)
    (period_ge_three : 3 ≤ cycle.period) (i : Fin cycle.period) :
    cyclePrev cycle i ≠ cycleNext' cycle.period cycle.period_pos i := by
  intro h
  have hh := cycleNext'_prev cycle i
  rw [h] at hh
  exact cycleNext'_two_step_ne cycle.period period_ge_three i hh

theorem cycle_pair_neighbors (cycle : OrderedBooleanCycle)
    (period_ge_three : 3 ≤ cycle.period) (i : Fin cycle.period)
    (p : Fin 6) (hpi : cycle.vertex i = pairCode p) :
    pairNeighbors p =
      {cycle.vertex (cyclePrev cycle i),
        cycle.vertex (cycleNext' cycle.period cycle.period_pos i)} := by
  apply pairNeighbors_eq_of_mem_distinct
  · simp only [pairNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hpi]
    apply adjacent_symmetric
    simpa [cycleNext'_prev cycle i] using
      cycle.adjacent (cyclePrev cycle i)
  · simp only [pairNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hpi]
    exact cycle.adjacent i
  · intro h
    exact (cyclePrev_ne_next cycle period_ge_three i)
      (cycle.vertex_injective h)

theorem mem_orderedPairSupport_iff (cycle : OrderedBooleanCycle) (p : Fin 6) :
    p ∈ orderedPairSupport cycle ↔
      pairCode p ∈ orderedVertexSupport cycle := by
  simp [orderedPairSupport]

theorem ordered_pair_support_subset (cycle : OrderedBooleanCycle) :
    orderedPairSupport cycle ⊆ Finset.univ := by
  simp

theorem ordered_pair_support_intersecting (cycle : OrderedBooleanCycle)
    (hcomp : ¬HasComplementaryPairsOn (orderedVertexSupport cycle)) :
    PairFamilyIntersecting6 (orderedPairSupport cycle) := by
  intro a ha b hb hab hd
  apply hcomp
  refine ⟨pairCode a, ?_, pairCode b, ?_, ?_, ?_, ?_⟩
  · exact (mem_orderedPairSupport_iff cycle a).1 ha
  · exact (mem_orderedPairSupport_iff cycle b).1 hb
  · exact pairCode_card a
  · exact pairCode_card b
  · exact hd

theorem ordered_period_two_common (cycle : OrderedBooleanCycle)
    (hp : cycle.period = 2) :
    HasCommonPlayerOn (orderedVertexSupport cycle) := by
  rcases cycle with ⟨period, period_pos, vertex, vertex_injective, adjacent⟩
  dsimp at hp ⊢
  subst period
  change HasCommonPlayerOn (Finset.univ.image vertex)
  obtain ⟨p, hp0, hp1⟩ := adjacent_pair_has_common_player
    (vertex ⟨0, by omega⟩) (vertex ⟨1, by omega⟩) (by
      simpa [cycleNext'] using adjacent ⟨0, by omega⟩)
  refine ⟨p, ?_⟩
  intro c hc
  obtain ⟨i, -, hci⟩ := Finset.mem_image.1 hc
  rw [← hci]
  have hi : i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ := by
    fin_cases i <;> simp
  rcases hi with rfl | rfl
  · exact hp0
  · exact hp1

theorem ordered_common_of_pair_star (cycle : OrderedBooleanCycle)
    (period_ge_three : 3 ≤ cycle.period)
    (hstar : PairFamilyStar6 (orderedPairSupport cycle)) :
    HasCommonPlayerOn (orderedVertexSupport cycle) := by
  rcases hstar with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro c hc
  obtain ⟨i, -, hci⟩ := Finset.mem_image.1 hc
  rw [← hci]
  by_cases htr : isTriple (cycle.vertex i)
  · have hprev : ¬isTriple (cycle.vertex (cyclePrev cycle i)) := by
      intro hprev
      have hx := adjacent_triple_xor (cycle.vertex (cyclePrev cycle i))
        (cycle.vertex i) (by
          simpa [cycleNext'_prev cycle i] using
            cycle.adjacent (cyclePrev cycle i))
      exact (hx.mp hprev) htr
    have hnext : ¬isTriple
        (cycle.vertex (cycleNext' cycle.period cycle.period_pos i)) := by
      intro hnext
      have hx := adjacent_triple_xor (cycle.vertex i)
        (cycle.vertex (cycleNext' cycle.period cycle.period_pos i))
        (cycle.adjacent i)
      exact (hx.mp htr) hnext
    have hdistinct : cycle.vertex (cyclePrev cycle i) ≠
        cycle.vertex (cycleNext' cycle.period cycle.period_pos i) := by
      intro heq
      exact (cyclePrev_ne_next cycle period_ge_three i)
        (cycle.vertex_injective heq)
    have hprev_pair_or_univ :
        cycle.vertex (cyclePrev cycle i) = 10 ∨
          ∃ q : Fin 6, cycle.vertex (cyclePrev cycle i) = pairCode q := by
      by_cases hu : cycle.vertex (cyclePrev cycle i) = 10
      · exact Or.inl hu
      · exact Or.inr (nontriple_nonuniversal_is_pair _ hprev hu)
    have hnext_pair_or_univ :
        cycle.vertex (cycleNext' cycle.period cycle.period_pos i) = 10 ∨
          ∃ q : Fin 6,
            cycle.vertex (cycleNext' cycle.period cycle.period_pos i) = pairCode q := by
      by_cases hu : cycle.vertex (cycleNext' cycle.period cycle.period_pos i) = 10
      · exact Or.inl hu
      · exact Or.inr (nontriple_nonuniversal_is_pair _ hnext hu)
    rcases hprev_pair_or_univ with hprev_univ | ⟨q, hq⟩
    · rcases hnext_pair_or_univ with hnext_univ | ⟨q, hq⟩
      · exact False.elim (hdistinct (hprev_univ.trans hnext_univ.symm))
      · have hqmem : q ∈ orderedPairSupport cycle := by
          rw [mem_orderedPairSupport_iff]
          refine Finset.mem_image.2 ⟨cycleNext' cycle.period cycle.period_pos i,
            Finset.mem_univ _, hq⟩
        have hqp := hp q hqmem
        exact adjacent_pair_contains_player q (cycle.vertex i) p hqp
          (by
            apply adjacent_symmetric
            simpa [hci, hq] using cycle.adjacent i)
    · have hqmem : q ∈ orderedPairSupport cycle := by
        rw [mem_orderedPairSupport_iff]
        refine Finset.mem_image.2 ⟨cyclePrev cycle i, Finset.mem_univ _, hq⟩
      have hqp := hp q hqmem
      exact adjacent_pair_contains_player q (cycle.vertex i) p hqp (by
        simpa [cycleNext'_prev cycle i, hci, hq] using
          cycle.adjacent (cyclePrev cycle i))
  · by_cases huniv : cycle.vertex i = 10
    · rw [huniv]
      have hall : ∀ q : Player, q ∈ coalitionSet (10 : CoalitionCode) := by
        intro q
        revert q
        decide
      exact hall p
    · obtain ⟨q, hq⟩ := nontriple_nonuniversal_is_pair _ htr huniv
      have hqmem : q ∈ orderedPairSupport cycle := by
        rw [mem_orderedPairSupport_iff]
        exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hq⟩
      rw [hq]
      exact hp q hqmem

theorem no_three_cyclic_pair_neighbors (cycle : OrderedBooleanCycle)
    (period_ge_three : 3 ≤ cycle.period)
    (a b c : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ia ib ic : Fin cycle.period)
    (ha : cycle.vertex ia = pairCode a)
    (hb : cycle.vertex ib = pairCode b)
    (hc : cycle.vertex ic = pairCode c)
    (hcommon : ∃ d : CoalitionCode, ∀ x ∈ ({a, b, c} : Finset (Fin 6)),
      oneCoordinateAdjacent (pairCode x) d) : False := by
  rcases hcommon with ⟨d, hd⟩
  have hia : ia ≠ ib := by
    intro h
    apply hab
    apply pairCode_injective
    rw [← ha, h, hb]
  have hia' : ia ≠ ic := by
    intro h
    apply hac
    apply pairCode_injective
    rw [← ha, h, hc]
  have hib : ib ≠ ic := by
    intro h
    apply hbc
    apply pairCode_injective
    rw [← hb, h, hc]
  have hma : d ∈ pairNeighbors a := by
    simp only [pairNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hd a (by simp)
  rw [cycle_pair_neighbors cycle period_ge_three ia a ha] at hma
  have hmb : d ∈ pairNeighbors b := by
    simp only [pairNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hd b (by simp)
  rw [cycle_pair_neighbors cycle period_ge_three ib b hb] at hmb
  have hmc : d ∈ pairNeighbors c := by
    simp only [pairNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hd c (by simp)
  rw [cycle_pair_neighbors cycle period_ge_three ic c hc] at hmc
  rcases (by simpa using hma) with hda | hda
  · let k := cyclePrev cycle ia
    have hdk : d = cycle.vertex k := hda
    have hka : ia ∈ ({cycleNext' cycle.period cycle.period_pos k,
        cyclePrev cycle k} : Finset (Fin cycle.period)) := by
      exact Finset.mem_insert.2 (Or.inl (by
        simpa [k] using (cycleNext'_prev cycle ia).symm))
    have hkb : ib ∈ ({cycleNext' cycle.period cycle.period_pos k,
        cyclePrev cycle k} : Finset (Fin cycle.period)) := by
      rcases (by simpa using hmb) with hdb | hdb
      · have heq : cyclePrev cycle ib = k := by
          have hv : cycle.vertex (cyclePrev cycle ib) = cycle.vertex k :=
            hdb.symm.trans hdk
          apply cycleNext'_injective cycle.period cycle.period_pos
          exact congrArg (cycleNext' cycle.period cycle.period_pos)
            (cycle.vertex_injective hv)
        exact Finset.mem_insert.2 (Or.inl (by
          simpa [heq] using (cycleNext'_prev cycle ib).symm))
      · have heq : cycleNext' cycle.period cycle.period_pos ib = k :=
          cycle.vertex_injective (hdb.symm.trans hdk)
        have hrel : ib = cyclePrev cycle k := by
          apply cycleNext'_injective cycle.period cycle.period_pos
          rw [cycleNext'_prev cycle k, heq]
        exact Finset.mem_insert.2 (Or.inr (by simp [hrel]))
    have hkc : ic ∈ ({cycleNext' cycle.period cycle.period_pos k,
        cyclePrev cycle k} : Finset (Fin cycle.period)) := by
      rcases (by simpa using hmc) with hdc | hdc
      · have heq : cyclePrev cycle ic = k := by
          have hv : cycle.vertex (cyclePrev cycle ic) = cycle.vertex k :=
            hdc.symm.trans hdk
          apply cycleNext'_injective cycle.period cycle.period_pos
          exact congrArg (cycleNext' cycle.period cycle.period_pos)
            (cycle.vertex_injective hv)
        exact Finset.mem_insert.2 (Or.inl (by
          simpa [heq] using (cycleNext'_prev cycle ic).symm))
      · have heq : cycleNext' cycle.period cycle.period_pos ic = k :=
          cycle.vertex_injective (hdc.symm.trans hdk)
        have hrel : ic = cyclePrev cycle k := by
          apply cycleNext'_injective cycle.period cycle.period_pos
          rw [cycleNext'_prev cycle k, heq]
        exact Finset.mem_insert.2 (Or.inr (by simp [hrel]))
    have hcard : ({ia, ib, ic} : Finset (Fin cycle.period)).card = 3 := by
      simp [hia, hia', hib]
    have hsub : ({ia, ib, ic} : Finset (Fin cycle.period)) ⊆
        {cycleNext' cycle.period cycle.period_pos k, cyclePrev cycle k} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hka
      · exact hkb
      · exact hkc
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    have hpair : ({cycleNext' cycle.period cycle.period_pos k,
        cyclePrev cycle k} : Finset (Fin cycle.period)).card = 2 := by
      exact Finset.card_pair (cyclePrev_ne_next cycle period_ge_three k).symm
    rw [hpair] at hle
    omega
  · let k := cycleNext' cycle.period cycle.period_pos ia
    have hdk : d = cycle.vertex k := hda
    have hka : ia ∈ ({cycleNext' cycle.period cycle.period_pos k,
        cyclePrev cycle k} : Finset (Fin cycle.period)) := by
      have hrel : ia = cyclePrev cycle k := by
        apply cycleNext'_injective cycle.period cycle.period_pos
        rw [cycleNext'_prev cycle k]
      exact Finset.mem_insert.2 (Or.inr (by simpa using hrel))
    have hkb : ib ∈ ({cycleNext' cycle.period cycle.period_pos k,
        cyclePrev cycle k} : Finset (Fin cycle.period)) := by
      rcases (by simpa using hmb) with hdb | hdb
      · have heq : cyclePrev cycle ib = k := by
          have hv : cycle.vertex (cyclePrev cycle ib) = cycle.vertex k :=
            hdb.symm.trans hdk
          apply cycleNext'_injective cycle.period cycle.period_pos
          exact congrArg (cycleNext' cycle.period cycle.period_pos)
            (cycle.vertex_injective hv)
        exact Finset.mem_insert.2 (Or.inl (by
          simpa [heq] using (cycleNext'_prev cycle ib).symm))
      · have heq : cycleNext' cycle.period cycle.period_pos ib = k :=
          cycle.vertex_injective (hdb.symm.trans hdk)
        have hrel : ib = cyclePrev cycle k := by
          apply cycleNext'_injective cycle.period cycle.period_pos
          rw [cycleNext'_prev cycle k, heq]
        exact Finset.mem_insert.2 (Or.inr (by simp [hrel]))
    have hkc : ic ∈ ({cycleNext' cycle.period cycle.period_pos k,
        cyclePrev cycle k} : Finset (Fin cycle.period)) := by
      rcases (by simpa using hmc) with hdc | hdc
      · have heq : cyclePrev cycle ic = k := by
          have hv : cycle.vertex (cyclePrev cycle ic) = cycle.vertex k :=
            hdc.symm.trans hdk
          apply cycleNext'_injective cycle.period cycle.period_pos
          exact congrArg (cycleNext' cycle.period cycle.period_pos)
            (cycle.vertex_injective hv)
        exact Finset.mem_insert.2 (Or.inl (by
          simpa [heq] using (cycleNext'_prev cycle ic).symm))
      · have heq : cycleNext' cycle.period cycle.period_pos ic = k :=
          cycle.vertex_injective (hdc.symm.trans hdk)
        have hrel : ic = cyclePrev cycle k := by
          apply cycleNext'_injective cycle.period cycle.period_pos
          rw [cycleNext'_prev cycle k, heq]
        exact Finset.mem_insert.2 (Or.inr (by simp [hrel]))
    have hcard : ({ia, ib, ic} : Finset (Fin cycle.period)).card = 3 := by
      simp [hia, hia', hib]
    have hsub : ({ia, ib, ic} : Finset (Fin cycle.period)) ⊆
        {cycleNext' cycle.period cycle.period_pos k, cyclePrev cycle k} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hka
      · exact hkb
      · exact hkc
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    have hpair : ({cycleNext' cycle.period cycle.period_pos k,
        cyclePrev cycle k} : Finset (Fin cycle.period)).card = 2 := by
      exact Finset.card_pair (cyclePrev_ne_next cycle period_ge_three k).symm
    rw [hpair] at hle
    omega

theorem ordered_period_one_impossible' (cycle : OrderedBooleanCycle)
    (hp : cycle.period = 1) : False := by
  rcases cycle with ⟨period, period_pos, vertex, vertex_injective, adjacent⟩
  dsimp at hp
  subst period
  have h := adjacent ⟨0, by omega⟩
  have hi : cycleNext' 1 (by omega) ⟨0, by omega⟩ =
      (⟨0, by omega⟩ : Fin 1) := by
    apply Fin.ext
    simp [cycleNext']
  rw [hi] at h
  have hirr : ∀ c : CoalitionCode, ¬oneCoordinateAdjacent c c := by
    intro c
    revert c
    decide
  exact hirr _ h

theorem orderedBooleanCycle_common_or_complementary
    (cycle : OrderedBooleanCycle) :
    HasCommonPlayerOn (orderedVertexSupport cycle) ∨
      HasComplementaryPairsOn (orderedVertexSupport cycle) := by
  by_cases hp1 : cycle.period = 1
  · exact False.elim (ordered_period_one_impossible' cycle hp1)
  by_cases hp2 : cycle.period = 2
  · exact Or.inl (ordered_period_two_common cycle hp2)
  have hpos := cycle.period_pos
  have hp3 : 3 ≤ cycle.period := by omega
  by_cases hcomp : HasComplementaryPairsOn (orderedVertexSupport cycle)
  · exact Or.inr hcomp
  have hpair := ordered_pair_support_intersecting cycle hcomp
  rcases pair_family_star_or_exact_triangle6 (orderedPairSupport cycle) hpair with
    hstar | htriangle
  · exact Or.inl (ordered_common_of_pair_star cycle hp3 hstar)
  · rcases htriangle with ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hset,
        hab', hac', hbc', hnostar⟩
    have htri : TriangleIndices6 a b c :=
      ⟨hab, hac, hbc, hab', hac', hbc', hnostar⟩
    have hma : a ∈ orderedPairSupport cycle := by
      rw [hset]
      simp
    have hmb : b ∈ orderedPairSupport cycle := by
      rw [hset]
      simp
    have hmc : c ∈ orderedPairSupport cycle := by
      rw [hset]
      simp
    obtain ⟨ia, -, hai⟩ := Finset.mem_image.1
      ((mem_orderedPairSupport_iff cycle a).1 hma)
    obtain ⟨ib, -, hbi⟩ := Finset.mem_image.1
      ((mem_orderedPairSupport_iff cycle b).1 hmb)
    obtain ⟨ic, -, hci⟩ := Finset.mem_image.1
      ((mem_orderedPairSupport_iff cycle c).1 hmc)
    exact False.elim (no_three_cyclic_pair_neighbors cycle hp3 a b c
      hab hac hbc ia ib ic hai hbi hci (triangle_common_triple a b c htri))

theorem orderedBooleanCycle_card_le_eight_and_geometry
    (cycle : OrderedBooleanCycle) :
    cycle.period ≤ 8 ∧
      (HasCommonPlayerOn (orderedVertexSupport cycle) ∨
        HasComplementaryPairsOn (orderedVertexSupport cycle)) :=
  ⟨orderedBooleanCycle_card_le_eight cycle,
    orderedBooleanCycle_common_or_complementary cycle⟩

end MathUE.FinFourCoalitionCycle
