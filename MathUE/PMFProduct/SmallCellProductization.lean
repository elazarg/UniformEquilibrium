import MathUE.PMFProduct.SmallHazardBounds
import MathUE.Topology.PoincareMirandaCube

/-!
This file formalizes the small-cell productization argument in
Ashkenazi-Golan--Krasikov--Rainer--Solan, published version, Lemma 4.9.  Its
Poincare--Miranda field and its deletion of zero-singleton players follow the
published proof literally.  The coordinate estimate uses `≤` rather than the
printed `<`, because the weak form also states the degenerate `p = 0` case and
is the form required by downstream consumers.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
private theorem continuous_akrsCoalitionMass (coalition : Finset ι) :
    Continuous fun root : ι → ℝ =>
      Math.PMFProduct.coalitionMass root coalition := by
  unfold Math.PMFProduct.coalitionMass
  fun_prop

omit [DecidableEq ι] [Nonempty ι] in
private theorem continuous_akrsAbsorptionMass :
    Continuous fun root : ι → ℝ =>
      1 - Math.PMFProduct.continueMass root := by
  unfold Math.PMFProduct.continueMass
  fun_prop

omit [Nonempty ι] in
private theorem akrsLawMass_le_absorption_of_nonempty
    {law : Finset ι → ℝ}
    (hlaw_nonneg : ∀ coalition, 0 ≤ law coalition)
    (hlaw_sum : (∑ coalition, law coalition) = 1)
    {coalition : Finset ι} (hcoalition : coalition.Nonempty) :
    law coalition ≤ 1 - law ∅ := by
  have hmem : coalition ∈ Finset.univ.erase (∅ : Finset ι) := by
    simp [Finset.nonempty_iff_ne_empty.mp hcoalition]
  have hsingle := Finset.single_le_sum
    (fun other _ => hlaw_nonneg other) hmem
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (f := law) (Finset.mem_univ (∅ : Finset ι))
  rw [hlaw_sum] at hsplit
  linarith

omit [Nonempty ι] in
private theorem akrsCoalitionMass_le_absorption_sq
    {root : ι → ℝ}
    (hroot_nonneg : ∀ player, 0 ≤ root player)
    (hroot_le_one : ∀ player, root player ≤ 1)
    {coalition : Finset ι} (hcoalition : 2 ≤ coalition.card) :
    Math.PMFProduct.coalitionMass root coalition ≤
      (1 - Math.PMFProduct.continueMass root) ^ 2 := by
  have hone_lt : 1 < coalition.card := by omega
  obtain ⟨first, hfirst, second, hsecond, hne⟩ :=
    Finset.one_lt_card.mp hone_lt
  have hpair : ({first, second} : Finset ι) ⊆ coalition := by
    intro player hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
    rcases hplayer with rfl | rfl
    · exact hfirst
    · exact hsecond
  have hinside :
      (∏ player ∈ coalition, root player) ≤ root first * root second := by
    have h := Finset.prod_le_prod_of_subset_of_le_one hpair
      (fun player _ => hroot_nonneg player)
      (fun player _ _ => hroot_le_one player)
    simpa [hne, mul_comm] using h
  have houtside_nonneg :
      0 ≤ ∏ player ∈ coalitionᶜ, (1 - root player) :=
    Finset.prod_nonneg fun player _ => sub_nonneg.mpr (hroot_le_one player)
  have houtside_le_one :
      (∏ player ∈ coalitionᶜ, (1 - root player)) ≤ 1 :=
    Finset.prod_le_one
      (fun player _ => sub_nonneg.mpr (hroot_le_one player))
      (fun player _ => by linarith [hroot_nonneg player])
  have hfirst_le := Math.PMFProduct.coordinate_le_one_sub_prod_one_sub
    root Finset.univ (fun player _ => hroot_nonneg player)
      (fun player _ => hroot_le_one player) (Finset.mem_univ first)
  have hsecond_le := Math.PMFProduct.coordinate_le_one_sub_prod_one_sub
    root Finset.univ (fun player _ => hroot_nonneg player)
      (fun player _ => hroot_le_one player) (Finset.mem_univ second)
  have habsorption_nonneg :
      0 ≤ 1 - Math.PMFProduct.continueMass root := by
    exact sub_nonneg.mpr
      (Math.PMFProduct.continueMass_le_one hroot_nonneg hroot_le_one)
  unfold Math.PMFProduct.coalitionMass
  calc
    (∏ player ∈ coalition, root player) *
        (∏ player ∈ coalitionᶜ, (1 - root player)) ≤
      (root first * root second) *
        (∏ player ∈ coalitionᶜ, (1 - root player)) :=
      mul_le_mul_of_nonneg_right hinside houtside_nonneg
    _ ≤ (root first * root second) * 1 := by
      exact mul_le_mul_of_nonneg_left houtside_le_one
        (mul_nonneg (hroot_nonneg first) (hroot_nonneg second))
    _ ≤ (1 - Math.PMFProduct.continueMass root) ^ 2 := by
      simp only [mul_one, Math.PMFProduct.continueMass]
      change root first * root second ≤
        (1 - ∏ player, (1 - root player)) ^ 2
      have hmul := mul_le_mul hfirst_le hsecond_le
        (hroot_nonneg second) habsorption_nonneg
      simpa [sq] using hmul

/-- The coordinatewise dimension constant printed in the published AKRS
small-cell lemma. -/
def akrsSmallCellCoordinateConstant (ι : Type) [Fintype ι] : ℝ :=
  ((2 ^ Fintype.card ι : ℕ) : ℝ)

/-- The numerical two-player witness behind the correction of the printed
`1 / k` collision factor at `k = 5`.  Its absorption probability is below
`1 / 5`, but its double-quit to first-player-only odds ratio is above
`1 / 5`. -/
theorem akrsPrintedCollisionFactor_five_counterexample :
    ∃ root : Bool → ℝ,
      (∀ player, 0 ≤ root player ∧ root player ≤ 1) ∧
        1 - Math.PMFProduct.continueMass root = 19081 / 100000 ∧
        1 - Math.PMFProduct.continueMass root < 1 / 5 ∧
        Math.PMFProduct.coalitionMass root Finset.univ /
            Math.PMFProduct.coalitionMass root {false} = 19 / 81 ∧
        1 / 5 < Math.PMFProduct.coalitionMass root Finset.univ /
          Math.PMFProduct.coalitionMass root {false} := by
  refine ⟨fun player ↦ if player then 19 / 100 else 1 / 1000, ?_⟩
  have hfalseComplement : ({false} : Finset Bool)ᶜ = {true} := by decide
  norm_num [Math.PMFProduct.continueMass, Math.PMFProduct.coalitionMass,
    Fintype.univ_bool, hfalseComplement]

private def akrsCollisionCoalitions (ι : Type) [Fintype ι] :
    Finset (Finset ι) :=
  Finset.univ.filter fun coalition : Finset ι => 2 ≤ coalition.card

omit [Nonempty ι] in
private def akrsExtendRoot (players : Finset ι)
    (root : players → ℝ) : ι → ℝ :=
  fun player => if hplayer : player ∈ players then root ⟨player, hplayer⟩ else 0

omit [Nonempty ι] in
private def akrsLiftCoalition (players : Finset ι)
    (coalition : Finset players) : Finset ι :=
  coalition.map (Function.Embedding.subtype fun player => player ∈ players)

omit [Fintype ι] [Nonempty ι] in
@[simp] private theorem akrsExtendRoot_apply_subtype
    (players : Finset ι) (root : players → ℝ) (player : players) :
    akrsExtendRoot players root player.1 = root player := by
  simp [akrsExtendRoot, player.2]

omit [Fintype ι] [Nonempty ι] in
private theorem akrsExtendRoot_apply_not_mem
    (players : Finset ι) (root : players → ℝ)
    {player : ι} (hplayer : player ∉ players) :
    akrsExtendRoot players root player = 0 := by
  simp [akrsExtendRoot, hplayer]

omit [Nonempty ι] in
private theorem akrsContinueMass_extend
    (players : Finset ι) (root : players → ℝ) :
    Math.PMFProduct.continueMass (akrsExtendRoot players root) =
      Math.PMFProduct.continueMass root := by
  unfold Math.PMFProduct.continueMass
  calc
    (∏ player, (1 - akrsExtendRoot players root player)) =
        ∏ player ∈ players, (1 - akrsExtendRoot players root player) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ players)
      intro player _ hplayer
      rw [akrsExtendRoot_apply_not_mem players root hplayer]
      simp
    _ = ∏ player : players, (1 - root player) := by
      rw [Finset.prod_subtype players (fun _ => Iff.rfl)]
      apply Finset.prod_congr rfl
      intro player hplayer
      simp [akrsExtendRoot]

omit [Nonempty ι] in
private theorem akrsCoalitionMass_extend_lift
    (players : Finset ι) (root : players → ℝ)
    (coalition : Finset players) :
    Math.PMFProduct.coalitionMass (akrsExtendRoot players root)
        (akrsLiftCoalition players coalition) =
      Math.PMFProduct.coalitionMass root coalition := by
  unfold Math.PMFProduct.coalitionMass
  unfold akrsLiftCoalition
  rw [Finset.prod_map]
  congr 1
  · apply Finset.prod_congr rfl
    intro player _
    exact akrsExtendRoot_apply_subtype players root player
  · let embedding :=
      Function.Embedding.subtype fun player => player ∈ players
    let activeComplement : Finset ι := coalitionᶜ.map embedding
    have hsubset : activeComplement ⊆
        (coalition.map embedding)ᶜ := by
      intro player hplayer
      simp only [activeComplement, Finset.mem_map, Finset.mem_compl]
        at hplayer ⊢
      obtain ⟨principal, hprincipal, rfl⟩ := hplayer
      intro hinside
      obtain ⟨other, hother, heq⟩ := hinside
      have heq' : other = principal := Subtype.ext heq
      subst other
      exact hprincipal hother
    have hoff : ∀ player ∈ (coalition.map embedding)ᶜ,
        player ∉ activeComplement →
          1 - akrsExtendRoot players root player = 1 := by
      intro player hcomplement hnot
      have houtside : player ∉ players := by
        intro hplayer
        apply hnot
        simp only [activeComplement, Finset.mem_map]
        refine ⟨⟨player, hplayer⟩, ?_, rfl⟩
        simp only [Finset.mem_compl]
        intro hcoalition
        have hnotMapped : player ∉ coalition.map embedding := by
          simpa only [Finset.mem_compl] using hcomplement
        exact hnotMapped (Finset.mem_map.mpr
          ⟨⟨player, hplayer⟩, hcoalition, rfl⟩)
      rw [akrsExtendRoot_apply_not_mem players root houtside]
      simp
    calc
      (∏ player ∈ (coalition.map embedding)ᶜ,
          (1 - akrsExtendRoot players root player)) =
          ∏ player ∈ activeComplement,
            (1 - akrsExtendRoot players root player) := by
        symm
        exact Finset.prod_subset hsubset hoff
      _ = ∏ player ∈ coalitionᶜ, (1 - root player) := by
        dsimp only [activeComplement]
        rw [Finset.prod_map]
        apply Finset.prod_congr rfl
        intro player _
        exact congrArg (fun value : ℝ => 1 - value)
          (akrsExtendRoot_apply_subtype players root player)

omit [Nonempty ι] in
private theorem akrsCoalitionMass_extend_eq_zero_of_not_subset
    (players : Finset ι) (root : players → ℝ)
    {coalition : Finset ι} (hcoalition : ¬coalition ⊆ players) :
    Math.PMFProduct.coalitionMass (akrsExtendRoot players root) coalition = 0 := by
  obtain ⟨player, hplayer, houtside⟩ := Set.not_subset.mp hcoalition
  unfold Math.PMFProduct.coalitionMass
  have hzero : ∏ member ∈ coalition,
      akrsExtendRoot players root member = 0 := by
    exact Finset.prod_eq_zero hplayer
      (akrsExtendRoot_apply_not_mem players root houtside)
  rw [hzero, zero_mul]

omit [Fintype ι] [Nonempty ι] in
private theorem akrsLiftCoalition_subtype
    (players : Finset ι) (coalition : Finset ι)
    (hcoalition : coalition ⊆ players) :
    akrsLiftCoalition players
        (coalition.subtype fun player => player ∈ players) = coalition := by
  exact Finset.subtype_map_of_mem hcoalition

omit [Nonempty ι] in
private theorem akrsLawSingletonMass_add_collisionMass
    (law : Finset ι → ℝ) (hlaw_sum : (∑ coalition, law coalition) = 1) :
    (∑ player, law {player}) +
        ∑ coalition ∈ akrsCollisionCoalitions ι, law coalition =
      1 - law ∅ := by
  let singles : Finset (Finset ι) :=
    Finset.univ.image fun player : ι => ({player} : Finset ι)
  let collisions : Finset (Finset ι) := akrsCollisionCoalitions ι
  have hdisjoint : Disjoint singles collisions := by
    rw [Finset.disjoint_left]
    intro coalition hsingle hcollision
    simp only [singles, Finset.mem_image, Finset.mem_univ, true_and] at hsingle
    obtain ⟨player, rfl⟩ := hsingle
    simp [collisions, akrsCollisionCoalitions] at hcollision
  have hpartition :
      Finset.univ.erase (∅ : Finset ι) = singles ∪ collisions := by
    ext coalition
    simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_union]
    constructor
    · intro hne
      have hpos : 0 < coalition.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hne.1)
      by_cases hone : coalition.card = 1
      · left
        obtain ⟨player, rfl⟩ := Finset.card_eq_one.mp hone
        simp [singles]
      · right
        simp only [collisions, akrsCollisionCoalitions,
          Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    · rintro (hsingle | hcollision)
      · simp only [singles, Finset.mem_image, Finset.mem_univ, true_and]
          at hsingle
        obtain ⟨player, rfl⟩ := hsingle
        simp
      · simp only [collisions, akrsCollisionCoalitions,
          Finset.mem_filter, Finset.mem_univ, true_and] at hcollision
        exact ⟨fun hempty => by simp [hempty] at hcollision, trivial⟩
  have hsingleSum :
      ∑ coalition ∈ singles, law coalition = ∑ player, law {player} := by
    rw [show singles = Finset.univ.image
        (fun player : ι => ({player} : Finset ι)) by rfl,
      Finset.sum_image]
    intro first _ second _ heq
    simpa using heq
  have htotal := Finset.sum_erase_add (s := Finset.univ)
    (f := law) (Finset.mem_univ (∅ : Finset ι))
  rw [hlaw_sum, hpartition, Finset.sum_union hdisjoint, hsingleSum] at htotal
  change (∑ player, law {player}) +
      ∑ coalition ∈ collisions, law coalition = 1 - law ∅
  linarith

omit [DecidableEq ι] [Nonempty ι] in
private theorem akrsCollisionSum_le
    {mass : Finset ι → ℝ} {scale : ℝ}
    (hscale : 0 ≤ scale)
    (hbound : ∀ coalition, 2 ≤ coalition.card → mass coalition ≤ scale) :
    (∑ coalition ∈ akrsCollisionCoalitions ι, mass coalition) ≤
      akrsSmallCellCoordinateConstant ι * scale := by
  let collisions := akrsCollisionCoalitions ι
  have hsum : (∑ coalition ∈ collisions, mass coalition) ≤
      (collisions.card : ℝ) * scale := by
    calc
      (∑ coalition ∈ collisions, mass coalition) ≤
          ∑ _coalition ∈ collisions, scale := by
        apply Finset.sum_le_sum
        intro coalition hcoalition
        exact hbound coalition (Finset.mem_filter.mp hcoalition).2
      _ = (collisions.card : ℝ) * scale := by simp
  have hcard : (collisions.card : ℝ) ≤
      akrsSmallCellCoordinateConstant ι := by
    have hnat : collisions.card ≤ Fintype.card (Finset ι) := by
      simpa using Finset.card_le_card (Finset.subset_univ collisions)
    rw [Fintype.card_finset] at hnat
    change (collisions.card : ℝ) ≤ ((2 ^ Fintype.card ι : ℕ) : ℝ)
    exact_mod_cast hnat
  simpa [collisions] using
    hsum.trans (mul_le_mul_of_nonneg_right hcard hscale)

/-- A product row realizing the conclusions needed from the AKRS small-cell
construction.  Relative singleton weights are stated by cross multiplication,
so zero singleton coordinates do not require a division convention. -/
structure SmallCellProductization
    (ε : ℝ) (law : Finset ι → ℝ) where
  root : ι → ℝ
  root_nonneg : ∀ player, 0 ≤ root player
  root_lt_one : ∀ player, root player < 1
  absorption_exact :
    1 - Math.PMFProduct.continueMass root = 1 - law ∅
  relative_singleton_weights : ∀ first second,
    Math.PMFProduct.coalitionMass root {first} * law {second} =
      Math.PMFProduct.coalitionMass root {second} * law {first}
  quit_pos_iff_singletonMass_pos : ∀ player,
    0 < root player ↔ 0 < law {player}
  coalition_coordinate_error : ∀ coalition, coalition.Nonempty →
    |Math.PMFProduct.coalitionMass root coalition - law coalition| ≤
      akrsSmallCellCoordinateConstant ι * ε * (1 - law ∅)

/-- Exact formal statement suggested by the printed AKRS small-cell lemma.

The existential threshold is the literal meaning of “sufficiently small” in
the source.  It is uniform over all probability laws on a fixed finite player
type, and is proved below with threshold `1 / 2`. -/
def AKRSSmallCellProductizationStatement (ι : Type)
    [Fintype ι] [DecidableEq ι] [Nonempty ι] : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ law : Finset ι → ℝ,
        (∀ coalition, 0 ≤ law coalition) →
        (∑ coalition, law coalition) = 1 →
        1 - law ∅ ≤ ε →
        (∀ coalition player, 2 ≤ coalition.card → player ∈ coalition →
          law coalition ≤ ε * law {player}) →
        Nonempty (SmallCellProductization ε law)

private theorem exists_akrsProductRoot_of_all_singletons_pos
    {ε : ℝ} {law : Finset ι → ℝ}
    (hεpos : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hp_pos : 0 < 1 - law ∅)
    (hp_le : 1 - law ∅ ≤ ε)
    (hsingleton_pos : ∀ player, 0 < law {player}) :
    ∃ root : ι → ℝ,
      (∀ player, 0 < root player ∧ root player < 1) ∧
      1 - Math.PMFProduct.continueMass root = 1 - law ∅ ∧
      ∀ first second,
        Math.PMFProduct.coalitionMass root {first} * law {second} =
          Math.PMFProduct.coalitionMass root {second} * law {first} := by
  classical
  let p : ℝ := 1 - law ∅
  let singleton : ι → ℝ := fun player => law {player}
  let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty singleton
  have hδpos : 0 < δ := by
    dsimp only [δ]
    rw [Finset.lt_inf'_iff]
    intro player _
    exact hsingleton_pos player
  have hδ_le (player : ι) : δ ≤ singleton player := by
    exact Finset.inf'_le singleton (Finset.mem_univ player)
  let ratio : (ι → ℝ) → ι → ℝ := fun root player =>
    Math.PMFProduct.coalitionMass root {player} / singleton player
  let average : (ι → ℝ) → ℝ := fun root =>
    (∑ player, ratio root player) / Fintype.card ι
  let imbalance : (ι → ℝ) → ι → ℝ := fun root player =>
    2 / δ * (p - (1 - Math.PMFProduct.continueMass root)) +
      (average root - ratio root player)
  let field : (ι → ℝ) → ι → ℝ := fun root player =>
    max (imbalance root player) 0 +
      root player * min (imbalance root player) 0
  have hratio (player : ι) : Continuous fun root : ι → ℝ => ratio root player := by
    dsimp only [ratio]
    exact (continuous_akrsCoalitionMass {player}).div_const _
  have haverage : Continuous average := by
    dsimp only [average]
    exact (continuous_finsetSum _ fun player _ => hratio player).div_const _
  have himbalance (player : ι) :
      Continuous fun root : ι → ℝ => imbalance root player := by
    dsimp only [imbalance]
    exact (continuous_const.mul
      (continuous_const.sub continuous_akrsAbsorptionMass)).add
        (haverage.sub (hratio player))
  have hfield : Continuous field := by
    exact continuous_pi fun player =>
      ((himbalance player).max continuous_const).add
        ((continuous_apply player).mul
          ((himbalance player).min continuous_const))
  have hlower : ∀ root ∈ Set.Icc (fun _ => 0) (fun _ => 1), ∀ player,
      root player = 0 → 0 ≤ field root player := by
    intro root _ player hroot
    dsimp only [field]
    rw [hroot, zero_mul, add_zero]
    exact le_max_right _ _
  have hupper : ∀ root ∈ Set.Icc (fun _ => 0) (fun _ => 1), ∀ player,
      root player = 1 → field root player ≤ 0 := by
    intro root hroot player hrootPlayer
    have hcontinue : Math.PMFProduct.continueMass root = 0 :=
      Math.PMFProduct.continueMass_eq_zero_of_eq_one hrootPlayer
    have hratio_nonneg (other : ι) : 0 ≤ ratio root other := by
      dsimp only [ratio]
      exact div_nonneg
        (Math.PMFProduct.coalitionMass_nonneg root hroot.1 hroot.2 {other})
        (hsingleton_pos other).le
    have hratio_le (other : ι) : ratio root other ≤ 1 / δ := by
      have hmass_le : Math.PMFProduct.coalitionMass root {other} ≤ 1 := by
        exact (Math.PMFProduct.coalitionMass_le_coordinate_of_mem
          root hroot.1 hroot.2 (by simp)).trans (hroot.2 other)
      dsimp only [ratio]
      apply (div_le_div_iff₀ (hsingleton_pos other) hδpos).2
      have hδ := hδ_le other
      dsimp only [singleton] at hδ
      nlinarith
    have haverage_le : average root ≤ 1 / δ := by
      dsimp only [average]
      have hcard_pos : (0 : ℝ) < Fintype.card ι := by
        exact_mod_cast Fintype.card_pos
      apply (div_le_iff₀ hcard_pos).2
      calc
        (∑ other, ratio root other) ≤ ∑ _other : ι, 1 / δ :=
          Finset.sum_le_sum fun other _ => hratio_le other
        _ = (Fintype.card ι : ℝ) * (1 / δ) := by simp
      simp [mul_comm]
    have himbalance_nonpos : imbalance root player ≤ 0 := by
      dsimp only [imbalance, p]
      rw [hcontinue]
      have hratio0 := hratio_nonneg player
      have hfirst : 2 / δ * ((1 - law ∅) - (1 - 0)) ≤ -(1 / δ) := by
        rw [show 2 / δ * ((1 - law ∅) - (1 - 0)) =
          (2 * ((1 - law ∅) - 1)) / δ by ring]
        rw [show -(1 / δ) = (-1) / δ by ring]
        apply (div_le_div_iff_of_pos_right hδpos).2
        nlinarith
      linarith
    dsimp only [field]
    rw [hrootPlayer, one_mul, max_add_min]
    simpa using himbalance_nonpos
  obtain ⟨root, hroot, hfield_zero⟩ :=
    Math.Topology.exists_cube_zero_of_opposite_face_signs
      field hfield hlower hupper
  have himbalance_nonpos (player : ι) : imbalance root player ≤ 0 := by
    by_contra hnot
    have hpos : 0 < imbalance root player := lt_of_not_ge hnot
    have hfield_pos : 0 < field root player := by
      dsimp only [field]
      rw [max_eq_left hpos.le, min_eq_right hpos.le]
      simpa using hpos
    exact hfield_pos.ne' (hfield_zero player)
  have habsorption_eq :
      1 - Math.PMFProduct.continueMass root = p := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with habsorption_lt | habsorption_gt
    · have hsumSecond :
          ∑ player, (average root - ratio root player) = 0 := by
        dsimp only [average]
        have hcard_pos : (0 : ℝ) < Fintype.card ι := by
          exact_mod_cast Fintype.card_pos
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
        ring
      have hexistsSecond : ∃ player, 0 ≤ average root - ratio root player := by
        by_contra hnone
        push Not at hnone
        have hsumNeg : ∑ player, (average root - ratio root player) < 0 :=
          Finset.sum_neg (fun player _ => hnone player) Finset.univ_nonempty
        linarith
      obtain ⟨player, hsecond⟩ := hexistsSecond
      have himbalance_pos : 0 < imbalance root player := by
        dsimp only [imbalance]
        have hfactor : 0 < 2 / δ := div_pos (by norm_num) hδpos
        nlinarith
      exact (not_le_of_gt himbalance_pos) (himbalance_nonpos player)
    · obtain ⟨maxPlayer, _, hmaxPlayer⟩ :=
        Finset.exists_mem_eq_sup' Finset.univ_nonempty (ratio root)
      have hratio_le_max (player : ι) :
          ratio root player ≤ ratio root maxPlayer := by
        exact (Finset.le_sup' (ratio root) (Finset.mem_univ player)).trans_eq
          hmaxPlayer
      have hratio_nonneg (player : ι) : 0 ≤ ratio root player := by
        dsimp only [ratio]
        exact div_nonneg
          (Math.PMFProduct.coalitionMass_nonneg root hroot.1 hroot.2 {player})
          (hsingleton_pos player).le
      have haverage_le_max : average root ≤ ratio root maxPlayer := by
        dsimp only [average]
        have hcard_pos : (0 : ℝ) < Fintype.card ι := by
          exact_mod_cast Fintype.card_pos
        apply (div_le_iff₀ hcard_pos).2
        calc
          (∑ player, ratio root player) ≤
              ∑ _player : ι, ratio root maxPlayer :=
            Finset.sum_le_sum fun player _ => hratio_le_max player
          _ = (Fintype.card ι : ℝ) * ratio root maxPlayer := by simp
        simp [mul_comm]
      have hexists_root_pos : ∃ player, 0 < root player := by
        by_contra hnone
        push Not at hnone
        have hroot_zero : root = fun _ => 0 := by
          funext player
          exact le_antisymm (hnone player) (hroot.1 player)
        subst root
        simp [Math.PMFProduct.continueMass, p] at habsorption_gt hp_pos
        linarith
      obtain ⟨positivePlayer, hpositivePlayer⟩ := hexists_root_pos
      obtain ⟨selected, hselected_pos, hselected_max⟩ :
          ∃ selected, 0 < root selected ∧
            ratio root selected = ratio root maxPlayer := by
        by_cases hmax_pos : 0 < root maxPlayer
        · exact ⟨maxPlayer, hmax_pos, rfl⟩
        · have hmax_zero : root maxPlayer = 0 :=
            le_antisymm (le_of_not_gt hmax_pos) (hroot.1 maxPlayer)
          have hmaxRatio_zero : ratio root maxPlayer = 0 := by
            dsimp only [ratio]
            rw [Math.PMFProduct.coalitionMass_singleton, hmax_zero,
              zero_mul, zero_div]
          have hpositiveRatio_zero : ratio root positivePlayer = 0 := by
            apply le_antisymm
            · simpa [hmaxRatio_zero] using hratio_le_max positivePlayer
            · exact hratio_nonneg positivePlayer
          exact ⟨positivePlayer, hpositivePlayer,
            hpositiveRatio_zero.trans hmaxRatio_zero.symm⟩
      have hsecond_nonpos : average root - ratio root selected ≤ 0 := by
        rw [hselected_max]
        linarith
      have himbalance_neg : imbalance root selected < 0 := by
        dsimp only [imbalance]
        have hfactor : 0 < 2 / δ := div_pos (by norm_num) hδpos
        nlinarith
      have hfield_neg : field root selected < 0 := by
        dsimp only [field]
        rw [max_eq_right himbalance_neg.le,
          min_eq_left himbalance_neg.le, zero_add]
        exact mul_neg_of_pos_of_neg hselected_pos himbalance_neg
      exact hfield_neg.ne (hfield_zero selected)
  have hroot_lt_one (player : ι) : root player < 1 := by
    apply lt_of_le_of_ne (hroot.2 player)
    intro hone
    have hcontinue : Math.PMFProduct.continueMass root = 0 :=
      Math.PMFProduct.continueMass_eq_zero_of_eq_one hone
    have hp_half : p ≤ 1 / 2 := hp_le.trans hεhalf
    rw [hcontinue] at habsorption_eq
    nlinarith
  have hexists_root_pos : ∃ player, 0 < root player := by
    by_contra hnone
    push Not at hnone
    have hroot_zero : root = fun _ => 0 := by
      funext player
      exact le_antisymm (hnone player) (hroot.1 player)
    subst root
    simp [Math.PMFProduct.continueMass] at habsorption_eq
    linarith
  obtain ⟨positivePlayer, hpositivePlayer⟩ := hexists_root_pos
  have hratio_nonneg (player : ι) : 0 ≤ ratio root player := by
    dsimp only [ratio]
    exact div_nonneg
      (Math.PMFProduct.coalitionMass_nonneg root hroot.1 hroot.2 {player})
      (hsingleton_pos player).le
  have hpositiveRatio : 0 < ratio root positivePlayer := by
    have hsingletonMass :
        0 < Math.PMFProduct.coalitionMass root {positivePlayer} := by
      rw [Math.PMFProduct.coalitionMass_singleton]
      exact mul_pos hpositivePlayer
        (Finset.prod_pos fun other _ => sub_pos.mpr (hroot_lt_one other))
    exact div_pos hsingletonMass (hsingleton_pos positivePlayer)
  have haverage_pos : 0 < average root := by
    dsimp only [average]
    have hsum_pos : 0 < ∑ player, ratio root player :=
      Finset.sum_pos' (fun player _ => hratio_nonneg player)
        ⟨positivePlayer, Finset.mem_univ positivePlayer, hpositiveRatio⟩
    exact div_pos hsum_pos (by exact_mod_cast Fintype.card_pos)
  have hroot_pos (player : ι) : 0 < root player := by
    by_contra hnot
    have hroot_zero : root player = 0 :=
      le_antisymm (le_of_not_gt hnot) (hroot.1 player)
    have hratio_zero : ratio root player = 0 := by
      dsimp only [ratio]
      rw [Math.PMFProduct.coalitionMass_singleton, hroot_zero,
        zero_mul, zero_div]
    have himbalance_pos : 0 < imbalance root player := by
      dsimp only [imbalance]
      rw [habsorption_eq, sub_self, mul_zero, zero_add, hratio_zero, sub_zero]
      exact haverage_pos
    exact (not_le_of_gt himbalance_pos) (himbalance_nonpos player)
  have himbalance_zero (player : ι) : imbalance root player = 0 := by
    have hnonpos := himbalance_nonpos player
    have hfield := hfield_zero player
    dsimp only [field] at hfield
    rw [max_eq_right hnonpos, min_eq_left hnonpos, zero_add] at hfield
    exact (mul_eq_zero.mp hfield).resolve_left (ne_of_gt (hroot_pos player))
  refine ⟨root, fun player => ⟨hroot_pos player, hroot_lt_one player⟩,
    habsorption_eq.trans rfl, ?_⟩
  intro first second
  have hratio_eq : ratio root first = ratio root second := by
    have hfirst := himbalance_zero first
    have hsecond := himbalance_zero second
    dsimp only [imbalance] at hfirst hsecond
    rw [habsorption_eq, sub_self, mul_zero, zero_add] at hfirst hsecond
    linarith
  dsimp only [ratio, singleton] at hratio_eq
  apply (div_eq_div_iff (ne_of_gt (hsingleton_pos first))
    (ne_of_gt (hsingleton_pos second))).mp at hratio_eq
  simpa [mul_comm] using hratio_eq

/-! The published proof first treats the case in which every singleton atom
is positive.  The next theorem packages that case, including the printed
coordinate estimate.  The weak inequality is intentional: unlike the strict
inequality printed in AKRS, Lemma 4.9, it remains meaningful when the total
absorption probability is zero. -/

private theorem akrsProductization_of_all_singletons_pos
    {ε : ℝ} {law : Finset ι → ℝ}
    (hεpos : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hlaw_nonneg : ∀ coalition, 0 ≤ law coalition)
    (hlaw_sum : (∑ coalition, law coalition) = 1)
    (hp_pos : 0 < 1 - law ∅)
    (hp_le : 1 - law ∅ ≤ ε)
    (hcollision : ∀ coalition player, 2 ≤ coalition.card →
      player ∈ coalition → law coalition ≤ ε * law {player})
    (hsingleton_pos : ∀ player, 0 < law {player}) :
    Nonempty (SmallCellProductization ε law) := by
  classical
  obtain ⟨root, hroot, habsorption, hrelative⟩ :=
    exists_akrsProductRoot_of_all_singletons_pos
      hεpos hεhalf hp_pos hp_le hsingleton_pos
  have hroot_nonneg (player : ι) : 0 ≤ root player := (hroot player).1.le
  have hroot_le_one (player : ι) : root player ≤ 1 := (hroot player).2.le
  let scale : ℝ := ε * (1 - law ∅)
  let bound : ℝ := akrsSmallCellCoordinateConstant ι * scale
  have hscale_nonneg : 0 ≤ scale :=
    mul_nonneg hεpos.le hp_pos.le
  have hconstant_nonneg : 0 ≤ akrsSmallCellCoordinateConstant ι := by
    unfold akrsSmallCellCoordinateConstant
    exact_mod_cast (Nat.zero_le (2 ^ Fintype.card ι))
  have hbound_nonneg : 0 ≤ bound :=
    mul_nonneg hconstant_nonneg hscale_nonneg
  have hrootCollisionAtom_le (coalition : Finset ι)
      (hcard : 2 ≤ coalition.card) :
      Math.PMFProduct.coalitionMass root coalition ≤ scale := by
    have hsq := akrsCoalitionMass_le_absorption_sq
      hroot_nonneg hroot_le_one hcard
    rw [habsorption] at hsq
    dsimp only [scale]
    nlinarith
  have hlawCollisionAtom_le (coalition : Finset ι)
      (hcard : 2 ≤ coalition.card) : law coalition ≤ scale := by
    have hnonempty : coalition.Nonempty := by
      exact Finset.card_pos.mp (by omega)
    obtain ⟨player, hplayer⟩ := hnonempty
    have hlocal := hcollision coalition player hcard hplayer
    have hsingleton_le := akrsLawMass_le_absorption_of_nonempty
      hlaw_nonneg hlaw_sum (coalition := ({player} : Finset ι)) (by simp)
    dsimp only [scale]
    nlinarith
  have hrootCollision_le : Math.PMFProduct.collisionMass root ≤ bound := by
    unfold Math.PMFProduct.collisionMass
    exact akrsCollisionSum_le hscale_nonneg hrootCollisionAtom_le
  have hlawCollision_le :
      (∑ coalition ∈ akrsCollisionCoalitions ι, law coalition) ≤ bound :=
    akrsCollisionSum_le hscale_nonneg hlawCollisionAtom_le
  have hrootCollision_nonneg :
      0 ≤ Math.PMFProduct.collisionMass root :=
    Math.PMFProduct.collisionMass_nonneg root hroot_nonneg hroot_le_one
  have hlawCollision_nonneg :
      0 ≤ ∑ coalition ∈ akrsCollisionCoalitions ι, law coalition :=
    Finset.sum_nonneg fun coalition _ => hlaw_nonneg coalition
  have hrootSplit := Math.PMFProduct.singletonMass_add_collisionMass root
  have hlawSplit := akrsLawSingletonMass_add_collisionMass law hlaw_sum
  have hsingletonDifference :
      Math.PMFProduct.singletonMass root - (∑ player, law {player}) =
        (∑ coalition ∈ akrsCollisionCoalitions ι, law coalition) -
          Math.PMFProduct.collisionMass root := by
    rw [habsorption] at hrootSplit
    linarith
  have hsingletonTotal_error :
      |Math.PMFProduct.singletonMass root - (∑ player, law {player})| ≤
        bound := by
    rw [hsingletonDifference, abs_le]
    constructor <;> linarith
  have hsingletonCoordinate_error (player : ι) :
      |Math.PMFProduct.coalitionMass root {player} - law {player}| ≤ bound := by
    let anchor : ι := Classical.choice (inferInstance : Nonempty ι)
    by_cases hanchor :
        Math.PMFProduct.coalitionMass root {anchor} ≤ law {anchor}
    · have hall (other : ι) :
          Math.PMFProduct.coalitionMass root {other} ≤ law {other} := by
        apply le_of_mul_le_mul_right _ (hsingleton_pos anchor)
        rw [hrelative other anchor]
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_right hanchor (hsingleton_pos other).le
      have hterm_nonneg (other : ι) :
          0 ≤ law {other} - Math.PMFProduct.coalitionMass root {other} :=
        sub_nonneg.mpr (hall other)
      have hsingle_le_sum :
          law {player} - Math.PMFProduct.coalitionMass root {player} ≤
            ∑ other, (law {other} -
              Math.PMFProduct.coalitionMass root {other}) :=
        Finset.single_le_sum (fun other _ => hterm_nonneg other)
          (Finset.mem_univ player)
      have hsum_order : Math.PMFProduct.singletonMass root ≤
          ∑ other, law {other} := by
        unfold Math.PMFProduct.singletonMass
        exact Finset.sum_le_sum fun other _ => hall other
      rw [abs_of_nonpos (sub_nonpos.mpr (hall player))]
      rw [neg_sub]
      calc
        law {player} - Math.PMFProduct.coalitionMass root {player} ≤
            (∑ other, law {other}) - Math.PMFProduct.singletonMass root := by
          simpa [Math.PMFProduct.singletonMass, Finset.sum_sub_distrib]
            using hsingle_le_sum
        _ = |Math.PMFProduct.singletonMass root -
            (∑ other, law {other})| := by
          rw [abs_of_nonpos (sub_nonpos.mpr hsum_order)]
          ring
        _ ≤ bound := hsingletonTotal_error
    · have hanchor' : law {anchor} ≤
          Math.PMFProduct.coalitionMass root {anchor} :=
        le_of_lt (lt_of_not_ge hanchor)
      have hall (other : ι) : law {other} ≤
          Math.PMFProduct.coalitionMass root {other} := by
        apply le_of_mul_le_mul_right _ (hsingleton_pos anchor)
        rw [hrelative other anchor]
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_right hanchor' (hlaw_nonneg {other})
      have hterm_nonneg (other : ι) :
          0 ≤ Math.PMFProduct.coalitionMass root {other} - law {other} :=
        sub_nonneg.mpr (hall other)
      have hsingle_le_sum :
          Math.PMFProduct.coalitionMass root {player} - law {player} ≤
            ∑ other, (Math.PMFProduct.coalitionMass root {other} -
              law {other}) :=
        Finset.single_le_sum (fun other _ => hterm_nonneg other)
          (Finset.mem_univ player)
      have hsum_order : (∑ other, law {other}) ≤
          Math.PMFProduct.singletonMass root := by
        unfold Math.PMFProduct.singletonMass
        exact Finset.sum_le_sum fun other _ => hall other
      rw [abs_of_nonneg (sub_nonneg.mpr (hall player))]
      calc
        Math.PMFProduct.coalitionMass root {player} - law {player} ≤
            Math.PMFProduct.singletonMass root - (∑ other, law {other}) := by
          simpa [Math.PMFProduct.singletonMass, Finset.sum_sub_distrib]
            using hsingle_le_sum
        _ = |Math.PMFProduct.singletonMass root -
            (∑ other, law {other})| := by
          rw [abs_of_nonneg (sub_nonneg.mpr hsum_order)]
        _ ≤ bound := hsingletonTotal_error
  have htwo_le_constant : (2 : ℝ) ≤ akrsSmallCellCoordinateConstant ι := by
    have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
    have hpow : 2 ^ 1 ≤ 2 ^ Fintype.card ι :=
      Nat.pow_le_pow_right (by norm_num) hcard
    unfold akrsSmallCellCoordinateConstant
    norm_num at hpow ⊢
    exact_mod_cast hpow
  refine ⟨⟨root, hroot_nonneg, fun player => (hroot player).2,
    habsorption, hrelative, ?_, ?_⟩⟩
  · intro player
    exact ⟨fun _ => hsingleton_pos player,
      fun _ => (hroot player).1⟩
  · intro coalition hcoalition
    by_cases hsingleton : coalition.card = 1
    · obtain ⟨player, rfl⟩ := Finset.card_eq_one.mp hsingleton
      simpa [bound, scale, mul_assoc] using hsingletonCoordinate_error player
    · have hcard : 2 ≤ coalition.card := by
        have hpos := Finset.card_pos.mpr hcoalition
        omega
      have hrootAtom_nonneg := Math.PMFProduct.coalitionMass_nonneg
        root hroot_nonneg hroot_le_one coalition
      have hlawAtom_nonneg := hlaw_nonneg coalition
      have hrootAtom_le := hrootCollisionAtom_le coalition hcard
      have hlawAtom_le := hlawCollisionAtom_le coalition hcard
      rw [abs_le]
      constructor
      · have htwoScale_le : 2 * scale ≤ bound :=
          mul_le_mul_of_nonneg_right htwo_le_constant hscale_nonneg
        linarith
      · have htwoScale_le : 2 * scale ≤ bound :=
          mul_le_mul_of_nonneg_right htwo_le_constant hscale_nonneg
        linarith

/-! AKRS dispatches zero singleton atoms by deleting their player
coordinates, applying the positive-singleton construction to the active
subtype, and extending the resulting product row by zero.  This is the
literal active-player reduction compressed into the opening sentence of the
published proof of Lemma 4.9. -/

private theorem akrsSmallCellProductization
    {ε : ℝ} {law : Finset ι → ℝ}
    (hεpos : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hlaw_nonneg : ∀ coalition, 0 ≤ law coalition)
    (hlaw_sum : (∑ coalition, law coalition) = 1)
    (hp_le : 1 - law ∅ ≤ ε)
    (hcollision : ∀ coalition player, 2 ≤ coalition.card →
      player ∈ coalition → law coalition ≤ ε * law {player}) :
    Nonempty (SmallCellProductization ε law) := by
  classical
  by_cases hp_zero : 1 - law ∅ = 0
  · let root : ι → ℝ := fun _ => 0
    have hlaw_zero (coalition : Finset ι) (hcoalition : coalition.Nonempty) :
        law coalition = 0 := by
      apply le_antisymm
      · have hle := akrsLawMass_le_absorption_of_nonempty
          hlaw_nonneg hlaw_sum hcoalition
        linarith
      · exact hlaw_nonneg coalition
    have hrootMass_zero (coalition : Finset ι)
        (hcoalition : coalition.Nonempty) :
        Math.PMFProduct.coalitionMass root coalition = 0 := by
      obtain ⟨player, hplayer⟩ := hcoalition
      unfold Math.PMFProduct.coalitionMass
      have hprod : ∏ member ∈ coalition, root member = 0 :=
        Finset.prod_eq_zero hplayer rfl
      rw [hprod, zero_mul]
    refine ⟨⟨root, fun _ => le_rfl, fun _ => by norm_num,
      ?_, ?_, ?_, ?_⟩⟩
    · simpa [root, Math.PMFProduct.continueMass] using hp_zero.symm
    · intro first second
      rw [hrootMass_zero {first} (by simp),
        hrootMass_zero {second} (by simp)]
      ring
    · intro player
      rw [hlaw_zero {player} (by simp)]
    · intro coalition hcoalition
      rw [hrootMass_zero coalition hcoalition,
        hlaw_zero coalition hcoalition, hp_zero]
      simp
  · have hp_pos : 0 < 1 - law ∅ := by
      have hp_nonneg := akrsLawMass_le_absorption_of_nonempty
        hlaw_nonneg hlaw_sum (coalition := ({Classical.choice
          (inferInstance : Nonempty ι)} : Finset ι)) (by simp)
      have hp_nonnegative : 0 ≤ 1 - law ∅ :=
        (hlaw_nonneg {Classical.choice
          (inferInstance : Nonempty ι)}).trans hp_nonneg
      exact lt_of_le_of_ne hp_nonnegative (Ne.symm hp_zero)
    let players : Finset ι :=
      Finset.univ.filter fun player => 0 < law {player}
    have hlawSingleton_zero_of_not_mem {player : ι}
        (hplayer : player ∉ players) : law {player} = 0 := by
      have hnotpos : ¬0 < law {player} := by
        simpa only [players, Finset.mem_filter, Finset.mem_univ, true_and]
          using hplayer
      exact le_antisymm (le_of_not_gt hnotpos) (hlaw_nonneg {player})
    have hlaw_zero_off (coalition : Finset ι)
        (hoff : ¬coalition ⊆ players) : law coalition = 0 := by
      obtain ⟨player, hplayer, hplayerOutside⟩ := Set.not_subset.mp hoff
      have hsingletonZero := hlawSingleton_zero_of_not_mem hplayerOutside
      by_cases hsingleton : coalition.card = 1
      · obtain ⟨only, rfl⟩ := Finset.card_eq_one.mp hsingleton
        have heq : player = only := by simpa using hplayer
        subst player
        exact hsingletonZero
      · have hcard : 2 ≤ coalition.card := by
          have hcard_pos : 0 < coalition.card :=
            Finset.card_pos.mpr ⟨player, hplayer⟩
          omega
        have hle := hcollision coalition player hcard hplayer
        rw [hsingletonZero, mul_zero] at hle
        exact le_antisymm hle (hlaw_nonneg coalition)
    have hplayers_nonempty : players.Nonempty := by
      by_contra hempty
      have hplayers_empty : players = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      have hsingletons_zero (player : ι) : law {player} = 0 := by
        apply hlawSingleton_zero_of_not_mem
        rw [hplayers_empty]
        simp
      have hcollisions_zero (coalition : Finset ι)
          (hcard : 2 ≤ coalition.card) : law coalition = 0 := by
        have hnonempty : coalition.Nonempty :=
          Finset.card_pos.mp (by omega)
        obtain ⟨player, hplayer⟩ := hnonempty
        have hle := hcollision coalition player hcard hplayer
        rw [hsingletons_zero player, mul_zero] at hle
        exact le_antisymm hle (hlaw_nonneg coalition)
      have hsplit := akrsLawSingletonMass_add_collisionMass law hlaw_sum
      rw [Finset.sum_eq_zero fun player _ => hsingletons_zero player,
        Finset.sum_eq_zero] at hsplit
      · linarith
      · intro coalition hcoalition
        exact hcollisions_zero coalition
          (Finset.mem_filter.mp hcoalition).2
    letI : Nonempty players := Finset.nonempty_coe_sort.mpr hplayers_nonempty
    let activeLaw : Finset players → ℝ := fun coalition =>
      law (akrsLiftCoalition players coalition)
    have hactiveLaw_nonneg (coalition : Finset players) :
        0 ≤ activeLaw coalition :=
      hlaw_nonneg (akrsLiftCoalition players coalition)
    let supportedCoalitions : Finset (Finset ι) :=
      Finset.univ.filter fun coalition => coalition ⊆ players
    have hsupportedSum :
        (∑ coalition ∈ supportedCoalitions, law coalition) = 1 := by
      calc
        (∑ coalition ∈ supportedCoalitions, law coalition) =
            ∑ coalition, law coalition := by
          apply Finset.sum_subset (Finset.subset_univ supportedCoalitions)
          intro coalition _ hcoalition
          apply hlaw_zero_off coalition
          simpa only [supportedCoalitions, Finset.mem_filter,
            Finset.mem_univ, true_and] using hcoalition
        _ = 1 := hlaw_sum
    have hactiveLaw_sum : (∑ coalition, activeLaw coalition) = 1 := by
      rw [← hsupportedSum]
      apply Finset.sum_bij (fun coalition _ =>
        akrsLiftCoalition players coalition)
      · intro coalition _
        simp only [supportedCoalitions, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro player hplayer
        obtain ⟨principal, _, rfl⟩ := Finset.mem_map.mp hplayer
        exact principal.2
      · intro first _ second _ heq
        exact Finset.map_injective
          (Function.Embedding.subtype fun player => player ∈ players) heq
      · intro coalition hcoalition
        have hsubset : coalition ⊆ players := by
          simpa only [supportedCoalitions, Finset.mem_filter,
            Finset.mem_univ, true_and] using hcoalition
        let principal := coalition.subtype fun player => player ∈ players
        refine ⟨principal, Finset.mem_univ principal, ?_⟩
        exact akrsLiftCoalition_subtype players coalition hsubset
      · intro coalition _
        rfl
    have hactiveEmpty : activeLaw ∅ = law ∅ := by
      rfl
    have hactive_p_pos : 0 < 1 - activeLaw ∅ := by
      simpa only [hactiveEmpty] using hp_pos
    have hactive_p_le : 1 - activeLaw ∅ ≤ ε := by
      simpa only [hactiveEmpty] using hp_le
    have hactiveSingleton_pos (player : players) :
        0 < activeLaw {player} := by
      change 0 < law {player.1}
      simpa only [players, Finset.mem_filter, Finset.mem_univ, true_and]
        using player.2
    have hactiveCollision (coalition : Finset players) (player : players)
        (hcard : 2 ≤ coalition.card) (hplayer : player ∈ coalition) :
        activeLaw coalition ≤ ε * activeLaw {player} := by
      apply hcollision (akrsLiftCoalition players coalition) player.1
      · simpa only [akrsLiftCoalition, Finset.card_map] using hcard
      · exact Finset.mem_map.mpr ⟨player, hplayer, rfl⟩
    obtain ⟨activePacket⟩ := akrsProductization_of_all_singletons_pos
      hεpos hεhalf hactiveLaw_nonneg hactiveLaw_sum hactive_p_pos
      hactive_p_le hactiveCollision hactiveSingleton_pos
    let root : ι → ℝ := akrsExtendRoot players activePacket.root
    have hroot_nonneg (player : ι) : 0 ≤ root player := by
      by_cases hplayer : player ∈ players
      · simpa only [root, akrsExtendRoot, hplayer, dite_true] using
          activePacket.root_nonneg ⟨player, hplayer⟩
      · simp [root, akrsExtendRoot, hplayer]
    have hroot_lt_one (player : ι) : root player < 1 := by
      by_cases hplayer : player ∈ players
      · simpa only [root, akrsExtendRoot, hplayer, dite_true] using
          activePacket.root_lt_one ⟨player, hplayer⟩
      · simp [root, akrsExtendRoot, hplayer]
    have hrootMass_zero_off (coalition : Finset ι)
        (hoff : ¬coalition ⊆ players) :
        Math.PMFProduct.coalitionMass root coalition = 0 := by
      exact akrsCoalitionMass_extend_eq_zero_of_not_subset
        players activePacket.root hoff
    have hrootMass_restrict (coalition : Finset ι)
        (hsubset : coalition ⊆ players) :
        Math.PMFProduct.coalitionMass root coalition =
          Math.PMFProduct.coalitionMass activePacket.root
            (coalition.subtype fun player => player ∈ players) := by
      let principal := coalition.subtype fun player => player ∈ players
      have htransport := akrsCoalitionMass_extend_lift
        players activePacket.root principal
      have hlift := akrsLiftCoalition_subtype players coalition hsubset
      rw [hlift] at htransport
      simpa only [root] using htransport
    have hconstant_le : akrsSmallCellCoordinateConstant players ≤
        akrsSmallCellCoordinateConstant ι := by
      unfold akrsSmallCellCoordinateConstant
      have hcard : Fintype.card players ≤ Fintype.card ι := by
        simpa using Finset.card_le_univ players
      have hpow : 2 ^ Fintype.card players ≤ 2 ^ Fintype.card ι :=
        Nat.pow_le_pow_right (by norm_num) hcard
      exact_mod_cast hpow
    refine ⟨⟨root, hroot_nonneg, hroot_lt_one, ?_, ?_, ?_, ?_⟩⟩
    · change 1 - Math.PMFProduct.continueMass
          (akrsExtendRoot players activePacket.root) = 1 - law ∅
      rw [akrsContinueMass_extend]
      simpa only [hactiveEmpty] using activePacket.absorption_exact
    · intro first second
      by_cases hfirst : first ∈ players
      · by_cases hsecond : second ∈ players
        · let principalFirst : players := ⟨first, hfirst⟩
          let principalSecond : players := ⟨second, hsecond⟩
          have hfirstCoalition : ({first} : Finset ι) ⊆ players := by
            simpa using hfirst
          have hsecondCoalition : ({second} : Finset ι) ⊆ players := by
            simpa using hsecond
          have hsubFirst : ({first} : Finset ι).subtype
              (fun player => player ∈ players) = {principalFirst} := by
            ext player
            simp only [Finset.mem_subtype, Finset.mem_singleton]
            constructor
            · exact fun heq => Subtype.ext heq
            · exact fun heq => congrArg Subtype.val heq
          have hsubSecond : ({second} : Finset ι).subtype
              (fun player => player ∈ players) = {principalSecond} := by
            ext player
            simp only [Finset.mem_subtype, Finset.mem_singleton]
            constructor
            · exact fun heq => Subtype.ext heq
            · exact fun heq => congrArg Subtype.val heq
          rw [hrootMass_restrict {first} hfirstCoalition,
            hrootMass_restrict {second} hsecondCoalition,
            hsubFirst, hsubSecond]
          have hrelativeActive := activePacket.relative_singleton_weights
            principalFirst principalSecond
          change Math.PMFProduct.coalitionMass activePacket.root
                {principalFirst} * law {second} =
              Math.PMFProduct.coalitionMass activePacket.root
                {principalSecond} * law {first} at hrelativeActive
          exact hrelativeActive
        · have hsecondLaw := hlawSingleton_zero_of_not_mem hsecond
          have hsecondRoot := hrootMass_zero_off {second} (by simpa using hsecond)
          rw [hsecondLaw, hsecondRoot]
          ring
      · have hfirstLaw := hlawSingleton_zero_of_not_mem hfirst
        have hfirstRoot := hrootMass_zero_off {first} (by simpa using hfirst)
        rw [hfirstLaw, hfirstRoot]
        ring
    · intro player
      by_cases hplayer : player ∈ players
      · let principal : players := ⟨player, hplayer⟩
        change 0 < akrsExtendRoot players activePacket.root player ↔
          0 < law {player}
        rw [akrsExtendRoot_apply_subtype players activePacket.root principal]
        have hactive := activePacket.quit_pos_iff_singletonMass_pos principal
        change 0 < activePacket.root principal ↔ 0 < law {player} at hactive
        exact hactive
      · change 0 < akrsExtendRoot players activePacket.root player ↔
          0 < law {player}
        rw [akrsExtendRoot_apply_not_mem players activePacket.root hplayer,
          hlawSingleton_zero_of_not_mem hplayer]
    · intro coalition hcoalition
      by_cases hsubset : coalition ⊆ players
      · let principal := coalition.subtype fun player => player ∈ players
        have hprincipal_nonempty : principal.Nonempty := by
          obtain ⟨player, hplayer⟩ := hcoalition
          exact ⟨⟨player, hsubset hplayer⟩, by simp [principal, hplayer]⟩
        have hactiveError := activePacket.coalition_coordinate_error
          principal hprincipal_nonempty
        have hlift := akrsLiftCoalition_subtype players coalition hsubset
        have hactiveLawPrincipal : activeLaw principal = law coalition := by
          change law (akrsLiftCoalition players principal) = law coalition
          rw [hlift]
        rw [hactiveLawPrincipal, hactiveEmpty] at hactiveError
        have hscale_nonneg : 0 ≤ ε * (1 - law ∅) :=
          mul_nonneg hεpos.le hp_pos.le
        have hbound_mono :
            akrsSmallCellCoordinateConstant players * ε * (1 - law ∅) ≤
              akrsSmallCellCoordinateConstant ι * ε * (1 - law ∅) := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right hconstant_le hscale_nonneg
        rw [hrootMass_restrict coalition hsubset]
        exact hactiveError.trans hbound_mono
      · rw [hrootMass_zero_off coalition hsubset,
          hlaw_zero_off coalition hsubset]
        simp only [sub_self, abs_zero]
        have hconstant_nonneg :
            0 ≤ akrsSmallCellCoordinateConstant ι := by
          unfold akrsSmallCellCoordinateConstant
          positivity
        exact mul_nonneg (mul_nonneg hconstant_nonneg hεpos.le) hp_pos.le

/-- Published AKRS small-cell productization, with the conservative weak
coordinate estimate that includes zero total absorption. -/
theorem exists_akrsSmallCellProductization
    {ε : ℝ} {law : Finset ι → ℝ}
    (hεpos : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hlaw_nonneg : ∀ coalition, 0 ≤ law coalition)
    (hlaw_sum : (∑ coalition, law coalition) = 1)
    (hp_le : 1 - law ∅ ≤ ε)
    (hcollision : ∀ coalition player, 2 ≤ coalition.card →
      player ∈ coalition → law coalition ≤ ε * law {player}) :
    Nonempty (SmallCellProductization ε law) :=
  akrsSmallCellProductization hεpos hεhalf hlaw_nonneg hlaw_sum
    hp_le hcollision

/-- The existential-threshold specification is satisfied with the uniform
threshold `1 / 2`. -/
theorem akrsSmallCellProductizationStatement :
    AKRSSmallCellProductizationStatement ι := by
  refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
  intro ε hεpos hεhalf law hlaw_nonneg hlaw_sum hp_le hcollision
  exact exists_akrsSmallCellProductization hεpos hεhalf hlaw_nonneg
    hlaw_sum hp_le hcollision

end GameTheory
