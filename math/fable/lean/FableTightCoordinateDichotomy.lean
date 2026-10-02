/-
The tight-coordinate dichotomy at a unique-all-Continue cap.

Fix a quitting reward table and a continuation cap dominating every solo
quitting reward, and suppose the all-Continue root is the *only* exact root
Nash action against that cap.  Call a coordinate *tight* when its solo
quitting reward already equals its cap entry.

The first theorem here says a tight coordinate is never alone: whenever `i`
is tight, some other coordinate `k` is tight as well and strictly gains from
colliding with `i`, that is `0 < quittingCollisionMatrix reward k i`.  This
is a restatement, in the collision-matrix vocabulary, of the integrated
`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`
(`UniformEquilibrium/Quitting/Punishment/SingletonCapBindingCollision.lean`),
which already proves it in the cap-defect and collision-gain vocabulary --
and proves it *without* any reward bound.  The `hreward` bound below is
therefore vestigial: it is retained only because the requested statement
carries it, and the proof does not consume it.

The two corollaries are not in the repository.  If no ordered pair of
distinct tight coordinates has a positive collision entry, then no
coordinate is tight at all, so the singleton gap is strict everywhere and,
over a nonempty finite player set, uniformly positive.  The uniform gap is
the missing hypothesis of the neighborhood-propagation consumer.

Scratch `math/` lane; nothing imports this file.
-/
import UniformEquilibrium.Quitting.Root.FirstOrderProductFlow
import UniformEquilibrium.Quitting.Punishment.SingletonCapBindingCollision

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Collision matrix versus collision gain -/

omit [Fintype ι] in
/-- Off the diagonal the collision matrix entry `k, i` is exactly the gain
`k` makes by joining `i`'s solo exit.  The two definitions differ only in
the order in which the colliding pair is listed. -/
theorem fable_quittingCollisionMatrix_eq_singletonCollisionGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who owner : ι} (hne : who ≠ owner) :
    quittingCollisionMatrix reward who owner =
      quittingSingletonCollisionGain reward owner who := by
  have hpair : quittingPairTerminal who owner =
      (⟨{owner, who}, by simp⟩ : {S : Finset ι // S.Nonempty}) :=
    Subtype.ext (Finset.pair_comm who owner)
  rw [quittingCollisionMatrix, dif_neg hne, hpair]
  rfl

/-! ## The tight-coordinate dichotomy -/

/-- **Tight coordinates recruit tight eager joiners.**  If the cap dominates
every solo quitting reward and the all-Continue root is the unique exact root
Nash action against it, then every tight coordinate `i` has a *different*
tight coordinate `k` with a strictly positive collision entry against `i`.

The witness root -- the solo stationary row in which only `i` quits, at a
hazard low enough that no opponent wants to join -- and the contradiction
with uniqueness are supplied by
`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`. -/
theorem fable_uniqueAllContinueCapNash_tight_exists_tightEagerJoiner
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {M : ℝ}
    (hreward : ∀ S who, |reward S who| ≤ M)
    (cap : Payoff ι)
    (hdominate : ∀ who, reward (quittingSingletonTerminal who) who ≤ cap who)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root → root = quittingAllContinueRoot)
    (i : ι)
    (htight : reward (quittingSingletonTerminal i) i = cap i) :
    ∃ k, k ≠ i ∧ reward (quittingSingletonTerminal k) k = cap k ∧
      0 < quittingCollisionMatrix reward k i := by
  -- The reward bound is not needed; naming it here keeps the requested
  -- signature honest about being unused.
  have _hM : 0 ≤ M :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal i) i)
  have hdefect : quittingSingletonCapDefect reward cap i = 0 := by
    rw [quittingSingletonCapDefect, htight, sub_self]
  obtain ⟨k, hk, hzero, hgain⟩ :=
    exists_quittingSingletonCollisionGain_pos_of_unique_allContinue
      reward cap hdominate hunique i hdefect
  refine ⟨k, hk, ?_, ?_⟩
  · rw [quittingSingletonCapDefect] at hzero
    linarith
  · rw [fable_quittingCollisionMatrix_eq_singletonCollisionGain reward hk]
    exact hgain

/-- **No tight eager pair forces a strict singleton gap.**  With no ordered
pair of distinct tight coordinates carrying a positive collision entry, a
unique-all-Continue cap has no tight coordinate at all. -/
theorem fable_uniqueAllContinueCapNash_strict_singletonGap_of_noTightEagerPair
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {M : ℝ}
    (hreward : ∀ S who, |reward S who| ≤ M)
    (cap : Payoff ι)
    (hdominate : ∀ who, reward (quittingSingletonTerminal who) who ≤ cap who)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root → root = quittingAllContinueRoot)
    (hnopair : ∀ i k, k ≠ i →
      reward (quittingSingletonTerminal i) i = cap i →
      reward (quittingSingletonTerminal k) k = cap k →
      quittingCollisionMatrix reward k i ≤ 0) :
    ∀ who, reward (quittingSingletonTerminal who) who < cap who := by
  intro who
  rcases lt_or_eq_of_le (hdominate who) with hlt | heq
  · exact hlt
  · obtain ⟨k, hk, htightk, hpos⟩ :=
      fable_uniqueAllContinueCapNash_tight_exists_tightEagerJoiner
        hreward cap hdominate hunique who heq
    exact absurd (hnopair who k hk heq htightk) (not_le.mpr hpos)

/-- **A uniform singleton gap.**  Over a nonempty finite player set the
strict gaps of the previous corollary have a positive finite minimum.  This
is the hypothesis consumed by neighborhood propagation of the uniqueness
plateau. -/
theorem fable_uniqueAllContinueCapNash_exists_uniform_singletonGap_of_noTightEagerPair
    [Nonempty ι] {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {M : ℝ}
    (hreward : ∀ S who, |reward S who| ≤ M)
    (cap : Payoff ι)
    (hdominate : ∀ who, reward (quittingSingletonTerminal who) who ≤ cap who)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root → root = quittingAllContinueRoot)
    (hnopair : ∀ i k, k ≠ i →
      reward (quittingSingletonTerminal i) i = cap i →
      reward (quittingSingletonTerminal k) k = cap k →
      quittingCollisionMatrix reward k i ≤ 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ who, delta ≤ cap who - reward (quittingSingletonTerminal who) who := by
  have hstrict :=
    fable_uniqueAllContinueCapNash_strict_singletonGap_of_noTightEagerPair
      hreward cap hdominate hunique hnopair
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  refine ⟨Finset.univ.inf' hne
    (fun who => cap who - reward (quittingSingletonTerminal who) who), ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro k _
    linarith [hstrict k]
  · intro who
    exact Finset.inf'_le _ (Finset.mem_univ who)

end GameTheory
