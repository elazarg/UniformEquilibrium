import Mathlib

/-!
# Equivariant transport of finite block words

This independent module formalizes the action-groupoid calculation in
the equivariant word-transport construction.

An external group acts on fully labelled edges and on the continuation fiber.
If every block map intertwines those actions, then every finite composite does
too.  Fixed points and equivariant acceptance checks therefore transport along
word orbits.  A stabilizer of a word fixes its unique periodic point.

No group structure is assumed on the block maps themselves.
-/

noncomputable section

namespace Research.EquivariantWordTransport

variable {Gamma Edge Fiber : Type}
  [Group Gamma] [MulAction Gamma Edge] [MulAction Gamma Fiber]

/-- Relabel every edge of a finite block word by the same group element. -/
def relabelWord (g : Gamma) (word : List Edge) : List Edge :=
  word.map fun edge => g • edge

@[simp] theorem relabelWord_one (word : List Edge) :
    relabelWord (1 : Gamma) word = word := by
  simp [relabelWord]

theorem relabelWord_mul (g h : Gamma) (word : List Edge) :
    relabelWord (g * h) word =
      relabelWord g (relabelWord h word) := by
  simp [relabelWord, mul_smul]

/-- Backward/continuation evaluation of a word: the tail is evaluated first,
then the head block acts on its result. -/
def evalWord (block : Edge → Fiber → Fiber) :
    List Edge → Fiber → Fiber
  | [], point => point
  | edge :: word, point => block edge (evalWord block word point)

/-- **Whole-word intertwining.**  One-block equivariance propagates through
every finite composite. -/
theorem evalWord_relabel
    (block : Edge → Fiber → Fiber)
    (blockEquivariant : ∀ (g : Gamma) (edge : Edge) (point : Fiber),
      block (g • edge) (g • point) = g • block edge point)
    (g : Gamma) (word : List Edge) (point : Fiber) :
    evalWord block (relabelWord g word) (g • point) =
      g • evalWord block word point := by
  induction word generalizing point with
  | nil => rfl
  | cons edge word inductionHypothesis =>
      simp only [relabelWord, List.map_cons, evalWord]
      change block (g • edge)
          (evalWord block (relabelWord g word) (g • point)) =
        g • block edge (evalWord block word point)
      rw [inductionHypothesis]
      exact blockEquivariant g edge (evalWord block word point)

/-- A point is periodic for the based finite block word. -/
def IsFixedWord (block : Edge → Fiber → Fiber)
    (word : List Edge) (point : Fiber) : Prop :=
  evalWord block word point = point

/-- Periodic points transport to relabelled words. -/
theorem isFixedWord_relabel
    (block : Edge → Fiber → Fiber)
    (blockEquivariant : ∀ (g : Gamma) (edge : Edge) (point : Fiber),
      block (g • edge) (g • point) = g • block edge point)
    (g : Gamma) (word : List Edge) (point : Fiber)
    (fixed : IsFixedWord block word point) :
    IsFixedWord block (relabelWord g word) (g • point) := by
  unfold IsFixedWord at fixed ⊢
  calc
    evalWord block (relabelWord g word) (g • point) =
        g • evalWord block word point :=
      evalWord_relabel block blockEquivariant g word point
    _ = g • point := congrArg (fun value => g • value) fixed

/-- If a group element stabilizes a word and the word has a unique fixed
point, then it fixes that periodic point. -/
theorem smul_eq_of_stabilizes_word_of_unique_fixedPoint
    (block : Edge → Fiber → Fiber)
    (blockEquivariant : ∀ (g : Gamma) (edge : Edge) (point : Fiber),
      block (g • edge) (g • point) = g • block edge point)
    (g : Gamma) (word : List Edge) (point : Fiber)
    (stabilizes : relabelWord g word = word)
    (fixed : IsFixedWord block word point)
    (unique : ∀ candidate, IsFixedWord block word candidate →
      candidate = point) :
    g • point = point := by
  apply unique
  have transported :=
    isFixedWord_relabel block blockEquivariant g word point fixed
  simpa only [stabilizes] using transported

/-- Fixed-point validation and any explicitly equivariant strategic
acceptance predicate transport together along the word orbit. -/
theorem fixed_and_accepted_relabel
    (block : Edge → Fiber → Fiber)
    (blockEquivariant : ∀ (g : Gamma) (edge : Edge) (point : Fiber),
      block (g • edge) (g • point) = g • block edge point)
    (Accept : List Edge → Fiber → Prop)
    (acceptEquivariant : ∀ (g : Gamma) (word : List Edge) (point : Fiber),
      Accept word point → Accept (relabelWord g word) (g • point))
    (g : Gamma) (word : List Edge) (point : Fiber)
    (fixed : IsFixedWord block word point)
    (accepted : Accept word point) :
    IsFixedWord block (relabelWord g word) (g • point) ∧
      Accept (relabelWord g word) (g • point) := by
  exact ⟨isFixedWord_relabel block blockEquivariant g word point fixed,
    acceptEquivariant g word point accepted⟩

end Research.EquivariantWordTransport
