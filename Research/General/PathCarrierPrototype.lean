/-
Prototype: does an initial-state + (action, resulting-state) history carrier
make fixed-length prefix recovery unconditional?

Question under test.  The production carrier is

  Hist t = (Fin t → State × JointAct) × State

which stores the current state separately from the stage records, so
`appendHist` discards the base's current state and `Hist.StartsAt` must be
threaded through the dispatcher lemmas to recover it.

The alternative is

  Path t = State × (Fin t → JointAct × State)

an initial state followed by `t` (action, resulting state) pairs.  Claims to
check, in order of importance:

  (1) prefix recovery of the base from an append needs NO boundary hypothesis;
  (2) consecutive-stage continuity is structural, not propositional;
  (3) a boundary predicate is still required for semantic composition;
  (4) how much index transport (casts / HEq) this costs.

Run: lake env lean experiments/PathCarrierPrototype.lean
-/
import Mathlib


namespace PathCarrierPrototype

variable {S A : Type}

/-- Initial state followed by `t` `(action, resulting state)` pairs. -/
abbrev Path (S A : Type) (t : ℕ) : Type := S × (Fin t → A × S)

/-- The production carrier, for comparison throughout. -/
abbrev Hist (S A : Type) (t : ℕ) : Type := (Fin t → S × A) × S

/-- The state occupied at position `i`; position `0` is the initial state and
position `i+1` is the state resulting from stage `i`.

This is where claim (2) is settled: there is exactly one state per position,
so the source state of stage `i+1` *is* the result state of stage `i` by
construction.  No chaining hypothesis can be stated, because none is
expressible. -/
def stateAt {t : ℕ} (h : Path S A t) : Fin (t + 1) → S
  | ⟨0, _⟩ => h.1
  | ⟨j + 1, hj⟩ => (h.2 ⟨j, Nat.lt_of_succ_lt_succ hj⟩).2

/-- The current state: the state at the last position. -/
def current {t : ℕ} (h : Path S A t) : S := stateAt h (Fin.last t)

@[simp] theorem current_zero (h : Path S A 0) : current h = h.1 := rfl

/-- Concatenation keeps the base's initial state and both pair blocks.  The
suffix's *initial* state is what gets dropped -- that is the boundary datum. -/
def append {m n : ℕ} (base : Path S A m) (suffix : Path S A n) :
    Path S A (m + n) :=
  (base.1, Fin.append base.2 suffix.2)

/-- The fixed-length prefix of a path. -/
def take {t : ℕ} (h : Path S A t) (k : Fin (t + 1)) : Path S A k :=
  (h.1, fun i => h.2 (Fin.castLE (Nat.lt_succ_iff.mp k.isLt) i))

/-! ## Claim (1): unconditional base recovery -/

/-- **The decisive lemma.**  The base is recovered from an append with no
boundary hypothesis whatsoever.  Under the production carrier the
corresponding statement (`terminalPrefix_appendHist`) needs
`suffix.StartsAt base.2`. -/
theorem take_append_left {m n : ℕ}
    (base : Path S A m) (suffix : Path S A n) :
    take (append base suffix) ⟨m, by omega⟩ = base := by
  refine Prod.ext rfl ?_
  funext i
  change Fin.append base.2 suffix.2 (Fin.castLE _ i) = base.2 i
  rw [show (Fin.castLE (by omega : m ≤ m + n) i) = Fin.castAdd n i from rfl]
  exact Fin.append_left base.2 suffix.2 i

/-- Consequently `append` is injective in its base, again unconditionally.
This is what gives fixed-depth branch-cone disjointness. -/
theorem append_left_injective {m n : ℕ}
    (base base' : Path S A m) (suffix suffix' : Path S A n)
    (h : append base suffix = append base' suffix') :
    base = base' := by
  have := congrArg (fun p => take p ⟨m, by omega⟩) h
  simpa only [take_append_left] using this

/-! ## Claim (3): a boundary predicate survives -/

/-- The boundary datum that `append` drops. -/
def BoundaryCompatible {m n : ℕ}
    (base : Path S A m) (suffix : Path S A n) : Prop :=
  suffix.1 = current base

/-- With a nonempty suffix the current state of an append is the suffix's,
with no boundary hypothesis. -/
theorem current_append_of_succ {m n : ℕ}
    (base : Path S A m) (suffix : Path S A (n + 1)) :
    current (append base suffix) = current suffix := by
  change stateAt (append base suffix) (Fin.last (m + (n + 1))) =
    stateAt suffix (Fin.last (n + 1))
  change (Fin.append base.2 suffix.2 ⟨m + n, by omega⟩).2 = (suffix.2 ⟨n, by omega⟩).2
  congr 1
  rw [show (⟨m + n, by omega⟩ : Fin (m + (n + 1))) = Fin.natAdd m ⟨n, by omega⟩ from rfl]
  exact Fin.append_right base.2 suffix.2 ⟨n, by omega⟩

/-- With an *empty* suffix the current state of an append is the base's, so
`current (append base suffix) = current suffix` genuinely requires the
boundary equation.  Claim (3) confirmed: composition semantics still needs a
predicate, even though recovery no longer does. -/
theorem current_append_zero {m : ℕ}
    (base : Path S A m) (suffix : Path S A 0) :
    current (append base suffix) = current base := by
  cases m with
  | zero => rfl
  | succ k =>
      change (Fin.append base.2 suffix.2 ⟨k, by omega⟩).2 = (base.2 ⟨k, by omega⟩).2
      congr 1
      rw [show (⟨k, by omega⟩ : Fin (k + 1 + 0)) = Fin.castAdd 0 ⟨k, by omega⟩ from rfl]
      exact Fin.append_left base.2 suffix.2 ⟨k, by omega⟩

theorem current_append_zero_eq_suffix {m : ℕ}
    (base : Path S A m) (suffix : Path S A 0)
    (hb : BoundaryCompatible base suffix) :
    current (append base suffix) = current suffix := by
  rw [current_append_zero, current_zero]
  exact hb.symm

/-! ## The dual side: what the candidate *loses*

The production `appendHist` drops the base's terminal state; this candidate
drops the suffix's initial state.  They are two copies of one seam datum, so
the candidate does not remove a boundary predicate -- it moves it from the
prefix side to the suffix side.  Production has `terminalSuffix_appendHist`
and `appendHist_injective` unconditionally; the candidate cannot. -/

/-- `append base` is **not** injective in its suffix: two suffixes differing
only in their (dropped) initial state give the same append.  Production's
`appendHist_injective` is unconditional and load-bearing for
`histDistAfter_apply_appendHist`, so this is a real loss. -/
theorem append_not_injective_in_suffix :
    ∃ (base s₁ s₂ : Path Bool Unit 0),
      s₁ ≠ s₂ ∧ append base s₁ = append base s₂ := by
  refine ⟨(true, Fin.elim0), (true, Fin.elim0), (false, Fin.elim0), ?_, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (by simp)
  · exact Prod.ext rfl (funext fun i => i.elim0)

/-! ## The split-role design

Histories stay rooted; continuations become *unrooted* -- `n` pairs whose
start state is supplied by context.  Then nothing is dropped at the seam,
because the continuation never carries a competing copy of it. -/

/-- An unrooted continuation: `n` `(action, resulting state)` pairs. -/
abbrev Cont (S A : Type) (n : ℕ) : Type := Fin n → A × S

/-- States along a continuation launched from `start`. -/
def contStateAt {n : ℕ} (start : S) (c : Cont S A n) : Fin (n + 1) → S
  | ⟨0, _⟩ => start
  | ⟨j + 1, hj⟩ => (c ⟨j, Nat.lt_of_succ_lt_succ hj⟩).2

/-- Appending a continuation to a history.  The base's terminal state becomes
the source state of the continuation's first stage, so **no state is
discarded**. -/
def appendCont {m n : ℕ} (base : Hist S A m) (c : Cont S A n) :
    Hist S A (m + n) :=
  (Fin.append base.1
      (fun i => (contStateAt base.2 c i.castSucc, (c i).1)),
    contStateAt base.2 c (Fin.last n))

/-- Base-record recovery, unconditional. -/
theorem histTake_appendCont {m n : ℕ} (base : Hist S A m) (c : Cont S A n)
    (i : Fin m) : (appendCont base c).1 (Fin.castAdd n i) = base.1 i := by
  change Fin.append base.1
      (fun j => (contStateAt base.2 c j.castSucc, (c j).1))
      (Fin.castAdd n i) = base.1 i
  rw [Fin.append_left]

/-- **The seam state is not lost.**  Where production's `appendHist` discards
`base.2`, here it is recorded as the source state of the first appended
stage.  This is why no boundary predicate is needed. -/
theorem baseState_appendCont {m n : ℕ} (base : Hist S A m) (c : Cont S A (n + 1)) :
    ((appendCont base c).1 (Fin.natAdd m ⟨0, by omega⟩)).1 = base.2 := by
  change (Fin.append base.1
      (fun j => (contStateAt base.2 c j.castSucc, (c j).1))
      (Fin.natAdd m ⟨0, by omega⟩)).1 = base.2
  rw [Fin.append_right]
  rfl

/-- Continuation recovery, also unconditional: both the action and the
resulting state of every appended stage are read back exactly. -/
theorem contRecover_appendCont {m n : ℕ} (base : Hist S A m) (c : Cont S A n)
    (i : Fin n) :
    ((appendCont base c).1 (Fin.natAdd m i)).2 = (c i).1 := by
  change (Fin.append base.1 _ (Fin.natAdd m i)).2 = (c i).1
  rw [Fin.append_right]

/-- The resulting state of a *non-final* appended stage is read back from the
next record entry. -/
theorem contState_of_lt {m n : ℕ} (base : Hist S A m) (c : Cont S A n)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    ((appendCont base c).1 (Fin.natAdd m ⟨(i : ℕ) + 1, hi⟩)).1 = (c i).2 := by
  change (Fin.append base.1
      (fun j => (contStateAt base.2 c j.castSucc, (c j).1))
      (Fin.natAdd m ⟨(i : ℕ) + 1, hi⟩)).1 = _
  rw [Fin.append_right]
  rfl

/-- The resulting state of the *final* appended stage is the append's own
current state. -/
theorem contState_last {m n : ℕ} (base : Hist S A m) (c : Cont S A (n + 1)) :
    (appendCont base c).2 = (c (Fin.last n)).2 := rfl

/-- Hence `appendCont base` **is** injective in its continuation, with no
boundary hypothesis -- the property the prototyped `Path` design loses. -/
theorem appendCont_injective {m n : ℕ} (base : Hist S A m) :
    Function.Injective (appendCont base : Cont S A n → Hist S A (m + n)) := by
  intro c₁ c₂ heq
  funext i
  refine Prod.ext ?_ ?_
  · rw [← contRecover_appendCont base c₁ i, ← contRecover_appendCont base c₂ i,
      heq]
  · by_cases hi : (i : ℕ) + 1 < n
    · rw [← contState_of_lt base c₁ i hi, ← contState_of_lt base c₂ i hi, heq]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hlast : i = Fin.last k := by
        refine Fin.ext ?_
        have := i.isLt
        simp only [Fin.val_last]
        omega
      subst hlast
      rw [← contState_last base c₁, ← contState_last base c₂, heq]

/-! ## Translation to the production carrier -/

/-- Every `Path` denotes a `Hist`: stage `i` was visited at `stateAt i` and
played action `i`.  The image consists exactly of the chained histories, so
the new carrier is the well-formed part of the old one. -/
def toHist {t : ℕ} (h : Path S A t) : Hist S A t :=
  (fun i => (stateAt h i.castSucc, (h.2 i).1), current h)

/-- The production `StartsAt`, for comparison. -/
def Hist.StartsAt (state : S) {t : ℕ} (h : Hist S A t) : Prop :=
  match t with
  | 0 => h.2 = state
  | _ + 1 => (h.1 0).1 = state

/-- A denoted path always starts where its initial state says, so `StartsAt`
is not an extra obligation on the new carrier -- it is a theorem. -/
theorem startsAt_toHist {t : ℕ} (h : Path S A t) :
    Hist.StartsAt h.1 (toHist h) := by
  cases t with
  | zero => rfl
  | succ n => rfl

/-! ## Are the two carriers isomorphic?

The design record claimed the image of `toHist` is "exactly the chained
histories", i.e. that `Path` is the well-formed part of `Hist`.  That is
false: `Hist t` stores `t+1` states and `t` actions, exactly as `Path t`
does, and no state appears twice, so there is no chaining condition a `Hist`
could violate.  `toHist` is a bijection.  Constructing its inverse settles
it. -/

/-- State at position `k` of a production history. -/
def histStateAt {t : ℕ} (h : Hist S A t) : Fin (t + 1) → S :=
  fun k => if hlt : (k : ℕ) < t then (h.1 ⟨k, hlt⟩).1 else h.2

/-- The inverse of `toHist`. -/
def ofHist {t : ℕ} (h : Hist S A t) : Path S A t :=
  (histStateAt h ⟨0, by omega⟩, fun i => ((h.1 i).2, histStateAt h i.succ))

theorem stateAt_ofHist {t : ℕ} (h : Hist S A t) (j : Fin (t + 1)) :
    stateAt (ofHist h) j = histStateAt h j := by
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- **`toHist` is surjective**, so every production history is denoted -- the
carriers are isomorphic and `Path` imposes no well-formedness restriction. -/
theorem toHist_ofHist {t : ℕ} (h : Hist S A t) : toHist (ofHist h) = h := by
  refine Prod.ext ?_ ?_
  · funext i
    refine Prod.ext ?_ rfl
    change stateAt (ofHist h) i.castSucc = (h.1 i).1
    rw [stateAt_ofHist]
    change (if hlt : (i : ℕ) < t then (h.1 ⟨i, hlt⟩).1 else h.2) = (h.1 i).1
    rw [dif_pos i.isLt]
  · show current (ofHist h) = h.2
    change stateAt (ofHist h) (Fin.last t) = h.2
    rw [stateAt_ofHist]
    change (if hlt : t < t then (h.1 ⟨t, hlt⟩).1 else h.2) = h.2
    rw [dif_neg (lt_irrefl t)]

end PathCarrierPrototype
