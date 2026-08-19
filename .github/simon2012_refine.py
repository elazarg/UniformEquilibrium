from pathlib import Path
p = Path('Literature/Simon2012.lean')
s = p.read_text()

def swap(old, new):
    global s
    if old not in s:
        raise SystemExit(f'missing: {old[:120]}')
    s = s.replace(old, new, 1)

# Question 2 includes the graph-domain hypothesis G ⊆ C × R^n.
swap('''  IsFullDimensionalStarShaped C ∧
  IsCompact G ∧
  (∀ c ∈ C, (GraphFiber G c).Nonempty ∧ Convex ℝ (GraphFiber G c)) ∧
''', '''  IsFullDimensionalStarShaped C ∧
  IsCompact G ∧
  (∀ g ∈ G, g.1 ∈ C) ∧
  (∀ c ∈ C, (GraphFiber G c).Nonempty ∧ Convex ℝ (GraphFiber G c)) ∧
''')

# Stages in the paper are indexed from zero, so “up to and including M” means t ≤ M.
swap('/-- Use a fixed row for `M` stages, then switch to the punishment profile. -/',
     '/-- Use a fixed row through stage `M`, then switch to the punishment profile. -/')
swap('fun t => if t < M then p else punishment (t - M)',
     'fun t => if t ≤ M then p else punishment (t - (M + 1))')

# Lemma 3.3 states only the upper bound here; the global hypothesis already supplies the lower bound.
swap('''        (p l : ℝ) ≤ 1 - ε / (2 * (Fintype.card G.Player : ℝ) * M) →
          |β l| ≤ (Fintype.card G.Player : ℝ) * M) →
''', '''        (p l : ℝ) ≤ 1 - ε / (2 * (Fintype.card G.Player : ℝ) * M) →
          β l ≤ (Fintype.card G.Player : ℝ) * M) →
''')

# Make the quantifier repair in Theorem 3.1 explicit.
swap('''A single `ρ` satisfying the two motion estimates on the bounded continuation
region used in Sections 3--4.  Lemma 2.3 is pointwise (`∀ r, ∃ ρ`); compactness
is therefore essential before one speaks of a common `ρ` in Theorem 3.1.
''', '''A single `ρ` satisfying the two motion estimates on the bounded continuation
region used in Sections 3--4.  The printed phrase “`ρ` satisfies Lemmas 2.1
and 2.3” mixes a common parameter with Lemma 2.3's pointwise quantifiers
`∀ r, ∃ ρ`; this predicate records the bounded uniformization actually used
by Lemmas 3.3--4.5 rather than silently asserting a global `∃ ρ, ∀ r`.
''')

# The paper fixes 0 < d ≤ 1 for all subsequent estimates.
swap('''theorem lemma3_5 (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (z : EZeroTilde G)
''', '''theorem lemma3_5 (G : QuittingGame) (M d : ℝ)
    (hM : IsSimonPayoffScale G M) (hd : 0 < d) (hd1 : d ≤ 1)
    (z : EZeroTilde G)
''')

# Record the two numerical definitions made before the cutoff.
marker='''/-- The cutoff `λ` used to glue the structure homotopy to the identity near `D`. -/
'''
insert='''/-- The small quitting bound `δ = ε / (2|N|M)` from Section 4.3. -/
def Section4Delta (G : QuittingGame) (M ε : ℝ) : ℝ :=
  ε / (2 * (Fintype.card G.Player : ℝ) * M)

/-- The small-step radius `ω = d ε ξ ρ δ / (200 R |N|² M)`. -/
def Section4Omega (G : QuittingGame) (M d ρ ξ R ε : ℝ) : ℝ :=
  d * ε * ξ * ρ * Section4Delta G M ε /
    (200 * R * (Fintype.card G.Player : ℝ) ^ 2 * M)

'''
swap(marker, insert + marker)

# Lemma 4.2 needs ε > 0, and uses the named delta.
swap('''theorem lemma4_2 (G : QuittingGame) (M R ε δ : ℝ)
    (hM : IsSimonPayoffScale G M)
    (hδ : δ = ε / (2 * (Fintype.card G.Player : ℝ) * M)) :
''', '''theorem lemma4_2 (G : QuittingGame) (M R ε δ : ℝ)
    (hM : IsSimonPayoffScale G M) (hε : 0 < ε)
    (hδ : δ = Section4Delta G M ε) :
''')

# Use the named delta in Lemma 4.5 too.
swap('''    (hε : 0 < ε) (hεη : ε < η / 3) (hερ : ε < ρ / 3)
    (hδ : δ = ε / (2 * (Fintype.card G.Player : ℝ) * M)) :
''', '''    (hε : 0 < ε) (hεη : ε < η / 3) (hερ : ε < ρ / 3)
    (hδ : δ = Section4Delta G M ε) :
''')

p.write_text(s)
