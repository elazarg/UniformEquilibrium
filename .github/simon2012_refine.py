from pathlib import Path
import re
p = Path('Literature/Simon2012.lean')
s = p.read_text()

def sub(pattern: str, replacement: str, flags=0):
    global s
    s2, n = re.subn(pattern, replacement, s, count=1, flags=flags)
    if n != 1:
        raise SystemExit(f'expected one match, found {n}: {pattern[:100]}')
    s = s2

def swap(old: str, new: str):
    global s
    if old not in s:
        raise SystemExit(f'missing: {old[:100]}')
    s = s.replace(old, new, 1)

swap(
'''The source leaves the symbol `δ` free in the definitions of stationarily
generated and instant approximate equilibria.  We therefore first define the
notions at a fixed punishment accuracy `δ`, and then use the arbitrarily-small
`δ` closure in the numbered results.  This records the only quantification
compatible with the compactness argument immediately following Lemma 2.1;
it is not hidden in prose.
''',
'''The source leaves the symbol `δ` free in the definitions of stationarily
generated and instant approximate equilibria.  We therefore first define the
notions at a fixed punishment accuracy `δ`, and then use the arbitrarily-small
`δ` closure in the numbered results.  This is the quantification used by the
compactness argument immediately following Lemma 2.1; it is not hidden in
prose.

`Payoff N = N → ℝ` inherits mathlib's finite product norm.  Thus the topological
claims are represented in an equivalent finite-dimensional norm, while every
quantitative estimate below is explicitly a claim in that chosen norm.  No
unmentioned identification with the Euclidean two-norm is used.
''')

swap('''def IsSimonPayoffScale (G : QuittingGame) (M : ℝ) : Prop :=
  1 ≤ M ∧
    (∀ A n, |G.reward A n| ≤ M / 3) ∧
    ∀ A B n, 3 * |G.reward A n - G.reward B n| ≤ M
''', '''def IsSimonPayoffScale (G : QuittingGame) (M : ℝ) : Prop :=
  1 ≤ M ∧
    (∀ A n, |G.reward A n| ≤ M / 3) ∧
    ∀ A B n, 3 * |G.reward A n - G.reward B n| ≤ M

/-- The standing assumption `|N| ≥ 3` made at the start of Section 2.1. -/
def HasAtLeastThreePlayers (G : QuittingGame) : Prop :=
  3 ≤ Fintype.card G.Player
''')

swap('/-- Use a fixed row through stage `M`, then switch to the punishment profile. -/',
     '/-- Use a fixed row for `M` stages, then switch to the punishment profile. -/')
swap('fun t => if t ≤ M then p else punishment (t - (M + 1))',
     'fun t => if t < M then p else punishment (t - M)')

marker = '/-- Lemma 2.1(1), isolated from the corrected compactness clause. -/'
insert = '''/--
The compact-set form of Lemma 2.1(2).  This is the corrected statement behind
the displayed distance-one application: the common parameter may depend on
`K`.  The proof is the compact-subsequence argument in the paper; neither the
uncorrected Simon 2007 declaration nor the production quitting-game library
contains this uniformization.
-/
theorem lemma2_1_part2_compact (G : QuittingGame)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (K : Set (Payoff G.Player)) (hK : IsCompact K) :
    SatisfiesCompactMotionBound G K := by
  sorry

'''
swap(marker, insert + marker)

swap('∀ j, MinMaxQuit G j - ρ / 2 < x j ∧ x j ≤ M',
     '∀ j, MinMaxQuit G j - ρ / 2 ≤ x j ∧ x j ≤ M')

sub(r'''/--\nA parameter strong enough for both motion inequalities used in Theorem 3\.1\..*?def IsStructureMotionParameter \(G : QuittingGame\) \(ρ : ℝ\) : Prop :=\n  SatisfiesCorrectedLemma2_1Parameter G ρ ∧\n  0 < ρ ∧ ρ ≤ 1 ∧ ∀ r p, p ∈ EpsilonRow G ρ r →\n    ρ \* QuitProbability G p ≤ ‖r - QuittingOneStagePayoff G r p‖\n''', '''/--
A single `ρ` satisfying the two motion estimates on the bounded continuation
region used in Sections 3--4.  Lemma 2.3 is pointwise (`∀ r, ∃ ρ`); compactness
is therefore essential before one speaks of a common `ρ` in Theorem 3.1.
-/
def IsStructureMotionParameter (G : QuittingGame) (M ρ : ℝ) : Prop :=
  SatisfiesCorrectedLemma2_1Parameter G ρ ∧
  0 < ρ ∧ ρ ≤ 1 ∧
  ∀ r : Payoff G.Player,
    (∀ j, MinMaxQuit G j - ρ ≤ r j ∧
      r j ≤ 2 * (Fintype.card G.Player : ℝ) * M) →
    ∀ p, p ∈ EpsilonRow G ρ r →
      ρ * QuitProbability G p ≤ ‖r - QuittingOneStagePayoff G r p‖
''', re.S)

swap('''    ∀ ρ, IsStructureMotionParameter G ρ →
      (∀ x, x ∈ FRow G 0 x → x ∈ closure ((WSet G)ᶜ)) ∧
''', '''    ∀ (_hnormal : ∀ n, IsNormalPlayer G n)
      (_hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
      (_hinstant : ¬HasInstantApproximateEquilibria G)
      (ρ : ℝ), IsStructureMotionParameter G M ρ →
      (∀ x, x ∈ FRow G 0 x → x ∈ closure ((WSet G)ᶜ)) ∧
''')

swap('''theorem lemma3_4 (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hM : IsSimonPayoffScale G M)
    (hconstants : AreSection3Constants G M d ρ ξ R)
''', '''theorem lemma3_4 (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hM : IsSimonPayoffScale G M)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
''')

swap('''  (∀ A n, |reward' A n - G.reward A n| ≤ tol) ∧
  (∀ i, reward' ⟨{i}, Finset.singleton_nonempty i⟩ i = SoloPayoff G i) ∧
''', '''  (∀ A n, |reward' A n - G.reward A n| ≤ tol) ∧
  (∀ A, A.1.card ≠ 1 → reward' A = G.reward A) ∧
  (∀ i, reward' ⟨{i}, Finset.singleton_nonempty i⟩ i = SoloPayoff G i) ∧
''')

swap('/-- Lemma 4.2: the upper glue is contained in `F_ε`. -/', '''/--
Lemma 4.2: the upper glue is contained in `F_ε`.  Membership of `x` in the
upper neighborhood is explicit; without it `UpperGlueFiber` contains the
all-continue image even outside the domain intended in the paper.
-/''')
swap('''    ∀ x y, y ∈ UpperGlueFiber G R ε δ x → y ∈ FRow G ε x := by
''', '''    ∀ x, x ∈ UpperNeighborhood G R ε → ∀ y,
      y ∈ UpperGlueFiber G R ε δ x → y ∈ FRow G ε x := by
''')

swap('/-- Lemma 4.3\'s coordinate drift statement. -/', '''/--
Lemma 4.3's coordinate drift statement, under the standing Section 3--4
choices used in its proof.  These hypotheses are not optional: the paper uses
normality, exclusion of the two simple equilibrium classes, the common motion
parameter, the constants `ξ,R`, and the support properties of the cutoff.
-/''')
swap('''theorem lemma4_3 (G : QuittingGame) (M d ρ R : ℝ)
    (hM : IsSimonPayoffScale G M)
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval)
''', '''theorem lemma4_3 (G : QuittingGame) (M d ρ ξ R δ : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hnormal : ∀ n, IsNormalPlayer G n)
    (hgenerated : ¬HasStationarilyGeneratedApproximateEquilibria G)
    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval)
    (hcutoff : IsSection4Cutoff G R δ cutoff)
''')

swap('/-- Lemma 4.4\'s boundedness of the continuation coordinate `β`. -/', '''/--
Lemma 4.4's boundedness of the continuation coordinate `β`, with the `d,ξ,R`
relations from the preceding construction made explicit.
-/''')
swap('''theorem lemma4_4 (G : QuittingGame) (M d R : ℝ)
    (hM : IsSimonPayoffScale G M) (z : EZeroTilde G)
''', '''theorem lemma4_4 (G : QuittingGame) (M d ρ ξ R : ℝ)
    (hM : IsSimonPayoffScale G M)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hconstants : AreSection3Constants G M d ρ ξ R)
    (z : EZeroTilde G)
''')

swap('''theorem lemma4_5 (G : QuittingGame) (M d ρ ξ R ε δ : ℝ)
    (hM : IsSimonPayoffScale G M)
''', '''theorem lemma4_5 (G : QuittingGame) (M d ρ ξ R η ε δ : ℝ)
    (hplayers : HasAtLeastThreePlayers G)
    (hM : IsSimonPayoffScale G M)
    (hd : 0 < d) (hd1 : d ≤ 1)
''')
swap('''    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hnonsingular : HasNonsingularSingletonDifferences G)
    (hconstants : AreSection3Constants G M d ρ ξ R)
''', '''    (hinstant : ¬HasInstantApproximateEquilibria G)
    (hmotion : IsStructureMotionParameter G M ρ)
    (hnonsingular : HasNonsingularSingletonDifferences G)
    (hη : Corollary4_1Statement G η)
    (hconstants : AreSection3Constants G M d ρ ξ R)
''')
swap('''    (hcutoff : IsSection4Cutoff G R δ cutoff)
    (hε : 0 < ε)
''', '''    (hcutoff : IsSection4Cutoff G R δ cutoff)
    (hε : 0 < ε) (hεη : ε < η / 3) (hερ : ε < ρ / 3)
''')

p.write_text(s)
