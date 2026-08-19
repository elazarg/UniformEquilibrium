from pathlib import Path
p = Path('Literature/Simon2012.lean')
s = p.read_text()

def swap(old, new):
    global s
    if old not in s:
        raise SystemExit(f'missing: {old[:160]}')
    s = s.replace(old, new, 1)

old = '''/-- The second coordinate `y(a)` of the deformed graph. -/
def Section4Y (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval) (a : Payoff G.Player) :
    Payoff G.Player :=
  let x := Section4X G inverse cutoff a
  let p := (inverse.inv a).1.2
  (cutoff a : ℝ) • x +
    (1 - (cutoff a : ℝ)) • QuittingOneStagePayoff G x p
'''
new = '''/-- The one-stage payoff `z(a) = f(x(a),p(a))` used in Lemma 4.3. -/
def Section4Z (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval) (a : Payoff G.Player) :
    Payoff G.Player :=
  QuittingOneStagePayoff G (Section4X G inverse cutoff a) (inverse.inv a).1.2

/-- The second coordinate `y(a) = λ(a)x(a) + (1-λ(a))z(a)`. -/
def Section4Y (G : QuittingGame) {M d : ℝ}
    (inverse : PhiInverseData G M d)
    (cutoff : Payoff G.Player → UnitInterval) (a : Payoff G.Player) :
    Payoff G.Player :=
  let x := Section4X G inverse cutoff a
  (cutoff a : ℝ) • x +
    (1 - (cutoff a : ℝ)) • Section4Z G inverse cutoff a
'''
swap(old, new)

swap('''      (MinMaxQuit G j - ρ / 3 ≤ Section4X G inverse cutoff a j →
        MinMaxQuit G j - ρ / 3 ≤ Section4Y G inverse cutoff a j) ∧
      (Section4X G inverse cutoff a j < MinMaxQuit G j - ρ / 3 →
        Section4X G inverse cutoff a j + ρ ^ 2 / (500 * M) ≤
          Section4Y G inverse cutoff a j) := by
''', '''      (MinMaxQuit G j - ρ / 3 ≤ Section4X G inverse cutoff a j →
        MinMaxQuit G j - ρ / 3 ≤ Section4Z G inverse cutoff a j) ∧
      (Section4X G inverse cutoff a j < MinMaxQuit G j - ρ / 3 →
        Section4X G inverse cutoff a j + ρ ^ 2 / (500 * M) ≤
          Section4Z G inverse cutoff a j) := by
''')

swap('''Lemma 4.3's coordinate drift statement, under the standing Section 3--4
choices used in its proof.  These hypotheses are not optional: the paper uses
normality, exclusion of the two simple equilibrium classes, the common motion
parameter, the constants `ξ,R`, and the support properties of the cutoff.
''', '''Lemma 4.3's coordinate drift statement for `z = f(x,p)`, under the standing
Section 3--4 choices used in its proof.  The deformed graph coordinate is the
separate vector `y = λx + (1-λ)z`.  The hypotheses are not optional: the paper
uses normality, exclusion of the two simple equilibrium classes, the common
motion parameter, the constants `ξ,R`, and the support properties of the
cutoff.
''')

p.write_text(s)
