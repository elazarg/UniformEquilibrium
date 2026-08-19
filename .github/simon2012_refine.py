from pathlib import Path
p=Path('Literature/Simon2012.lean')
s=p.read_text()

def swap(old,new):
    global s
    if old not in s:
        raise SystemExit(f'missing: {old[:160]}')
    s=s.replace(old,new,1)

swap('/-- The strengthened version discussed immediately after Question 2. -/', '''/--
The strengthened version discussed immediately after Question 2.  The omitted
proof is the escape-game spanning construction: it needs the Cech-homology
restriction and connected-component lemmas that remain `sorry` in
`Literature.Simon2007`, so no checked topological argument is currently
available to instantiate this statement.
-/''')

swap('/-- Lemma 2.2 in its exact 2012 normalization. -/', '''/--
Lemma 2.2 in its exact 2012 normalization.  The missing proof is the direct
min-max estimate separating the cases `rⁿ ≥ χⁿ-3ε` and `rⁿ < χⁿ-3ε`.
Simon 2007 contains only a declaration under its stricter payoff-bound package;
the exact positive-`B` statement below is not a formal consequence of that
interface without reproving the quantitative estimate.
-/''')

swap('/-- Lemma 3.1: injectivity and the all-continue fiber. -/', '''/--
Lemma 3.1: injectivity and the all-continue fiber.  The missing argument chooses
a player with maximal change in quitting probability, compares her forced-quit
payoffs in the two rows, and uses the singular penalty in `φ` to force a strict
best-response contradiction.  No existing theorem packages that quantitative
injectivity argument.
-/''')

swap('/-- Lemma 3.2: surjectivity and continuity of the inverse. -/', '''/--
Lemma 3.2: surjectivity and continuity of the inverse.  The missing proof is
the paper's Jacobian argument: strict diagonal dominance gives local openness
and an inverse, Claim A gives positive-coordinate motion, and the lower
semicontinuous minimization closes surjectivity.  The generic
Kohlberg--Mertens declaration in Simon 2007 does not imply this explicit `φ`
homeomorphism.
-/''')

swap('/-- Lemma 3.3. -/', '''/--
Lemma 3.3.  The missing proof rounds every sufficiently large quitting
probability to one and bounds the change in each forced-quit and
forced-continue payoff by the probability that the realized coalition changes.
The production library has analogous root inequalities, but no adapter to the
paper-local `QuittingGame` model or this exact constant package.
-/''')

swap('/-- Lemma 3.4, retaining all three displayed conclusions. -/', '''/--
Lemma 3.4, retaining all three displayed conclusions.  Its missing proof is
the properness case split on a large positive or negative coordinate of
`a = φ(β,p)`, using Lemma 3.3 to exclude an almost-sure quitter in the bounded
band and the definitions of `ξ` and `R` to control the interpolation.
-/''')

swap('/-- Lemma 3.5\'s two distance estimates. -/', '''/--
Lemma 3.5's two distance estimates.  The missing proof first uses exact
indifference for every player in positive quit support to place `β` near
`W_j ∩ ∂W`, then expands the definition of `φ` and the small-`q(p)` bound to
place `a` near the same face.  No reusable distance lemma for these fibers is
present in the repository.
-/''')

swap('/-- Corollary 4.1. -/', '''/--
Corollary 4.1.  The missing proof takes a minimum over the finitely many
nonempty principal player sets, uses continuity of determinant to preserve a
uniform determinant gap under entrywise perturbation, and then applies Lemma
4.1.  The finite minimum and subtype-matrix transport have not been assembled.
-/''')

swap('''Lemma 4.2: the upper glue is contained in `F_ε`.  Membership of `x` in the
upper neighborhood is explicit; without it `UpperGlueFiber` contains the
all-continue image even outside the domain intended in the paper.
''', '''Lemma 4.2: the upper glue is contained in `F_ε`.  Membership of `x` in the
upper neighborhood is explicit; without it `UpperGlueFiber` contains the
all-continue image even outside the domain intended in the paper.  The missing
proof is the finite product estimate that changing a row with total coordinate
hazard at most `|N|δ` changes each endpoint payoff by at most `ε/3`, followed
by the two support inequalities defining `E_ε`.
''')

swap('''uses normality, exclusion of the two simple equilibrium classes, the common
motion parameter, the constants `ξ,R`, and the support properties of the
cutoff.
''', '''uses normality, exclusion of the two simple equilibrium classes, the common
motion parameter, the constants `ξ,R`, and the support properties of the
cutoff.  The missing proof is the paper's three-way split according to the
player's quitting probability and continuation coordinate, with Lemma 2.2
supplying the strict coordinate increase in the low-rationality case.
''')

swap('''Lemma 4.4's boundedness of the continuation coordinate `β`, with the `d,ξ,R`
relations from the preceding construction made explicit.
''', '''Lemma 4.4's boundedness of the continuation coordinate `β`, with the `d,ξ,R`
relations from the preceding construction made explicit.  The missing proof
chooses a player of maximal quit probability, derives upper and lower bounds
on the corresponding continuation payoff from exact indifference, and then
uses the singular term in `φ` to contradict `a ∈ C` outside the displayed box.
''')

swap('''/--
The paper reports a counterexample to Question 2 and points to a similar
Gobbino--Simon construction, but does not print the counterexample.  Closing
this `sorry` requires importing or reconstructing that external example; no
claim in the present repository supplies it.
-/''', '''/--
The paper reports a counterexample to Question 2 and points to a similar
Gobbino--Simon construction, but does not print it.  The external blueprint is
Gobbino--Simon, Example 4.9: in `ℝ²`, take the square `[0,2]²` with the segment
from `(2,0)` to `(3,0)` attached, use the convex segment from `(1,1)` to `(3,0)`
as the exceptional fiber at `(2,0)`, and send the remaining square points to
`(3, dist(·, ∂[0,2]²))`.  Adapting that upper-semicontinuous correspondence to
the displayed homotopy and proving that it has only four iterations are the
missing formal obligations; no claim in the present repository supplies them.
-/''')

swap('''/--
Lemma 4.5.  This statement retains all seven conditions rather than replacing
them by a vague “viability” predicate.  Its proof contains the paper's long
contractibility/Jacobian and lower-boundary case analysis; no corresponding
production theorem exists.
-/''', '''/--
Lemma 4.5.  This statement retains all seven conditions rather than replacing
them by a vague “viability” predicate.  Its proof contains the paper's long
contractibility/Jacobian and lower-boundary case analysis; no corresponding
production theorem exists.  In Property (6), Case 5, the printed final phrase
“`λ ≥ 1/2`” must be read as “`1-λ ≥ 1/2`”: the preceding sentence proves
`λ ≤ 1/2`, and `y = λx + (1-λ)f(x,p)` needs the latter coefficient on the
strict drift.
-/''')

p.write_text(s)
