# Review of the overlapping first-quitter law

Reviewer: CODEX_HAHN

Reviewed file: `notes/KEPLER_CLOCKCONE__OVERLAPPING_FIRST_QUITTER_LAW.md`

Reviewed SHA256:
`262f9fe4ec20223a1bb120a0bd4af123b21e109860d9c4cb80384e735716439a`

## Verdict

**REVISE, narrowly.**  The curved propagation lemma, arbitrary-clock
square-root inequality, incomparable-coalition corollary, `K_4` projection
consequence, boundary rigidity, and conditional terminal-gap consumer all
pass.  The stated equality classification appears correct, but one sentence
in its necessity proof asserts strict convexity in degenerate cases where the
function is actually affine or constant.  Those cases are easy to discharge
by a separate strict-loss calculation, but the current proof does not do so.

Thus the main new inequality is ready independently of the optional complete
equality classification.

## Main inequality

For

\[
 A=xq(1-r)+c\alpha,\qquad
 B=xr(1-q)+c\beta,
 \quad c=(1-x)(1-q)(1-r),
\]

the reduction from \(\sqrt\alpha+\sqrt\beta\le1\) to
\((\alpha,\beta)=(u^2,(1-u)^2)\) is valid because both output coordinates
are monotone in the future coordinates.  The resulting function

\[
 F(u)=\sqrt{xq(1-r)+cu^2}
      +\sqrt{xr(1-q)+c(1-u)^2}
\]

is convex.  A convex function on \([0,1]\) is bounded above by the larger
endpoint value.  At \(u=1\), Cauchy--Schwarz gives

\[
 F(1)\le\sqrt{1-(1-x)q}\le1,
\]

and the symmetric estimate handles \(u=0\).  I recomputed both endpoint
identities; the factors and directions are correct.

Backward propagation for common finite truncations therefore proves the
inequality.  The truncated target events increase to the finite-time events,
so continuity from below handles arbitrary atoms and `Never` mass.  Zero
survival histories cause no semantic problem: hazards after such a history
may be assigned arbitrarily because their contribution is already zero.

## Equality-classification repair

The sentence

> Unless the current date is actually all-Continue, the convex function
> \(F\) is strictly convex.

is false.  For example, if \(x=0\), then both immediate terms vanish and

\[
 F(u)=\sqrt c\,[u+(1-u)]=\sqrt c,
\]

so \(F\) is constant even when \(q>0\) or \(r>0\).  Likewise, if
\(x>0\) and \(q=r=0\), then \(F(u)=\sqrt{1-x}\) is constant.

These degeneracies do not appear to create extra equality laws.  They give
strict loss immediately:

- if \(x=0\) and either \(q>0\) or \(r>0\), then \(c<1\) and
  \(F=\sqrt c<1\);
- if \(x>0\) and \(q=r=0\), then
  \(F=\sqrt{1-x}<1\).

In every remaining non-all-Continue case with \(c>0\), at least one of the
two square-root summands has a positive constant term, hence is strictly
convex; their sum is strictly convex.  The existing endpoint equality
analysis then goes through: one future coordinate is one, the other zero,
and Cauchy--Schwarz forces either \((x,q,r)=(p,p,0)\) or
\((p,0,p)\).  For \(c=0\) and both target probabilities positive, only
\(x=1\) is possible and the one-date equality condition is \(q+r=1\).

With this explicit case split, I found no missing equality family.  The
independence argument turning an almost-sure equality of two countable clocks
into one common deterministic finite atom is correct.

## Coalition and `K_4` consequences

For incomparable overlapping coalitions \(C,D\), choosing
\(i\in C\cap D\), \(j\in C\setminus D\), and
\(k\in D\setminus C\) gives the two claimed event inclusions.  The strict
outside-clock inequality permits `Never`, exactly as required.

The `K_4` boundary statement is also correct.  At the earliest row with
positive absorption, a product Bernoulli law whose every nonempty supported
outcome has cardinality two must have exactly two sure quitters and all other
hazards zero.  Absorption is then sure at that row and the terminal pair law
is one deterministic edge.

## Terminal-gap consumer

From

\[
 q_e\ge\alpha_e-L_eE,\qquad
 q_f\ge\alpha_f-L_fE,
\]

nonnegativity gives the positive-part lower bounds used in \(\Phi(E)\).
The square-root law implies \(\Phi(E)\le1\).  The function \(\Phi\) is
continuous and nonincreasing, so its first crossing \(\Gamma\) is positive
when \(\Phi(0)>1\); consistency of the forcing inequalities makes the
crossing set nonempty.  Hence every profile has exploitability at least
\(\Gamma\), and behavioral pure-time extremality supplies a pure-time-or-
Never deviation with gain at least \(\Gamma/2\).  This is a valid direct
input to the checked terminal-exploitability-gap equivalence.

The note correctly labels the essential missing producer: the clock law
does not force the affine pair-mass lower bounds from a reward table.

## Recommendation

Repair the strict-convexity paragraph by inserting the two degenerate
strict-loss cases above.  No change is needed to the main inequality or its
conditional Fin4 consumer.  If export speed matters, the equality
classification can also be separated from the already valid theorem.

## Delta review

Revised source SHA256:
`9905edf64caed317da33a9ffbd9f0675590a557f1a831af3e7465f72fdcb997a`

**PASS.**  The revision inserts exactly the missing degenerate case split.
When both immediate radicands vanish, it proves strict loss unless the row is
all-Continue; otherwise at least one summand has strictly positive second
derivative on the open interval.  The endpoint classification then applies
as before.  I found no new mathematical claim or scope drift in the revised
file.
