# Review: uniform exact-port reach and post-mark orientation

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Date: 2026-08-31

Verdict: **REVISE.**  The quantitative core is correct: a terminal-gap
witness gives a table-uniform positive survival floor through every finite
compatible exact punishment-floor prefix, and this composes with the scratch
actual-reach row to give the displayed joint-entry and paid-gap floors.  One
claim in Section 6 is false as written, and the word/source quantifiers need
to be stated more precisely.  Neither issue undermines Sections 2--5.

## 1. One-root margin

The named checked estimate is

\[
 q_i(Q)\le 1-\frac{\gamma}{4M}.
\]

Its hypotheses are exactly the ones available at every punishment-floor
orbit state: the tail lies in the reward box, dominates every punishment
value, and the root is exact Nash against that tail.  Positive terminal gap
forces \(M>0\).  Thus, for Fin4,

\[
 c(q)=\prod_{i<4}q_i(C)\ge
 \left(\frac{\gamma}{4M}\right)^4=:r>0.
\]

The theorem itself also implies that the displayed ratio is at most one
whenever such a root exists.  The constants and direction of (2.1)--(2.4)
are correct.

## 2. Charge-to-survival conversion

For \(c\in[r,1]\),

\[
 -\log c=\int_c^1\frac{dx}{x}
 \le\frac{1-c}{r}.
\]

The checked `prefixCharge_le` theorem bounds the sum of the absorption
charges \(1-c(q_t)\) of every finite `QuittingPunishmentFloorFinitePrefix`
by

\[
 C=\texttt{quittingPunishmentFloorPrefixChargeBound reward}.
\]

Consequently

\[
 \prod_{t<N}c(q_t)\ge e^{-C/r}.
\]

This argument is exact, and the floor is uniform in the prefix certificate
and its depth.  “Any exact word” should nevertheless be replaced by “any
compatible exact punishment-floor prefix certificate”: the word must carry
the box, anchor-floor, Bellman, and exact-Nash fields, and when it is composed
with \(\sigma_n\), its inner boundary must be the prescribed payoff of that
same \(\sigma_n\).  The theorem does not authorize attaching an unrelated
exact word to an arbitrary suffix.

## 3. Composition with the selected row

For every sufficiently late source index \(n\), the scratch theorem may be
applied with \(\Delta=D_*/2\).  It gives a row of declared gain

\[
 g_0=\Delta/4=D_*/8

\]

and

\[
 \Delta^2\le32M^2\,
 \Pr_{\sigma_n}(\text{joint survival to the row start}),
\]

so the floor \(D_*^2/(128M^2)\) is correct.  Literal prefix factorization
then multiplies joint entry by the whole-root Continue product.  The
pure-time payoff difference is multiplied by the observer-deleted opponent
Continue product, which is at least the joint product.  Equations
(4.3)--(4.4) therefore have the right constants.

Exact Nash prefixing against the actual prescribed continuation makes every
semantic-debt coordinate nonincreasing.  Global minimality supplies the
other inequality, so

\[
 D_*\le D(W\star\sigma_n)\le D(\sigma_n)

\]

uniformly over every compatible word and depth.  The precise quantifiers are

\[
 \exists n_0\ \forall n\ge n_0\ \exists\text{ row}_n\
 \forall N\ \forall W\text{ compatible of depth }N,
\]

with constants \(\lambda,\rho,g_0\) independent of \(n,N,W\).  The dates,
row witnesses, and support atoms may depend on \(n\).  The support theorem
asserts only positive mass of the selected source witness, not a uniform
lower bound on that atom.

## 4. What is and is not reached

The probability in (4.3) is joint survival to the shifted first-disagreement
**start**.  It is not:

* prescribed stopping mass at that start;
* mass of a terminal coalition at that start;
* survival from the start to the later pure-time witness;
* a positive-hazard interval after the start; or
* reach of a later suffix carrying near-minimum debt or exact Nash--Bellman
  data.

The paid gap compares two counterfactual pure stopping laws.  It is not an
actual prescribed root defect.  The exact roots in the construction all lie
before the shifted row.  Thus the orientation objection and the list of
missing post-mark fields are correct.

The local floor-safe screening regression also works, with one wording
clarification.  For the paid player \(m\), the punishment value is at most
its maximal reward one (and in fact its singleton option forces one); player
\(o\)'s punishment value is zero because the opponents may all Never; the
other two reward coordinates are identically zero.  Hence the displayed
receiving profile is floor-safe even though its post-row tail is unreachable.

## 5. False Never-mass claim

The sentence

> Since (4.3) persists while the row date tends to infinity, every compact
> law limit retains positive Never mass.

does not follow and is false for the project's date-forgetting terminal
outcome law.  Take profiles in which everyone Continues until date \(t_n\)
and one fixed player Quits surely at \(t_n\).  Joint reach to \(t_n\) is one
and \(t_n\to\infty\), but every terminal outcome law is the same Dirac mass
on that player's singleton; Never mass is zero in every profile and in the
limit.

If one instead compactifies labelled stopping times in a one-point
compactification, escaping date mass may appear at the added point, but that
is a different law object and needs a proved adapter back to the game's
terminal semantics.  Ordinary outcome-law compactness supplies no such
conclusion.  Section 6 should delete the Never-mass assertion and retain only
the valid statement that a uniformly reached marked feature can escape to
unbounded dates while date-forgetting law loses its relative timing.

## 6. Exact surviving result and Lean boundary

After the two revisions, the valid result is:

> Under a terminal exploitability witness, every compatible finite exact
> punishment-floor prefix preserves a table-uniform fraction
> \(e^{-C/r}\) of the literal suffix.  Applied to the repaired near-minimum
> sources and the scratch actual-reach selector, this yields cofinally deep
> actual profiles with uniform joint entry and paid pure-time gap at the
> shifted row, while all exact roots remain before the row.

The marginal terminal-gap estimate and prefix charge bound are production
Lean declarations.  The actual-reach and support selections are
kernel-checked conference-scratch declarations, not production imports.  The
exponential product estimate and the composed all-source/all-depth theorem
are ordinary mathematics and are not yet packaged as Lean declarations.

This is a useful strengthening of the pre-row passport, but it remains a
producer.  The absent post-mark data are exactly a later reached cut, positive
hazard between cuts, near-minimum semantic control at that later suffix,
exact Nash--Bellman rows after the mark, and renewable source ancestry.
