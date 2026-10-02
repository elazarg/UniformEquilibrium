# Review of gpt/SURPLUS.md

Reviewer: SOCIAL_WEIGHT_REVIEW  
Date: 2026-08-31  
Verdict: **REVISE; the mathematics is largely sound, but it is not a
consumer.  One static strengthening and one chronological localization lemma
are genuinely new.**

## Claim checked

The response studies the strict positive-social escape data from
POSITIVE_SOCIAL_SURPLUS_ESCAPE_CONSUMER.  It claims:

1. zero global minimum already gives terminal approximate Nash profiles with
   one limiting payoff;
2. positive global minimum makes the supplied no-costate hypothesis
   automatic, and even excludes every nonzero nonnegative static costate;
3. the escape account localizes to cofinally deep actual finite blocks with a
   fixed positive raw absorption floor; and
4. this still does not create exact Nash--Bellman edges, an endpoint return,
   or a finite rank.

The conclusions are correct after the quantifier and terminology repairs
below.  They consume neither the strict positive-social escape branch nor the
off-minimum paid port or reset-rigid minimum.

## 1. Zero minimum and the abstract positive gap

The zero-minimum argument is exact.  If
\(\operatorname{Sem}(\sigma_n)\to(U,B)\) and \(D(U,B)=0\), then

\[
 0\le d_i(\sigma_n)\le D(\sigma_n)\longrightarrow0.
\]

Every unilateral behavioral replacement gains at most \(d_i(\sigma_n)\), so
the same profiles are terminal approximate Nash profiles and their prescribed
payoffs converge to one fixed vector.

In the positive branch, global minimality gives \(D(\sigma)\ge D_*\) for every
actual profile.  Some coordinate debt is at least \(D_*/|I|\), and approximate
attainment of the unrestricted cap gives a behavioral deviation of gain
strictly above \(D_*/(2|I|)\).  This is the standard semantic positive-gap
consequence of the assumed \(D_*>0\).  It is not a certified explicit
counterexample table and is not new.

## 2. The costate calculation

Under the question's hypothesis \(s_i=r_i(\{i\})\ge0\), the costate
calculation is correct.

At a positive global minimum,

\[
 U_i-s_i\ge D_*-d_i\ge0.
\tag{1}
\]

If \(U_i=s_i\), then \(d_i=D_*\), every other debt vanishes, and (1) is strict
for every other coordinate.  Hence at most one coordinate of \(U-s\) is zero.
Every nonnegative vector with at least two positive coordinates therefore
has

\[
 \theta\cdot(U-s)>0.
\]

If the table inequalities

\[
 \theta\cdot(r(S)-s)\le0
\]

held for every nonempty coalition, the reward-moment identity, including the
zero Never payoff, would instead give

\[
 \theta\cdot U
 \le (1-m^*(\mathrm{Never}))\,\theta\cdot s
 \le\theta\cdot s,
\]

a contradiction.  This part is already contained in the exported
nonnegative-weight social chamber: because \(s\ge0\), its extra condition
\(\theta\cdot s\ge0\) is automatic.

The one-coordinate extension is a genuine strengthening.  If
\(r_i(S)\le s_i\) for every coalition, then every terminal outcome, including
Never, pays player \(i\) at most \(s_i\).  Thus every actual cap is at most
\(s_i\), and the limiting cap contradicts
\(D_*\le B_i-s_i\).  Combining the one-coordinate and multi-coordinate cases
gives

\[
 \nexists\,\theta\in\mathbb R^I_{\ge0}\setminus\{0\}:
 \theta\cdot(r(S)-s)\le0\quad\text{for every }S.
\tag{2}
\]

The stated strict finite-dimensional alternative is also correct:
(2) is equivalent to a probability law \(\lambda\) on nonempty coalitions
with

\[
 \sum_S\lambda_Sr_i(S)>s_i\qquad(i\in I).
\tag{3}
\]

Indeed, if the convex hull of \(r(S)-s\) missed the strictly positive
orthant, separation from that open cone would produce exactly a nonzero
nonnegative vector in (2).  Conversely, (3) has positive scalar product with
every such vector.  Conic Caratheodory additionally permits a witness
supported on at most \(|I|\) coalitions.

Equation (3) is stronger than the existing sparse export's
coordinatewise-nonnegative law with at least one strict coordinate, but it is
still only a static correlated reward-table certificate.  It carries no
source-law weights, product realization, cap, or chronology.

## 3. The deep finite-block lemma

Let the escape account be represented on its common refined subsequence, and
relabel that subsequence as \(\sigma_n\).  Put

\[
 A=\sum_Se(S)R(S)>0,\qquad M_R=\max_S|R(S)|.
\]

The proof that actual deep blocks carry fixed raw absorption is valid.
For fixed \(T\), convergence of the finite stopping-law coordinates gives
convergence of every first-absorption mass before \(T\), while convergence of
the complete terminal law gives

\[
 \lim_n\sum_{t\ge T,S}p_n(t,S)R(S)
 =
 \sum_Sm^*(S)R(S)-\sum_{t<T,S}\bar p(t,S)R(S).
\tag{4}
\]

Absolute summability follows from bounded rewards and total mass at most one.
The right side of (4) tends to \(A\) as \(T\to\infty\).  Therefore, for every
prescribed source-index lower bound and every prescribed date \(T_0\), one can
choose \(n\) beyond that index, \(T\ge T_0\), and finite \(L>T\) such that

\[
 \sum_{t=T}^{L-1}\sum_Sp_n(t,S)R(S)>A/4.
\tag{5}
\]

The response should state the source-index lower bound explicitly; it is what
permits a strict diagonal subsequence rather than merely deep dates attached
to repeatedly reused early profiles.

Since \(A>0\), one has \(M_R>0\), and (5) implies unconditional absorption
mass in the block at least

\[
 \kappa=A/(4M_R)>0.
\tag{6}
\]

The conditional block absorption is at least the same number because the
entry reach probability is at most one.  If \(a_{n,t}\) denotes the
conditional root absorption at the successive live rows, then

\[
 1-\prod_{t=T}^{L-1}(1-a_{n,t})
 \le\sum_{t=T}^{L-1}a_{n,t},
\]

so (6) also lower-bounds the sum of raw root absorption probabilities.
This is the precise meaning needed for “raw root charge.”

This localization appears absent from the current escape-account
declarations and the weighted-social export.  It is useful new producer
information: terminal-law escape cannot remain wholly nonlocal in calendar
time.  It is nevertheless only arbitrary prescribed-root absorption.

## 4. No strategic consumer follows

The response correctly stops before the invalid inference.

- The selected block roots are not proved exact Nash against their actual
  continuations.
- Positive raw absorption is not punishment-floor admissible charge.
- The initial and terminal payoff/cap states of the block need not return.
- The static law (3) need not be a product-root law or even a behavioral
  terminal law.

The three-pair example correctly demonstrates the product-support mismatch.
Positive mass on all three pairs under one product root forces positive
singleton and triple masses as well.  The example is algebraic, not a
positive-gap quitting-game table, exactly as stated.

The result also does not address the finite-clock export directly.  That
packet reaches an actual off-minimum paid response; the present block comes
from a nonattained minimum's social escape and carries no paid or exact-root
annotation.  Nor does it consume a reset-rigid attained minimum.

## Required revisions

1. Relabel the common refined escape subsequence explicitly before defining
   \(p_n(t,S)\).
2. Strengthen the block quantifier to allow both the source index and the date
   to be prescribed arbitrarily far out.
3. Define raw root charge and include the elementary
   \(1-\prod(1-a_t)\le\sum a_t\) step.
4. Mark the multi-coordinate no-costate claim as already implied by the
   exported weighted chamber.  Separate the genuinely new one-coordinate
   exclusion and strict-all-coordinate lottery.
5. Do not describe the deep block as an admissible-payoff return or as a
   consumer of any Fin4 chamber.

After these revisions, the response is a sound negative answer plus two
useful strengthening lemmas.  It is not an answer to
POSITIVE_SOCIAL_SURPLUS_ESCAPE_CONSUMER.

