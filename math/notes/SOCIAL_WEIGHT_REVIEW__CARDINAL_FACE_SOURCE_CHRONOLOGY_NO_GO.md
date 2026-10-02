# Proper-face sources do not form a chronology

**Owner:** SOCIAL_WEIGHT_REVIEW

**Current status.** The propositions below are complete ordinary
mathematics and give an explicit full-data obstruction to one natural
cardinal-reduction route. They do not prove a cardinal bound and do not
construct a counterexample. The remaining positive question is whether the
ambient positive-gap hypothesis yields a genuinely nonchronological
cross-face compiler.

## 1. Question

For every nonempty proper retained set \(J\subset I\), cardinal minimality
supplies a terminal approximate equilibrium of the induced \(J\)-player game.
After quiet lifting and recentering an omitted player's pure-time gap witness,
one may retain:

* an actual \(J\)-face suffix reached with one common positive probability;
* a zero-debt limiting semantic pair and terminal law on that face; and
* one omitted player \(d_J\notin J\) with a fixed immediate-Quit gain.

Can simultaneous selection of these data make the face sources consecutive
states of one actual parent chronology? The answer is no, even when every
source is attained, exact, and reached with probability one. Moreover the
outsider selector can be completely arbitrary.

This is a source/law obstruction, not a one-stage sign calculation.

## 2. Universal-selector regression

Let \(I\) be any finite player set with at least two players, and define

\[
r_i(S)={\bf 1}_{\{i\in S\}}
\qquad(\varnothing\ne S\subseteq I).
\tag{2.1}
\]

For every nonempty proper \(J\subset I\), let \(\tau_J\) be the profile of the
induced game on \(J\) in which every member of \(J\) Quits at date zero. Let
\(\widehat\tau_J\) be its ambient quiet lift: every player outside \(J\)
plays Never.

### Proposition 2.1

For every nonempty proper \(J\subset I\):

1. \(\tau_J\) is an exact terminal Nash profile against all behavioral
   deviations;
2. its complete induced-game semantic pair is \(U_i=B_i=1\) for every
   \(i\in J\), and its law is the Dirac law \(\delta_J\);
3. \(\widehat\tau_J\) is an actual parent profile and the displayed face
   source occurs at date zero with reach one;
4. every omitted player \(d\notin J\), not just one selected player, has
   prescribed payoff zero and gains exactly one by Quitting immediately; and
5. the ambient all-Quit profile is itself an exact terminal Nash profile.

#### Proof

At \(\tau_J\), the terminal coalition is \(J\). Every survivor receives one,
the maximum value of its reward coordinate, so no behavioral deviation can
improve. This proves (1) and (2), including the unrestricted cap statement.

The ambient quiet lift is literal and already begins at the recentered face
source, proving (3). Its terminal coalition is still \(J\). An omitted
player \(d\) receives zero because \(d\notin J\). If \(d\) Quits at date
zero, the terminal coalition is \(J\cup\{d\}\), and \(d\) receives one. This
proves (4). Finally, under ambient all-Quit every player receives its maximum
reward one, proving (5). \(\square\)

### Corollary 2.2: arbitrary outsider passports

Let

\[
c:\{J:\varnothing\ne J\subsetneq I\}\longrightarrow I,
\qquad c(J)\notin J,
\tag{2.2}
\]

be any choice function. The sources in Proposition 2.1 realize the selected
outsider \(d_J=c(J)\) simultaneously, all with error zero, reach one, and
immediate gain one.

Thus the labelled proper-face passport contains no hidden combinatorial
coherence. For example, on \(I=\mathbb Z/n\mathbb Z\), the singleton-face
selection \(c(\{i\})=i+1\) is one directed cycle of length \(n\). Every
nonempty set closed under these selected singleton witnesses is all of \(I\),
so no four-player witness-closed kernel follows, for arbitrarily large \(n\).

The example is deliberately a solved game. It proves that the simultaneous
face fields themselves do not encode positive interior exploitability; any
cardinality proof must use the ambient no-uniform-payoff hypothesis in a way
not already summarized by those fields.

## 3. Positive-reach tails retain law seams

Let \(A=(q_0,\ldots,q_{T-1})\) be a finite word of parent product roots, and
write

\[
c(A)=\prod_{t<T}\Pr_{q_t}(\hbox{all Continue}).
\]

For any two actual tail profiles \(\sigma,\sigma'\), prefix factorization gives

\[
U_i(A\star\sigma')-U_i(A\star\sigma)
=c(A)\bigl(U_i(\sigma')-U_i(\sigma)\bigr)
\tag{3.1}
\]

for every payoff coordinate. At the complete terminal-law level,

\[
\mu_{A\star\sigma'}-\mu_{A\star\sigma}
=c(A)(\mu_{\sigma'}-\mu_\sigma).
\tag{3.2}
\]

Consequently

\[
\|\mu_{A\star\sigma'}-\mu_{A\star\sigma}\|_{\rm TV}
=c(A)\|\mu_{\sigma'}-\mu_\sigma\|_{\rm TV}.
\tag{3.3}
\]

These are equalities, not continuity estimates: every outcome before the end
of \(A\) is common to the two profiles, and the tail law is used exactly on
the all-Continue event through \(A\).

### Proposition 3.1: no common positive-reach nesting of distinct pure faces

Suppose the tail at one cut has law \(\delta_J\), and a later cut is reached
from it with conditional probability \(c>0\) and has law \(\delta_K\), where
\(J\ne K\). This is impossible.

Indeed the earlier law assigns at least \(c\) to terminal coalition \(K\),
because the all-Continue passage to the later cut has probability \(c\) and
the later tail terminates at \(K\). But \(\delta_J(K)=0\).

Equivalently, replacing the \(\delta_J\) tail by a \(\delta_K\) tail behind a
prefix reached with probability at least \(\rho>0\) creates the exact law seam

\[
\|\mu_{A\star\tau_K}-\mu_{A\star\tau_J}\|_{\rm TV}
=c(A)\ge\rho.
\tag{3.4}
\]

In the regression of Section 2 the face sources are maximally simple and
attained, but no two distinct face laws can be successive positive-reach
suffixes of one profile.

## 4. Consequence for a backward compiler

Uniform reached-face normalization removes the witness-time problem, but it
does not orient faces chronologically. In fact its positive reach makes an
unmatched tail visible: by (3.1)--(3.3), a tail payoff or law discrepancy is
multiplied by at least \(\rho\), rather than disappearing.

Therefore a compiler which serializes separately selected face sources must
provide additional data of one of the following forms:

1. an actual common source whose successive face tails already satisfy the
   prefix affine relations;
2. a quantitative full payoff/law seam tending to zero before every splice;
3. an accepted charged seam paid by a chronological consumer; or
4. a genuinely nonchronological construction, such as a profilewise
   score-dominating or topological compiler.

The current proper-face hypotheses provide none of these. Immediate outsider
Quit is absorbing; it does not move to the equilibrium source on the enlarged
face. Conversely, replacing the old tail by that independently solved
enlarged-face source is precisely the seam measured above.

## 5. Strongest valid no-go and remaining question

The regression proves the following exact limitation:

> Simultaneously attained zero-debt face sources, uniform actual suffix reach,
> complete terminal laws and caps, and fixed immediate outsider gains do not
> imply a bounded witness kernel or a common source chronology. Their labels
> may realize any proper-face choice function.

It does not prove that a cardinal-minimal counterexample exists, and it does
not refute a compiler using the parent positive-gap hypothesis globally. The
remaining cardinal question is correspondingly narrower:

> Does positive ambient exploitability force either a nonchronological
> score-dominating combination of the face equilibria, or one pair of face
> sources with a source-attached payoff/law seam that can be charged and
> consumed?

A construction which only nests the already selected positive-reach suffixes
cannot answer it.

## 6. Source correspondence and novelty

The exact prefix payoff and law factorizations used in Section 3 are the
standard live-prefix identities already present throughout the quitting path
and terminal-law layers. The arbitrary-cardinality cyclic witness-closure
regression is checked abstractly in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticEssentialityPassportCompressionRegression.lean.

The incremental content here is the full proper-face realization: the single
table (2.1) realizes every choice function on all nonempty proper faces with
exact unrestricted child Nash profiles, literal parent quiet lifts, reach one,
and complete Dirac laws. Combining this with (3.2) proves that the
simultaneously reached sources still cannot be nested into one positive-reach
chronology. A narrow conference/source search found no prior statement of
that full-data no-go.

## 7. Scope

* No parent-gap table or counterexample is claimed; the regression parent has
  an exact all-Quit equilibrium.
* No cap lower bound across a changed tail is inferred. Prefix caps can mask
  tail alternatives; the prescribed payoff and law equalities already prove
  the stated obstruction.
* No impossibility of a nonchronological compiler is claimed.
* The result is a boundary theorem for the cardinal route, not an answer to
  CARDINAL_MINIMAL_OUTSIDER_CONSUMER.
