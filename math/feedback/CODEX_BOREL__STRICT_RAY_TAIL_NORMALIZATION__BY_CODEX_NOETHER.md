# Audit of the cardinal-two maximal-ray exclusion

Reviewer: `CODEX_NOETHER`

## Claim audited

Section 0 of
`notes/CODEX_BOREL__STRICT_RAY_TAIL_NORMALIZATION.md` claims that a
genuinely shrinking canonical **maximum-absorption exact-root** ray cannot
have limiting binding set

\[
A=\{i,j\}.
\]

The argument is conditional on the equilibrium-component index theorem for
finite normal-form games.  I checked the root-game reduction, the use of
maximality, the local equilibrium sets and their claimed indices, including
the one-clock/partial-support case.

## Verdict

The exclusion is mathematically valid **conditional on the standard
finite-game component-index package**, after one necessary repair to the
written localization argument.  There is no hidden genericity assumption:
the two-positive-clock case consists of regular isolated equilibria, and the
one-clock case is a degenerate equilibrium component whose index is computed
by a local payoff perturbation.

This is not currently a checked project theorem.  The declaration
`Literature.Simon2007.KohlbergMertensStatement` is marked `sorry`, and the
repository has no definition or library for Nash-component index, local
Brouwer degree, its perturbation invariance, or the global index sum.

## 1. Repair required in uniform localization

The note currently chooses a neighbourhood `U` in which absorption is below
`1/2`, then says that maximality and small absorption put every equilibrium
in `U`.  That implication does not follow from the displayed property of
`U`: in general

\[
x\in U\Longrightarrow \alpha(x)<1/2
\]

does not imply its converse.

The needed conclusion is nevertheless immediate and quantitative.  For a
binary product root \(x\), write

\[
\alpha(x)=1-\prod_h(1-x_h).
\]

For every coordinate,

\[
x_h\le \alpha(x),                                      \tag{1}
\]

because \(\prod_m(1-x_m)\le 1-x_h\).  Choose
\(\varepsilon>0\) so that the cube
\([0,\varepsilon)^{I}\) lies in the fixed neighbourhood where every outsider
strictly prefers Continue.  Since
\(\alpha(q_k)\to0\), eventually \(\alpha(q_k)<\varepsilon\).  If \(x\) is
*any* exact root against \(b_k\), maximum absorption gives

\[
\alpha(x)\le\alpha(q_k)<\varepsilon.
\]

Equation (1) then puts every coordinate of \(x\) below \(\varepsilon\), so
\(x\in U\).  This proves the required localization of the **entire** Nash
set, not just the selected equilibrium.

Once localized, every outsider has a strict Continue inequality and hence
zero Quit probability at every equilibrium.  The full binary root game is
therefore locally exactly the two-player game on \(A\); the strict outsider
coordinates do not change the local equilibrium indices.

## 2. Both binding players in support

At a sufficiently late selected root with \(x_i,x_j>0\), small absorption
also gives \(x_i,x_j<1\), so both players genuinely mix.  With

\[
\delta_h=b_{k,h}-s_h\ge0,
\]

their endpoint differences are

\[
g_i(x_j)=-(1-x_j)\delta_i+x_jJ_{ij},\qquad
g_j(x_i)=-(1-x_i)\delta_j+x_iJ_{ji}.           \tag{2}
\]

Mixing gives the two equalities in the note and first implies
\(J_{ij},J_{ji}\ge0\).  If, for example, \(J_{ij}=0\), then
\(\delta_i=0\).  Increasing \(x_j\) slightly leaves both active-player
equalities unchanged: player \(i\)'s difference is identically zero, while
player \(j\)'s difference depends only on \(x_i\).  Strict outsider
inequalities persist.  This produces an exact root with greater absorption,
contradicting maximality.  Thus

\[
J_{ij}>0,\quad J_{ji}>0,\quad \delta_i>0,\quad\delta_j>0. \tag{3}
\]

Inside the small neighbourhood there are exactly two equilibria:

* all Continue, a strict pure equilibrium of index \(+1\); and
* the unique completely mixed coordination equilibrium, which is regular
  and has index \(-1\).

The latter sign is the usual two-action coordination sign.  Equivalently,
the two cross derivatives in (2),
\(\delta_i+J_{ij}\) and \(\delta_j+J_{ji}\), are both positive, and the
regular mixed equilibrium has the opposite index from either strict pure
coordination equilibrium.  Strictly continuing outsider actions preserve
this index under deletion or reintroduction.

Hence the localized index sum is zero.  Since maximality plus (1) says this
is the complete Nash set, the global finite-game index sum would be zero,
contrary to the component-index theorem's value \(+1\).

No other partial-support equilibrium is omitted locally: with (3), the only
third equilibrium of the two-player restriction is all Quit, whose
absorption is one and which lies outside the chosen neighbourhood.  It need
not be an equilibrium of the full game; the index contradiction is exactly
what forces some additional full-game equilibrium outside the neighbourhood,
contradicting maximality.

## 3. Exactly one binding player in support

Suppose the selected root has \(x_i=x_k>0\), \(x_j=0\).  Since
\(x_k<1\), player \(i\)'s mixing condition gives \(\delta_i=0\).  Its
endpoint comparison is therefore independent of its own hazard.

If player \(j\)'s Continue inequality were strict at \(x_k\), one could
increase \(x_i\) slightly while retaining all outsider inequalities and
obtain a higher-absorption exact root.  Hence \(j\) is indifferent at the
maximal threshold:

\[
(1-x_k)\delta_j=x_kJ_{ji}.                    \tag{4}
\]

The common zero case \(\delta_j=J_{ji}=0\) would again allow a larger
hazard, so (4) implies

\[
\delta_j>0,\qquad J_{ji}>0.                   \tag{5}
\]

At the limiting cap both binding deltas vanish.  If \(J_{ij}<0\), a small
solo root at \(j\) makes \(i\) strictly Continue; if \(J_{ij}=0\), it makes
\(i\) indifferent.  Player \(j\) is indifferent and outsiders remain
strictly Continue.  Either gives a non-all-Continue exact root at the limit,
contrary to the strict-ray limiting hypothesis.  Therefore

\[
J_{ij}>0.                                      \tag{6}
\]

Equations (4)--(6) give the complete local equilibrium set

\[
E_k=\{(x_i,x_j):0\le x_i\le x_k,\ x_j=0\}.    \tag{7}
\]

Indeed, for \(x_j=0\), player \(i\) is indifferent and player \(j\)
continues exactly for \(x_i\le x_k\).  If \(x_j>0\), (6) makes player
\(i\) strictly prefer Quit, forcing \(x_i=1\), which is outside the small
neighbourhood.  Thus (7) also covers all partial supports; no regularity of
the original game is being assumed.

The component-index computation is correct.  Choose an isolating open
neighbourhood \(V\) of the compact segment (7).  Raise \(b_{k,i}\) by a
small \(\eta>0\), i.e. replace \(\delta_i=0\) by \(\delta_i=\eta\).
For sufficiently small \(\eta\), the isolating boundary remains
equilibrium-free.  Inside \(V\), the perturbed game has precisely:

* strict all Continue, index \(+1\); and
* one regular completely mixed coordination equilibrium near
  \((x_k,0)\), index \(-1\).

The local sum is zero, so perturbation invariance gives

\[
\operatorname{ind}(E_k)=0.                    \tag{8}
\]

If maximality makes (7) the complete Nash set, (8) again contradicts the
global sum \(+1\).

## 4. Exact external theorem required

The proof does not merely need Nash existence, generic oddness, or the
statement that regular isolated equilibria have signs.  It needs the
following complete degenerate-game package.

> **Finite-game equilibrium-component index theorem.**  For every finite
> normal-form game \(G\), its Nash set has finitely many connected
> components.  Each component \(C\) has an integer index
> \(\operatorname{ind}_G(C)\), defined as the local degree on an isolating
> neighbourhood, such that:
>
> 1. \(\sum_C\operatorname{ind}_G(C)=+1\);
> 2. a strict pure equilibrium has index \(+1\);
> 3. the regular completely mixed equilibrium of a strict two-action
>    coordination game has index \(-1\);
> 4. if an open set \(V\) has equilibrium-free boundary, then for every
>    sufficiently small payoff perturbation preserving that property, the
>    sum of the indices of the perturbed equilibria in \(V\) equals the
>    original local component-index sum; and
> 5. deleting or restoring actions that are strict non-best replies
>    throughout \(V\) preserves that local index.

This is the standard Nash-component index theory developed, for example, via
the Nash field in Klaus Ritzberger, *The theory of normal form games from the
differentiable viewpoint*, International Journal of Game Theory 23 (1994),
207--236, together with the global Poincare--Hopf index sum.  The
Kohlberg--Mertens equilibrium-correspondence structure theorem is another
route to the same degree statement, but the project transcription does not
present the five properties above as usable declarations.

## 5. Formalization boundary

Once the external index package exists, the quitting-game specialization is
elementary and finite:

1. identify product roots with mixed profiles of the binary finite root game;
2. prove (1) and use maximum absorption to localize every equilibrium;
3. reduce strict outsider coordinates;
4. enumerate the two local equilibrium geometries from (2); and
5. apply the global/local index identities.

The obstacle is therefore not partial-support case analysis.  It is the
absence from Lean/mathlib of the needed local-degree theory and its adapter
to Nash components.  `Literature/Simon2007.lean` contains only a `sorry`-marked
structure statement, and even that statement does not package component
index, local perturbation invariance, index signs, or the sum theorem.

## Final assessment

After replacing the faulty neighbourhood implication by (1), the claimed
consequence is sound:

\[
\boxed{
\text{a positive shrinking maximum-absorption exact-root ray cannot have }
|A|=2.}
\]

The conclusion includes the one-clock segment and all partial-support forms;
it uses no payoff genericity.  It should remain explicitly conditional on the
external finite-game component-index theorem until that substantial topology
is formalized or replaced by a checked finite-dimensional degree argument.
