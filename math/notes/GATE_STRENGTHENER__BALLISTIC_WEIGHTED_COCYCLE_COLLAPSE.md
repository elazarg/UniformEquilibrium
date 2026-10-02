# Ballistic weighted-cocycle collapse

## Status

This note records a corrected and strengthened **ordinary-mathematics theorem**
about normalized ballistic chains.  It is not exported and is not claimed to
be checked in Lean.

The result compresses every uniformly interior normalized ballistic chain to
one positive solution of a finite augmented-kernel system.  It does not lift
that solution to an absolute quitting root, payoff/cap pair, Nash--Bellman
block, behavioral chronology, or uniform-equilibrium consumer.

## Normalized data

Let `I` be finite.  Let `M,J : I x I -> R`, and fix `0 < eta <= 1`.  Suppose

\[
(\lambda_n,\Lambda_n,\rho_n)
\in\Delta(I)\times\Delta(I)\times[\eta,1]
\qquad(n\ge0)
\]

satisfy the renewal equations

\[
\Lambda_n
=\rho_n\lambda_n+(1-\rho_n)\Lambda_{n+1}
\tag{R}
\]

and coordinate complementarity

\[
\lambda_{n,i}
\bigl(M\Lambda_n+\rho_nJ\lambda_n\bigr)_i=0
\qquad(i\in I).
\tag{C}
\]

The usual ballistic feasibility inequality

\[
M\Lambda_n+\rho_nJ\lambda_n\le0
\]

is not needed for the theorem.  Only (R) and (C) are used.

## Theorem

At least one of the following holds:

1. there are a player `i` and a strict subsequence `n_k` such that

   \[
   \lambda_{n_k,i}\longrightarrow0;
   \tag{B}
   \]

2. there exist

   \[
   r\in[\eta,1],
   \qquad
   y\in\Delta(I),
   \qquad
   y_i>0\quad(i\in I),
   \]

   satisfying

   \[
   \boxed{(M+rJ)y=0.}
   \tag{F}
   \]

The alternatives are inclusive, not exclusive.  The correct logical form is

\[
\neg(B)\Longrightarrow(F).
\]

Moreover, `r` in the second arm may be chosen in the asymptotic range

\[
r\in[\liminf_n\rho_n,\limsup_n\rho_n],
\tag{1}
\]

and `y` lies in

\[
\bigcap_{N\ge0}
\overline{\operatorname{conv}}
\{\Lambda_n:n\ge N\}.
\tag{2}
\]

In fact, `y` may be chosen in the stronger common asymptotic hull

\[
\boxed{
y\in
\bigcap_{N\ge0}\overline{\operatorname{conv}}\{\lambda_n:n\ge N\}
\ \cap\
\bigcap_{N\ge0}\overline{\operatorname{conv}}\{\Lambda_n:n\ge N\}.}
\tag{2'}
\]

In finite dimension, each factor is the closed convex hull of the
corresponding tail cluster set.

The triple `(y,y,r)` is an exact fixed state of the ambient normalized
ballistic relation: renewal is

\[
y=ry+(1-r)y,
\]

and its work vector is zero by (F).

## Eventual-interior reduction

The negation of (B) does not imply an interior lower bound at every original
index.  It implies the eventual statement

\[
\exists N,\delta>0\quad
\forall n\ge N,\forall i\in I,qquad
\lambda_{n,i}\ge\delta.
\tag{3}
\]

Indeed, otherwise choose increasingly late indices with
`min_i lambda_{n,i}->0`; finiteness of `I` freezes one coordinate along a
subsequence.  Delete the finite prefix through `N` and relabel.  Then (C)
gives

\[
M\Lambda_n+\rho_nJ\lambda_n=0
\tag{4}
\]

at every retained date, while (R) and `rho_n>=eta` give the uniform tail floor

\[
\Lambda_{n,i}\ge\rho_n\lambda_{n,i}\ge\eta\delta.
\tag{5}
\]

## Quantitative cofinal-block certificate

Fix a cutoff `N_0` and an error `epsilon>0`.  Compactness of the simplex gives
indices

\[
N_0\le a<b,
\qquad
\|\Lambda_a-\Lambda_b\|\le\varepsilon.
\tag{6}
\]

They may be chosen cofinally, with `a->infinity` as `epsilon->0`.

For the fixed-state conclusion alone, one retained `rho_n=1` gives
`Lambda_n=lambda_n` and therefore (F) with `r=1`.  To obtain the common
asymptotic-hull conclusion (2'), a single finite occurrence is insufficient.
Split instead as follows:

- if `rho_n=1` at infinitely many cofinal dates, take a convergent subsequence
  of those dates; its common limit lies in both asymptotic hulls;
- if this occurs only finitely often, enlarge the cutoff past the last such
  date and use the weighted construction below.

Thus in the second case put

\[
g_n=1-\rho_n>0,
\qquad
L=b-a,
\]

\[
q=\left(\prod_{n=a}^{b-1}g_n\right)^{1/L},
\qquad
r=1-q,
\tag{7}
\]

and define positive cocycle weights by

\[
\alpha_a=1,
\qquad
\alpha_{n+1}=\frac{\alpha_ng_n}{q}.
\tag{8}
\]

The geometric-mean choice gives `alpha_b=1`.  Define

\[
A=\sum_{n=a}^{b-1}\alpha_n\Lambda_n,
\qquad
B=\sum_{n=a}^{b-1}\alpha_n\rho_n\lambda_n,
\qquad
Z=\sum_{n=a}^{b-1}\alpha_n.
\tag{9}
\]

Multiplying (R) by `alpha_n` and summing yields

\[
B=rA+q(\Lambda_a-\Lambda_b).
\tag{10}
\]

Multiplying (4) by the same weights and summing yields

\[
MA+JB=0.
\tag{11}
\]

Set

\[
y_{a,b}=A/Z,
\qquad
e_{a,b}=\frac qZ(\Lambda_a-\Lambda_b).
\tag{12}
\]

Then

\[
y_{a,b}\in\Delta(I),
\qquad
y_{a,b,i}\ge\eta\delta,
\tag{13}
\]

and the exact residual identity is

\[
\boxed{
(M+rJ)y_{a,b}=-Je_{a,b}.}
\tag{14}
\]

For any fixed norm and its induced operator norm,

\[
\boxed{
\|(M+rJ)y_{a,b}\|
\le
\|J\|\,\|\Lambda_a-\Lambda_b\|
\le
\|J\|\varepsilon.}
\tag{15}
\]

This is the finite certificate hidden by the compact limit.

There are two additional exact provenance facts.  Summing the coordinates in
(10) gives

\[
\boxed{
r=
\frac{\sum_{n=a}^{b-1}\alpha_n\rho_n}
     {\sum_{n=a}^{b-1}\alpha_n}.}
\tag{16}
\]

Thus `r` is a convex weighted average of the actual ratios in the selected
block.  Also

\[
z_{a,b}=\frac{B}{rZ}\in\Delta(I)
\]

is a convex weighted average of the current directions and satisfies

\[
z_{a,b}-y_{a,b}=e_{a,b}/r,
\qquad
\|z_{a,b}-y_{a,b}\|\le\varepsilon/\eta.
\tag{17}
\]

Hence the weighted current and tail directions coalesce quantitatively.
Moreover, `z_{a,b}` is a convex combination of current directions
`lambda_n`, while `y_{a,b}` is a convex combination of tail directions
`Lambda_n`, all from the same contiguous block.

Choose cofinal blocks with endpoint error tending to zero.  Compactness gives
a convergent subsequence of `(r,y)`.  Equation (17) forces the corresponding
`z` sequence to have the same limit. Equations (13)--(16) pass to the limit,
giving (F), the positive coordinate floor, (1), and the common convex-hull
statement (2').

## Inclusive-alternative falsifier

The alternatives cannot be stated as `Xor`.  Take two players,

\[
M=J=0,
\qquad
\rho_n=1,
\]

and

\[
\lambda_n=\Lambda_n=
\left(\frac1{n+2},1-\frac1{n+2}\right).
\]

Renewal and complementarity hold.  The first coordinate tends to zero, so
(B) holds, while every positive simplex vector and every ratio give an
ambient fixed state.  Thus (F) holds as well.

## Source-compatible Fin4 adapter

The normalized theorem has a checked conditional source entrance.

Start with one actual
`FinFourStrictRayForwardExactCapTail` and assume:

1. its limiting binding set is all four players; and
2. all four finite current normalized hazards are eventually positive.

The theorem

```text
eventually_renewalRatio_ge_pos_of_fullBinding_of_eventually_all_currentHazard_pos
```

in
`Research/Quitting/FinFourProducerAtlas/FullBindingPointwiseSupportBallistic.lean`
produces an eventual lower ratio bound `eta>0` on the same strict ray.  Then

```text
nonempty_ballisticNormalizedOmegaChain_of_fullBinding_of_eventually_all_currentHazard_pos
```

in
`Research/Quitting/FinFourProducerAtlas/BallisticNormalizedOmegaChain.lean`
produces a source-compatible bi-infinite normalized chain.  On its forward
half, take

\[
M=\operatorname{normalizedSoloMatrix}(r),
\qquad
J=\operatorname{quittingCollisionMatrix}(r).
\]

Its checked `renewal` and `current_work_eq_zero` declarations supply (R) and
(C).  The theorem therefore returns

\[
\boxed{
\text{an omega-current coordinate tending to zero}
\quad\text{or}\quad
\exists r,y>0\;(M+rJ)y=0.}
\tag{18}
\]

This source compatibility is exact at the normalized level:

* `source_current_tendsto` lets each fixed omega coordinate be approximated by
  strict actual dates of the same ray;
* `sourceFiniteWindow_tendsto` makes every fixed finite omega window the limit
  of literal consecutive windows of that ray; and
* a standard diagonal selection therefore approximates the successive finite
  cocycle certificates by same-source windows.

It does not make the averaged fixed state an actual state at one source date.
The first arm of (18) likewise gives a coordinate approaching zero, not a
coordinate equal to zero infinitely often.

## Regression and algebraic boundary

For Fin4, the fixed-state condition is the finite semialgebraic system

\[
r\in[\eta,1],
\quad
y_i>0,
\quad
\sum_i y_i=1,
\quad
(M+rJ)y=0.
\tag{19}
\]

Necessarily

\[
\det(M+rJ)=0,
\]

a polynomial equation of degree at most four in `r`, together with a positive
kernel-vector condition.  Therefore a particular reward table can be screened
exactly for (19).

The regression in
`Research/Quitting/BallisticNormalizedSelectedChainRegression.lean` shows why
(19) is not itself a hard-residual contradiction.  Its solo matrix has no
homogeneous simplex solution and carries the paired-singleton hard matrix
properties.  Its normalized relation nevertheless has:

* a uniformly interior, aperiodic selected chain with `rho=1/2`; and
* the uniform positive fixed state satisfying

  \[
  (M+\tfrac12J)y=0.
  \]

That object is matrix-level, not an actual positive-minimum quitting ray.  It
is a decisive falsifier of any argument using only hard solo-matrix geometry
or aperiodicity to exclude the augmented kernel.

## Exact nonclaims and remaining consumer

The theorem does **not** provide:

* an absolute hazard scale for `y`;
* an exact product root against an absolute cap vector;
* an actual semantic pair realizing `(y,y,r)`;
* an exact Nash--Bellman seam or returned block;
* a terminal approximate Nash profile;
* a uniform-equilibrium payoff;
* a renewable finite rank; or
* a positive-gap counterexample.

Scaling `y` to a small product hazard cancels only the first-order normalized
endpoint equations.  Exact product behavior leaves quadratic errors, and no
implicit-function, cap-matching, source-return, or chronology theorem is
available to remove them.

The boundary arm also lacks a consumer: asymptotic vanishing of a normalized
current coordinate is not literal omission and is not automatically a debt-
support drop.

The remaining source-level question is therefore:

> Does a positive-minimum Fin4 strict ray carrying the augmented fixed state
> admit an exact source-faithful semantic lift/return, or is the augmented
> kernel incompatible with the additional cap, law, and collision provenance?

Until that is answered, the weighted-cocycle theorem is a complete normalized
reduction and no more.

## Lean-facing declarations

A generic formalization should separate the finite algebra from compactness:

```text
ballisticCocycleBlock_identity
ballisticCocycleBlock_ratio_eq_weightedAverage
ballisticCocycleBlock_residual_le_endpointDistance

ballisticRenewal_exists_boundarySubseq_or_interiorAugmentedKernel
```

The last theorem must return an inclusive disjunction, not `Xor`, and must
shift past the eventual-interior cutoff before constructing weights.

The Fin4 adapter should be stated only at normalized level:

```text
FinFourBallisticNormalizedOmegaChain.nonempty_boundaryCurrent_or_fixedState
```

It should retain cofinal block approximants and source-window provenance but
must not assert `HasAbsoluteNashBellmanLift`.
