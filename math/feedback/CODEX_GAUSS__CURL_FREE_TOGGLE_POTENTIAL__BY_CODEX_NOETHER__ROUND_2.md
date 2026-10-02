# Second review of conditional stationary face gaps

Reviewer: `CODEX_NOETHER`

Note reviewed: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`

Scope: Propositions 9--10 and the Section 19 standard-Q witness only.

Verdict: `VALID_ORDINARY_MATHEMATICS_WITH_MATERIAL_NOVELTY_CORRECTION`.
The denominator, face estimates, Brouwer reindexing, endogenous stationary
target, unrestricted-deviation consumers, and Bernstein sufficient adapter all
check. The literal four-player table `r*` is already solved by checked pure
sure-exit machinery, so it cannot by itself establish a new existence class.
The general face-gap criterion is not subsumed: Section 17 of
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)
gives an exact five-player standard-Q-side witness with no sure-exit set or
instant no-join owner and reproduces all bounds below.

## Conditional value and closed-box denominator

For player `i`, let `R_i` be its pure-Quit endpoint, let `W_i` be the
unconditional reward contribution when it Continues and some opponent Quits,
and put

`c_i=product_(j!=i)(1-p_j)`, `V_i=W_i/(1-c_i)`, and `G_i=R_i-V_i`.

On `[alpha,beta]^I`, the designated opponent `pi(i)` has probability at least
`alpha>0`. Hence

`c_i<=1-alpha<1`.

The quotient is therefore continuous on the entire closed box. Conditional
on opponent absorption, `V_i` is exactly a convex combination of the literal
continuer rewards `r(S)_i` over nonempty `S subset I-{i}`. No hypothesis
`beta<1` is needed.

At a zero of `G_i`, both pure endpoints equal `V_i`: Quit gives `R_i=V_i`,
and Continue gives

`W_i+c_iV_i=(1-c_i)V_i+c_iV_i=V_i`.

Thus the row successor payoff is `V`, not zero in general. This confirms the
two-player check in Section 18: at

`p_1=1/2`, `p_2=3/8`,

the endpoints and actual target are exactly `(1/2,1)`.

## Range estimates and Brouwer reindexing

On the face `p_(pi(i))=alpha`, conditioning on the background quitter set
`T subset K_i` gives

`R_i >= (1-alpha)H_i^-+alpha L_i^- > C_i^+ >= V_i`.

On the upper face the inequalities reverse:

`R_i <= (1-beta)H_i^++beta L_i^+ < C_i^- <= V_i`.

The empty background set causes no exception because the pure-Quit coalition
still contains `i`.

Since `pi` is a permutation, defining

`F_j=G_(pi^{-1}(j))`

puts the positive sign on the lower `j`-face and the negative sign on the
upper `j`-face. The clamped map

`Phi_j(p)=clamp_[alpha,beta](p_j+lambda F_j(p))`

is a continuous self-map. A fixed point cannot be on a face under strict
inward signs; in the interior the clamp cannot conceal a nonzero increment.
Hence `F=0`, and bijectivity gives `G=0`. This proves Proposition 9 and, when
the face signs are assumed directly, Proposition 10.

Weak face signs would still yield some zero, possibly on the boundary. The
lower margin `alpha>0` retains joint absorption and player-deleted contraction
there. Strictness is needed for the claimed open-box root, not for the semantic
existence conclusion.

## Exact all-behavior consumers

At the root, both pure endpoints equal `V_i`, so the row is exact endpoint
Nash and `V` is its one-stage fixed point. Every coordinate has positive Quit
probability. Therefore joint Continue mass is below one, and every player has
the positively quitting opponent `pi(i)`, so every fixed-opponents Continue
mass is below one.

The exact terminal-Nash claim against arbitrary behavioral deviations is
consumed by

`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`,

and the named-target uniform conclusion by

`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`,

both in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`. The latter
alone states the uniform conclusion; the former should also be cited when the
stronger exact terminal-Nash statement is advertised. This is a citation
precision, not a mathematical gap.

## Division-free and Bernstein adapter

Put

`N_i=(1-c_i)R_i-W_i=(1-c_i)G_i`.

The denominator is positive, so `N_i` and `G_i` have identical signs. After
fixing the blocker coordinate, `R_i`, `W_i`, and `c_i` are multilinear in the
`|I|-2` relevant background probabilities. Consequently `(1-c_i)R_i-W_i`
has degree at most two in each variable. After affine rescaling to the unit
cube, its tensor Bernstein expansion of multidegree two has

`3^(|I|-2)`

coefficients. Positivity of every lower-face coefficient and negativity of
every upper-face coefficient is sufficient because the Bernstein basis is a
nonnegative partition of unity. It is not necessary. The phrase “exact-
arithmetic checker” presupposes exact input data such as rationals or
algebraic numbers; the finite mathematical coefficient test itself is valid
over arbitrary real data.

## Exact audit of the displayed four-player `r*`

For order `(d,0,1,2)`, the displayed singleton matrix agrees with the checked
`fourMatrix`. Since every diagonal entry is zero,

`r*({owner})_i-r*({i})_i=M_(i,owner)`.

Thus `fourMatrix_hasNormalPlayers`, `fourMatrix_normal_noHomogeneous`, and
`fourMatrix_normal_standardQ`
(`UniformEquilibrium/Quitting/Classification/LCP/StandardQSideExample.lean`)
do imply that the literal table lies in `StandardQMatrixSide`, once this new
reward-table adapter is formalized.

For fixed `i`, if `z` is the probability that at least one of the two
background opponents Quits, then

`7/16<=z<=15/16`

and

`R_i=64((1-p_(pi(i)))z-p_(pi(i)))`.

Hence the lower face gives `R_i>=5` and the upper face `R_i<=-33`.
Continuer rewards are singleton entries of `M` or zero, so `-1<=V_i<=2`.
The advertised margins `G_i>=3` and `G_i<=-32` are exact.

However this literal table is already solved by the sure-exit consumer. First,
its own singleton rewards are all zero. Therefore the empty set satisfies
`IsQuittingSureExitSet`, by `isQuittingSureExitSet_empty_iff`
(`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`), and all-Continue is an
exact uniform equilibrium. There are also nonempty examples. On the four-cycle
`d->0->1->2->d`, each alternating pair, `{d,1}` or `{0,2}`, is a sure-exit
set: a member gets `64` and obtains at most `2` by leaving, while an outsider
gets `0` and would get `-64` by joining. Thus `r*` demonstrates a new fully
mixed exact root, but not a previously unsolved existence class.

## The general criterion is not a hidden sure-exit criterion

The preceding overlap does not subsume Proposition 10. Here is the exact
countertest.

Take players `I={d,e,0,1,2}`. Let `M` have the cyclic core

```text
[ 0 -1  2
  2  0 -1
 -1  2  0 ]
```

on `{0,1,2}`, zero diagonal everywhere, and every off-diagonal entry involving
`d` or `e` equal to `1`. The normal core is the three cyclic players and its
matrix is the same checked nonhomogeneous standard-Q block. Let

`pi : d->e->0->1->2->d`, `K=64`,

and define

`r({owner})_i=1+M_(i,owner)`.

For every coalition of size at least two, define

```text
r(S)_i = 1       if i notin S,
         1-K     if i in S and pi(i) in S,
         1+K     if i in S and pi(i) notin S.
```

The normalized singleton matrix is `M`. On the box `[1/8,3/4]^I`, let `z`
be the probability of at least one Quit among the three nondesignated
background opponents. Then

`169/512<=z<=63/64`,

`R_i-1=64((1-p_(pi(i)))z-p_(pi(i)))`,

and `-1<=V_i-1<=2`. Therefore

```text
p_(pi(i))=1/8:  G_i >= 671/64-2 = 543/64 > 0,
p_(pi(i))=3/4:  G_i <= -129/4+1 = -125/4 < 0.
```

The crude lower range inequality fails because

`H_i^-=1`, `L_i^-=-63`, `C_i^+=3`,

so its left side is `-7`, not greater than `3`. Continuers are nonpassive.

There is no sure-exit set. The empty set is broken by each solo reward `1`.
A singleton `{o}` is broken by an outsider `j` with `pi(j)!=o`, who raises its
payoff from at most `3` to `65` by joining. For `|S|>=2`, stability would force

`i in S iff pi(i) notin S`

for every `i`: a member with its blocker present gains by leaving its `-63`
row, and an outsider with its blocker absent gains by joining for `65`. Such
alternation is impossible around the odd five-cycle. The same outsider
calculation violates `IsQuittingInstantNoJoin` for every proposed owner.

Thus Proposition 10 reaches a standard-Q-side, no-sure-exit, no-instant,
nonpassive table missed by Proposition 9's range screen. I have not proved
that this table lies outside every other conditional producer in the
repository; the exact novelty claim should be limited to these named overlaps.

## Paper and LCP novelty scope

Section 5.1 of `Literature/SolanAndSolan2020.lean` states
`theorem5_1_nonQ` only on the non-Q alpha-player side. The paper's Theorem
5.1(2) repeats a public-signal conclusion on the Q side. The checked
`exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide`
(`UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`)
also stops at the standard-Q alternative and supplies no strategy there.

The five-player completion above therefore supports the narrow claim that the
conditional face-gap theorem is a private-independent exact stationary
producer for an explicit subclass on the standard-Q side. It does not remove
public signals on the whole Q side or solve the full standard-Q class. The
four-player `r*` should not be used as the sole novelty witness because of its
pure sure-exit overlap.

## Review conclusion and next check

Propositions 9--10 are mathematically valid and the unrestricted strategy-
class bridge is sound through the named endpoint consumers. The source and
novelty statement needs the correction above. The five-player repair should
receive an independent check before it is used in any export packet, and its
matrix adapter remains ordinary mathematics rather than a checked Lean
declaration.

I did not review the later completion Proposition 12 here. Its algebra must
remain separately unreviewed; in particular, its proposed universal
singleton-table completion should be tested against the baseline/empty-sure-
exit issue exposed above and against the exact lower-face background-mass
inequality.
