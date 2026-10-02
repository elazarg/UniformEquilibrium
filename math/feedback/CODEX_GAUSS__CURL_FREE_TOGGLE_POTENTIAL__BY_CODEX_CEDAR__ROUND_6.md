# Sixth review: deadlock-core linear mixing

Reviewer: `CODEX_CEDAR`

Target: only Proposition 11 as used by, and Propositions 14--16 in Section 23
of
[`../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md).

Verdict: `VALID_AFTER_MINOR_ENDPOINT_REPAIR` as ordinary mathematics.  I
independently attempted to falsify the transformed-face theorem, the literal
13-player estimates, all sixteen complementarity supports, the degree
orientation, and the balanced-cycle reversal.  The stated conclusions
survive.  There is one omitted `beta = 1` subcase in the proof excluding
common-box playerwise certificates; the subcase has a short equality repair
given below.  More importantly for export, the refreshed production surface
now contains an arbitrary-coordinate-rectangle conditional-face producer.
Section 23 excludes only common boxes, so strict nonoverlap with that checked
producer remains open.  This review therefore supplies the requested second
mathematical falsification audit, but it does **not** clear the current export
blocker and supplies no Lean, production-adapter, or new consumer seal.

## Proposition 11 as used

The range--orthant argument is correct.  If the range of `A` were proper,
choose nonzero `y` perpendicular to it and take the lower `j`-face at a corner
when `y_j>0` and the upper face when `y_j<0`.  Every nonzero summand
`y_j (A G)_j` is then strictly positive, whereas `A G` belongs to the range of
`A`.  This contradicts `y dot A G=0`; hence the square map `A` is invertible.

For the clamped map `p -> clamp(p + lambda A G(p))`, a fixed point cannot lie
on a boundary face because the displayed sign points strictly inward.  At an
interior fixed point `A G=0`, and invertibility gives `G=0`, not merely a zero
of a projection.  In the application `0<alpha<beta<=1` and there are thirteen
players.  The interior root therefore has every hazard strictly between zero
and one.  It is jointly absorbing and every deleted-player opponent row
contracts.  The identities

`R_i=V_i` and `W_i+c_i V_i=V_i`

give exact endpoint Nash and the fixed successor target.  The named checked
corollaries
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
(`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`) cover every
unilateral behavioral deviation.  Proposition 11 and its literal reward
adapter remain ordinary mathematics, not checked declarations.

## Proposition 14: literal table and face estimates

The reindexing is consistent.  In the order `D={0,3,6,9}`, the core block is

```text
[ 0  3 -1  3
  2  0  1 -3
  2 -2  0 -1
 -1 -2  1  0 ].
```

Every dummy row has twelve positive off-diagonal entries and is removed at
the first normal layer.  The four displayed rows retain negative witnesses in
columns `2,3,1,0`, respectively, at every later layer.  Thus the normal core
is exactly `D`, and its normalized principal singleton matrix is the positive
scale `deadlockMatrix/10000`.  The ambient equality, reindexing, and scaling
are ordinary adapters.  The named source facts are
`deadlockMatrix_normalCore_eq_univ`
(`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockChargedReturn.lean`)
and `eq_zero_of_isDeadlockHomogeneousComplementary`
(`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean`).

The altered row bounds check exactly.  Singleton continuer rewards lie in
`[9997/10000,10003/10000]`; after adding the nine dummy columns, the four core
row sums are `14,9,8,7`, while a dummy row sum is `12`.  Hence every average
singleton weight is strictly greater than one.  The exact conditional
singleton-mass maximum is still

```text
16198260678656 / 1804483359485313 < 1/100.
```

Using `A=(P+P^2)^(-1)`, the identity
`(I+P)^(-1)=(1/2)(I-P+...+P^12)` gives row `l1` norm `13/2` and
`A 1=(1/2)1`.  Direct rational recomputation gives

```text
|A E|_infty <=
974157031319839814136010357980773 /
16547013791573166847229003906250000 < 59/1000,
```

with the note's positive slack

```text
2116782382977029850500872487977 /
16547013791573166847229003906250000.
```

Since `h_j` is `3/50` and `-3/50` on the two displayed faces, `A G` is
strictly above `1/1000` and below `-1/1000`, respectively.  I also recomputed
the mixed-blocker lower estimate

```text
20640001498501688382948756177069 /
2368317064126414895057678222656250000 > 0.
```

Thus Proposition 11 applies to the actual 13-player reward table.

The exclusion of every **common-box** playerwise certificate is valid after
one endpoint repair.  For either actual blocker, the two singleton weights
are both `10001/10000`, so swapping the lower and upper blocker probabilities
leaves the gap unchanged and contradicts opposite strict face signs.  For a
nonblocker on a box with `beta<1/11`, the diagonal gap `f_i(t)` is strictly
increasing.  For `1/11<=beta<1`, the weighted-odds calculation is legitimate,
and

`11(9997/10000)(1/10)-10003/10000=9937/100000>0`

makes `V_i` decrease as the selected nonblocker probability increases, while
the other terms weakly increase.  The own coordinate is absent.

The written odds proof does not cover its allowed endpoint `beta=1`, because
the odds are then infinite and the asserted strict monotonicity can fail.
The theorem nevertheless survives: hold the other eleven opponent
coordinates at one.  At least two opponents then Quit surely, so the
continuer singleton contribution and `V_i` are zero, `c_i=0`, and the gap is
independent of the selected nonblocker coordinate.  The selected lower- and
upper-face points have equal gaps, which already rules out a uniformly
positive lower face and a uniformly negative upper face.

The sure-exit audit also checks.  A singleton coalition is defeated by an
outsider joining for `1001/1000>10003/10000`.  For a coalition of size at
least two, stability would require

`x_i=0 => x_(i+1)=x_(i+2)=1`

and

`x_i=1 => not (x_(i+1)=x_(i+2)=1)`.

Every zero therefore begins `0110`, forcing a period-three word, while the
all-one word violates the second implication.  Such a word cannot close on
thirteen positions.  The same singleton joining deviation violates
`IsQuittingInstantNoJoin` for every owner, so
`isQuittingInstantNoJoin_of_works`
(`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`) excludes the
checked instant mechanism.

## Proposition 15: all supports and degree

For `Phi(x)=x^+-M x^-`, a preimage of `q` is exactly an `LCP(M,q)` solution
with LCP weight `w=x^-` and residual `z=x^+`.  On the orthant whose negative
support is `S`, the derivative has column `M(*,j)` for `j in S` and the
identity column otherwise.  The checked homogeneous-complementarity theorem
implies `Phi^(-1)(0)={0}`.  Positive homogeneity and compactness of the unit
sphere yield `|Phi(x)|>=eta|x|`, hence properness.

I solved all sixteen support systems at `q*=(1,1,2,1)`.  The feasible ones are
exactly

```text
S={}       : w=(),              z=(1,1,2,1),
S={1,3}    : w=(1/2,1/3),       z_(0,2)=(7/2,2/3),
S={1,2,3}  : w=(3/4,1/2,1/2),   z_0=17/4.
```

The four singleton systems are inconsistent.  The remaining infeasible
candidates are

```text
{0,1}: (-1/2,-1/3)       {0,2}: (-1,1)
{0,3}: (1,-1/3)          {1,2}: (1,-1)
{2,3}: (-1,2)            {0,1,2}: (-1,0,1)
{0,1,3}: (-7,4,-13/3)    {0,2,3}: (-8/5,-13/5,-6/5)
{0,1,2,3}: (-34/25,6/25,-47/25,-6/5).
```

The candidates containing a zero do not hide a boundary preimage because
they also contain a negative supported weight.  All three genuine preimages
are strictly complementary.  Their complementary-matrix determinants are
`1,-6,8`, so their local signs sum to `+1-1+1=1`.  Properness supplies one
large ball for the segment from `q*` to any prescribed `q`; homotopy
invariance preserves degree one, and nonzero degree gives an LCP solution.
Thus `deadlockMatrix` is standard Q.  Positive scaling and coordinate
reindexing preserve this property by rescaling the LCP weight and permuting
the equations.

## Proposition 16: compression and reverse lasso

The cycle-to-lasso reduction is sound.  A zero-hazard phase has current
coarse value equal to its successor and may be deleted.  A maximal run of one
owner composes to one singleton arc with survival equal to the product of the
run survivals.  Opponent divergence ensures that positive phases remain and
that at least two distinct owners remain; after compression every survival
lies in `(0,1)` and cyclic neighbors have distinct owners.

A dummy cannot own a remaining phase.  Relative to its own solo payoff, its
envy toward its own singleton is zero and toward every other owner is exactly
`1/10000`.  Cyclic unrolling is a convex combination with a strictly positive
off-owner coefficient (also forced directly by opponent divergence), which
contradicts that phase's active equality.

After restricting to `D`, subtracting the common solo baseline and scaling by
`10000`, the nonnegative clearances obey

`v_n=(1-s_n) deadlockMatrix(*,owner_n)+s_n v_(n+1)`.

Active equality gives `v_n(owner_n)=0`; since `s_n>0`, the owner coordinate
also gives `v_(n+1)(owner_n)=0`.  Reverse the cyclic phase order and use
incoming clearance `v_(n+1)` with survival `s_n`.  The next clearance is
exactly `v_n`, in the orientation required by
`ReducedIdealSingletonLasso.clearance_step`.  Nonnegativity of `v_n` makes
every opponent `max 0` clipping inactive.  The incoming owner clearance is
zero, so every local debt charge is zero and identically zero debt satisfies
`debt_step`.  This constructs a `ReducedIdealSingletonLasso` contradicting
the checked theorem `ReducedIdealSingletonLasso.debt_pos`
(`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean`).
The conclusion excludes the named `BalancedSingletonCycleCertificate`, not
all singleton-only behavioral languages.

## Remaining export and source issue

The refreshed checked theorem
`exists_uniformEquilibriumPayoff_of_conditionalFaceGap`
(`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGap.lean`)
accepts arbitrary coordinatewise lower and upper rectangles and a coordinate
permutation.  Proposition 14 proves only that no playerwise certificate exists
on a **common** box.  Therefore this review does not validate the claimed
strict nonoverlap with the current integrated stationary producer.

As a diagnostic only, I solved the literal stationary equations numerically
near the transformed root and tested infinitesimal coordinate dominance.  The
root is near `p_i=0.499005`, and both natural successor permutations have
scaled absolute-Jacobian spectral radius about `1.049975>1`; hence neither
admits the simplest sufficiently small diagonally-dominant rectangle.  This
is an experiment, not an exact exclusion of larger or nonlocal rectangles.
An exact arbitrary-rectangle exclusion, or an explicit rectangle certificate,
is still required before making a strict actual-data novelty claim.

## Sources inspected

- `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` and
  `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
  (`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`);
- `exists_uniformEquilibriumPayoff_of_conditionalFaceGap`
  (`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGap.lean`);
- `quittingFaceNumerator_eq_one_sub_continueMass_mul_conditionalFaceGap`
  (`UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`);
- `deadlockMatrix_normalCore_eq_univ`
  (`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockChargedReturn.lean`);
- `eq_zero_of_isDeadlockHomogeneousComplementary` and
  `ReducedIdealSingletonLasso.debt_pos`
  (`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean`);
- `BalancedSingletonCycleCertificate`
  (`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`);
- `idealSingletonClearance` and `idealSingletonDebt`
  (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/IdealSingletonCapDebtLasso.lean`); and
- `isQuittingInstantNoJoin_of_works`
  (`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`).

