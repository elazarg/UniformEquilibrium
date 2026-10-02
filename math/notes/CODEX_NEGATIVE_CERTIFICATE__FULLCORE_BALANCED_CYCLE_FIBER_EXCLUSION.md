# Every fullCoreMatrix-normalized singleton table has a balanced-cycle uniform payoff

**Identity:** `CODEX_NEGATIVE_CERTIFICATE`  
**Status:** proved in exact ordinary mathematics; explicit
`BalancedSingletonCycleCertificate` data, not yet instantiated in Lean  
**Conjecture impact:** excludes the entire 48-dimensional family whose
normalized singleton matrix is `fullCoreMatrix`, including every positive-solo
baseline lift and every nonsingleton completion, from the Fin4 counterexample
search

## Question

The literal zero-diagonal realization of `fullCoreMatrix` is already excluded
by the checked zero-solo/all-Continue theorem.  Does lifting its singleton rows
by positive solo baselines produce a serious exact negative-certificate
family?

No.  The normalized matrix itself admits an exact balanced four-owner
singleton-flow cycle over `Q(sqrt(13))`.  The checked singleton mesh compiler
then makes the effect of arbitrary nonsingleton collisions tend to zero and
supplies a fixed uniform-equilibrium payoff.  Their magnitudes affect the
finite collision cap and hence the mesh required for a requested accuracy,
but they do not restrict the class or change the target.  The construction
works for every real baseline vector, not only positive baselines.

## Exact class

Let the players be `0,1,2,3`, and write the columns of `fullCoreMatrix` as

```text
C0 = ( 0,  1, -1, -1),
C1 = (-1,  0,  3,  1),
C2 = ( 1, -1,  0,  1),
C3 = ( 1,  1, -1,  0).
```

Fix an arbitrary baseline vector `s=(s0,s1,s2,s3)` and assume only

```text
r_i({j}) = s_i + Cj_i
```

for every pair of players `i,j`.  Because `Cj_j=0`, the baseline coordinate
is exactly the own singleton payoff `s_i=r_i({i})`.

All reward coordinates at coalitions of cardinality at least two are
arbitrary.  Equivalently,

```text
normalizedSoloMatrix r = fullCoreMatrix.
```

This is a 48-dimensional affine family.  A Fin4 quitting table has
`4*(2^4-1)=60` real reward coordinates.  There are four singleton coalitions,
so the singleton part has 16 coordinates.  The displayed condition fixes the
12 off-diagonal differences

```text
r_i({j})-r_i({i}) = Cj_i,   i != j,
```

and leaves the four own-singleton coordinates `s_i` free.  The 11 coalitions
of size at least two (`6+4+1`) contribute `11*4=44` wholly free coordinates.
Thus the dimension is `4+44=48`; the phrase “arbitrary nonsingleton
completion” means all of those 44 coordinates, not merely coordinates outside
the singleton owner row.

## Exact certificate

Put `t=sqrt(13)`.  Use owners `0,1,2,3` in that order, with hazards

```text
p0 = ( 1 + 5t)/54,
p1 = (19 + 7t)/138,
p2 = ( 1 +  t)/14,
p3 = (13 +  t)/78.
```

Define the four nonnegative excess values

```text
z0 = (0, (1+5t)/54, (11+t)/54, 0),
z1 = (0, 0, (19+7t)/46, (7+5t)/46),
z2 = ((3+t)/14, 0, 0, (1+t)/14),
z3 = ((13+t)/78, (13+7t)/78, 0, 0).
```

The coarse phase values are

```text
v0=s+z0, v1=s+z1, v2=s+z2, v3=s+z3.
```

Since `3<t<4`, every displayed hazard lies strictly between zero and one and
every excess coordinate is nonnegative.

### Exact arc identities

Direct expansion using only `t^2=13` gives

```text
z0 = p0 C0 + (1-p0) z1,
z1 = p1 C1 + (1-p1) z2,
z2 = p2 C2 + (1-p2) z3,
z3 = p3 C3 + (1-p3) z0.
```

Here is the complete nontrivial coordinate check.  It avoids delegating any
part of the proof to the numerical search that found the point.  Write
`qk=1-pk`.  For the first arc,

```text
q0*(7+5t)/46  = p0,
q0*(19+7t)/46 = (12+6t)/54,
```

so its last coordinate is zero and its third coordinate is
`-p0+(12+6t)/54=(11+t)/54`.  Its second coordinate is `p0`.
For the second arc,

```text
q1*(3+t)/14 = p1,
q1*(1+t)/14 = (2+8t)/138,
```

so its first coordinate is zero, its third is `3p1=(19+7t)/46`,
and its fourth is
`p1+(2+8t)/138=(7+5t)/46`.  For the third arc,

```text
q2*(13+7t)/78 = p2,
q2*(13+t)/78  = 1/7,
```

so its second coordinate is zero, its first is
`p2+1/7=(3+t)/14`, and its fourth is `p2`.  Finally,

```text
q3*(11+t)/54  = p3,
q3*(1+5t)/54  = 6t/78,
```

so the third coordinate is zero, the first is `p3`, and the second is
`p3+6t/78=(13+7t)/78`.  All omitted coordinates are visibly zero.  Each
displayed product follows by multiplying numerators and replacing `t^2` by
13; for example

```text
(53-5t)(7+5t) = 46(1+5t),
(13-t)(13+t)  = 156,
(65-t)(11+t)  = 54(13+t).
```

For a compact independent check, the equations reduce to

```text
p3(39p3^2-13p3+1)=0,
27p0=1248p3^2-221p3,
23p1=468p3^2-65p3,
 7p2=234p3^2-39p3,
```

and the selected positive solution is

```text
p3=(13+sqrt(13))/78.
```

Substituting `39p3^2-13p3+1=0` yields exactly the other three displayed
hazards.  Coordinatewise expansion then yields the four `z` rows above.

Adding the baseline vector to an arc preserves it:

```text
vk = pk (s+Ck) + (1-pk) v(k+1).
```

Thus these are literal singleton-reward Bellman arcs for every table in the
class.

### Active and floor fields

At phase `k`, both facts needed by the balanced compiler are immediate:

```text
vk_k = s_k = r_k({k}),
r_i({i}) = s_i <= vk_i  for every i.
```

The first equality is `zk_k=0`; the second inequality is nonnegativity of
every `zk_i`.

Every player faces a positive hazard from three different owners in each
cycle.  In particular the deleted-player opponent survival product is
strictly below one for every possible deviator.  This is the exact terminal
seam covering Never and arbitrarily late stopping rules.

## Theorem and unrestricted proof

For every real reward table in the exact class (the player and coalition
indexing types are finite, so the derived reward bound is finite), the vector

```text
v0 = (s0,
      s1+(1+5sqrt(13))/54,
      s2+(11+sqrt(13))/54,
      s3)
```

is a uniform-equilibrium payoff.

Indeed, the displayed owners, hazards, coarse values and initial phase `0`
satisfy every field of the checked structure
`BalancedSingletonCycleCertificate`:

* probability bounds follow from `3<sqrt(13)<4`;
* the four exact arc equations were proved above;
* active-owner equalities and every solo floor follow from the `z` table; and
* opponent divergence follows from the four distinct positive-hazard owners.

The reader-facing certificate derives its collision bound from the finite
reward table.  At subdivision scale `m`, each coarse singleton block is split
into equal-survival microphases.  A passive deviator can then create only its
own singleton or a pair collision with the active owner; the positive
collision surplus is multiplied by a micro-hazard.  The checked terminal
error is

```text
balancedSingletonCycleCollisionCap(r)
  * balancedSingletonCycleIntensityCap(certificate) / m,
```

which tends to zero while the terminal payoff remains exactly `v0`.
Strict deleted-player contraction upgrades the local inequalities to every
randomized history-dependent unilateral replacement, including the pure Never
policy and deviations with unbounded stopping support.  Finally
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` gives the
fixed target `v0` with the correct uniform-horizon quantifiers.

Spelled out, for every `epsilon>0` it supplies one behavioral profile and one
threshold such that, for every horizon beyond that threshold, the same profile
is an `epsilon`-Nash equilibrium against every behavioral unilateral policy
and every player's finite-average payoff is within `epsilon` of the single
displayed vector `v0`.  The profile may depend on `epsilon`; neither `v0` nor
the nonsingleton reward table may depend on the horizon.  This is exactly the
definition `StochasticGame.Game.IsUniformEquilibriumPayoff` in
`GameTheory/Stochastic/Uniform.lean`, not only a terminal-payoff or
bounded-clock assertion.

No sign or magnitude restriction is imposed on a nonsingleton reward.
Its magnitude is read only by the internally derived finite collision cap,
which can increase the mesh required for a requested accuracy; it does not
enter the coarse certificate or the target payoff.

## Exact search and boundary audit

This theorem answers all required screens for the lifted family at once.

* **Positive solos:** arbitrary `s_i>0` are allowed; the result is not the
  zero-solo disjunct.
* **No-pure-coalition escape:** a completion may be engineered to reject
  every pure stationary coalition, but it still has the balanced-cycle
  uniform payoff.  The coarse certificate and target never read a
  nonsingleton row; the compiler reads their magnitudes only to choose its
  collision-error cap and sufficiently fine mesh.
* **Stationary faces:** whether a particular completion has an easy stationary
  equilibrium is irrelevant to the whole-fibre exclusion.  Some simple
  completions do, so stationary face enumeration remains a mandatory early
  rejection screen for individual candidates.
* **Persistent bases and deadlines:** arbitrary completion can open or close
  these chambers, but neither can restore a positive gap after the displayed
  uniform payoff exists.
* **Pair and general periodic profiles:** the coarse cycle is an exact
  one-owner Bellman orbit; mesh subdivision is the executable approximation
  needed when arbitrary pair collisions make the unsubdivided orbit
  strategically unsafe.
* **Late clocks:** opponent divergence supplies strict contraction for every
  deviator and is part of the checked all-behavior consumer.
* **Boundary limits:** no hazard is zero or one.  The construction is a fixed
  interior coarse orbit and sends only the subdivision micro-hazards to zero.

A preliminary floating battery recovered the four hazards to six digits, but
the theorem uses only the exact quadratic certificate above.  No raw or
scale-normalized search score enters the proof.

## Source audit

The normalized matrix and its checked sign/LCP properties are in

```text
UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  FullSupportLCPSignBarrier.lean
```

Named declarations inspected include:

* `fullCoreMatrix` and `fullCoreMatrix_diagonal`;
* `normalizedSoloMatrix_fullCoreReward`;
* `fullCoreMatrix_standardQ` and `fullCoreMatrix_noHomogeneous`; and
* `fullCoreMatrix_not_exists_relabelledCyclicOpenSignSkeleton`.

The all-behavior mesh interface and consumer are in

```text
UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean
```

with declarations:

* `BalancedSingletonCycleCertificate`;
* `BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue`; and
* `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`.

That file imports
`UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`; its final consumer
uses the terminal uniformization chain already contained in that import graph.
The exact semantic definition inspected is
`StochasticGame.Game.IsUniformEquilibriumPayoff` in
`GameTheory/Stochastic/Uniform.lean`, and the unrestricted deviation
quantifier is exposed by `StochasticGame.Game.isεHorizonNash_iff` there.

The no-cyclic-open-sign theorem is not contradicted.  Its structure is only a
necessary sign skeleton for one particular cyclic-open-sign producer.  The
balanced orbit above uses nonuniform hazards and continuation excesses; it
does not supply that skeleton.

## Search consequence

Fixing a hard normalized singleton matrix is not enough to define a hard
behavioral counterexample family.  `fullCoreMatrix` itself has an explicit
balanced orbit, and collision mesh purification covers every nonsingleton
completion.  The completion can change the required mesh through the error
constant, but cannot change the displayed target or prevent convergence.

Any next normalized-matrix family should be screened first for feasibility of
the finite balanced-cycle equations, including nonuniform hazards, repeated
owners, and limiting two-scale versions.  Failure of a relabelled cyclic
open-sign skeleton is far too weak an exclusion.  Only a matrix surviving
those exact singleton-flow screens should be paired with semialgebraic
stationary, persistent, deadline and complementary-pair exclusions.

## Proved and unproved

Proved here:

* every table with normalized singleton matrix `fullCoreMatrix` has the fixed
  displayed uniform-equilibrium payoff;
* the claim covers arbitrary real solo baselines and all 44 nonsingleton
  coordinates; and
* the construction covers every behavioral deviation and late clock through
  the checked balanced singleton compiler.

Not proved here:

* a Lean instance of the four algebraic certificate rows;
* completeness of balanced singleton cycles for other matrices;
* exclusion of a normalized matrix with no such cycle; or
* the full Fin4 conjecture.
