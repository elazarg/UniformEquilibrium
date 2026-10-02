# Repaired stress cycle has no strict Simon Lyapunov potential

Author: `CHATGPT_EXTERNAL`

Independent review:
[Noether](../feedback/CHATGPT_EXTERNAL__REPAIRED_STRESS_CYCLE_NO_SIMON_LYAPUNOV__BY_CODEX_NOETHER.md),
with [packet recheck](../feedback/REPAIRED_STRESS_CYCLE_NO_SIMON_LYAPUNOV__BY_CODEX_NOETHER.md)

## Exact statement

Let the player set be `I=Fin 4`, with all displayed indices read cyclically
modulo four, and define the rational quitting rewards by

```text
{0}       (1,3,2,0)       {0,1}     (2,0,1,1)
{1}       (0,1,3,2)       {1,2}     (1,2,0,1)
{2}       (2,0,1,3)       {2,3}     (1,1,2,0)
{3}       (3,2,0,1)       {0,3}     (0,1,1,2)
                           {0,2}     (0,1,0,1)
                           {1,3}     (1,0,1,0)
{0,1,2}   (0,0,0,1)       {1,2,3}   (1,0,0,0)
{0,2,3}   (0,1,0,0)       {0,1,3}   (0,0,1,0)
{0,1,2,3} (0,0,0,0).
```

This is `RepairedFourPlayerStress.stressWeight` at parameters `(2,1)`.

For every `epsilon>0`, the full production correspondence
`QuittingSimonFiniteOrbitGraphAt reward epsilon` contains a finite directed
cycle of strictly positive total `QuittingSimonFiniteOrbitCost`. Consequently
there are no `Phi`, `c_0>0` satisfying

```text
Phi(y) <= Phi(x)-c_0*QuittingSimonFiniteOrbitCost(x,y)
```

on every production edge. In particular, the table admits no strict
`HasQuittingSimonFiniteCellLyapunovCertificate` whose cost-decrease
coefficient `c_0` is positive, at any positive tolerance. Constant-zero
instances of the underlying generic finite-cell predicate are not excluded.

At the rational tolerance `epsilon=1/2`, a four-edge rational cycle suffices.
For smaller tolerances, an exact finite subdivision of the same four phases
gives the cycle.

## Conjecture-facing change

This completely answers the candidate-level negative alternative explicitly
accepted by
[`../questions/SIMON_LYAPUNOV_CERTIFICATE.md`](../questions/SIMON_LYAPUNOV_CERTIFICATE.md).
It eliminates the repaired four-player stress table as a possible source of a
strict Simon Lyapunov certificate over the full production graph. It excludes
every potential, not merely one proposed finite-cell formula.

It does not construct a positive certificate or exclude certificates for all
finite quitting games.

## Definitions and strategy scope

The carrier is `QuittingSimonFiniteOrbitCarrier reward epsilon`: payoff
vectors within `epsilon` of the feasible convex hull and individually rational
up to the same tolerance. An edge
`QuittingSimonFEdgeAt reward epsilon tail current` consists of a product root
whose Bellman successor is `current` from continuation `tail` and which
satisfies every support-local approximate-Nash clause, including the clauses
for passive players. The graph stores the continuation first and its Bellman
predecessor second.

The cost is the symmetric Euclidean distance between the two carrier states.
Each root is a simultaneous independent product action. Terminal ties use the
reward of the displayed quitter coalition.

This is a statement about the full support-local production correspondence.
It is not a terminal, discounted, finite-horizon, or uniform-Nash claim and
does not itself quantify over arbitrary behavioral deviations.

## Source correspondence

Existing source data:

- `stressWeight`, `stressVertex_step`, `stressCirculation`, and
  `exists_stressCirculation_orbit`
  (`UniformEquilibrium/Quitting/Circulation/RepairedFourPlayerStressCirculation.lean`)
  give the table, vertices, phase identities, punishment floor, and arbitrarily
  fine support-perfect circulation;
- `quittingPunishmentValue_le_stressFloor` and
  `exists_uniformEquilibriumPayoff_stressWeight`
  (`UniformEquilibrium/Quitting/Circulation/UniformPayoffExamples.lean`) give
  the floor comparison and independently show that this table has a uniform-
  equilibrium payoff; and
- `isQuittingRootSupportApproxNash_rootOfHazard_of_isSupportPerfectRow` and
  `quittingRootSuccessorPayoff_rootOfHazard_eq_oneStageNext`
  (`UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationPath.lean`)
  are the row-level semantic adapters.

The production objects are `QuittingSimonFiniteOrbitCarrier`,
`QuittingSimonFEdgeAt`, and `QuittingSimonFiniteOrbitCost`
(`UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean`).
The specialized certificate is
`HasQuittingSimonFiniteCellLyapunovCertificate`
(`UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean`).
The generic finite-cell interface supplies
`HasFiniteCellLyapunovCertificate.exists_globalPotential`
(`MathUE/Topology/CompactEdgeBudgetedPrefixRelation.lean`).

The circulation and subdivision are not new. The new mathematical packaging
is their exact embedding into the full Simon production carrier and graph,
followed by the positive-cycle obstruction to every strict global potential
and hence to every positive-coefficient finite-cell certificate.

## Proof at rational tolerance one-half

Write `R^k=r({k})` and define

```text
v^0=(1,2,2,1),  v^1=(1,1,2,2),
v^2=(2,1,1,2),  v^3=(2,2,1,1).
```

Modulo four,

```text
v^k=(8R^k+4R^(k+1)+2R^(k+2)+R^(k+3))/15.          (1)
```

The coefficients in (1) are positive and sum to one, so every vertex is
exactly feasible. Every own singleton payoff is one, and
`quittingPunishmentValue_le_stressFloor` gives punishment floor at most one.
Every vertex coordinate is one or two, hence each `v^k` is exactly
individually rational and lies in the carrier at `epsilon=1/2`.

For each `k`, use the product root at which only player `k` may Quit, with
probability `1/2`. Then

```text
v^k=(1/2)R^k+(1/2)v^(k+1).                           (2)
```

The Quit-minus-Continue endpoint differences for players in cyclic positions
`k,k+1,k+2,k-1` are

```text
0,  -3/2,  -3/2,  1/2.                              (3)
```

The owner uses both actions and is exactly indifferent. Every other player
Continues surely, and its unused Quit action improves by at most `1/2`.
Thus all full support clauses hold. Equation (2) gives the four directed edges

```text
v^0 -> v^3 -> v^2 -> v^1 -> v^0.                    (4)
```

Every edge has Euclidean cost `sqrt(2)`. If a global potential and `c_0>0`
satisfied the strict cost inequality, summing it over (4) would give

```text
0 <= -4*c_0*sqrt(2),
```

a contradiction.

## Subdivision for every positive tolerance

Fix `epsilon>0`. Choose `N>=1` sufficiently large and put

```text
beta=2^(-1/N),  h=1-beta<=epsilon.
```

For every phase `k`, define

```text
x^k_m=(1-beta^m)R^k+beta^m v^(k+1),  0<=m<=N.       (5)
```

Then

```text
x^k_0=v^(k+1),
x^k_N=v^k,
x^k_(m+1)=hR^k+beta*x^k_m.                          (6)
```

For a microedge `m<N`, use the product root at which only `k` may Quit,
with probability `h`. Put `t=beta^m`. The four Quit-minus-Continue endpoint
differences are

```text
D_k     = 0,
D_(k+1) = beta-3+2*beta*t <= -3h,
D_(k+2) = beta-2          = -(1+h),
D_(k-1) = 1+h-2*beta*t    <= h.                     (7)
```

The last bound uses `m+1<=N`, so `beta*t>=beta^N=1/2`. Hence every passive
upper clause is at most `epsilon`, while the owner is exactly indifferent.

Every state in (5) lies on the segment from `v^(k+1)` to `v^k`; its
coordinates lie in `[1,2]`. It is exactly feasible and individually rational,
so it belongs to the carrier. Equations (6)--(7) therefore give `4N` full
production edges forming a closed cycle.

The microedges in each phase are collinear and monotone. Their total cost is
the endpoint distance `sqrt(2)`, so the subdivided cycle still has total cost
`4sqrt(2)>0`. The same telescope excludes a strict potential at every positive
tolerance.

## Boundary tests

- The unsubdivided four-edge cycle has passive Quit advantage exactly `1/2`.
  It is therefore not a witness at tolerances below `1/2`; subdivision is
  essential there.
- The terminal index `m=N` in (5) is a phase endpoint, not the tail of another
  microedge. The predecessor bound in (7) is applied only for `m<N`.
- A zero-cost self-loop would impose only `Phi(x)<=Phi(x)` and would not
  contradict a cost-weighted potential. The present cycle has exact positive
  total cost `4sqrt(2)`.
- Reversing the graph convention would reverse the displayed cycle but leave
  its closure and symmetric cost unchanged. The orientation in (4) matches
  the actual continuation-first production definition.

## Adapter and consumer

Equations (1)--(3), together with the named stress-floor and row-semantic
adapters, place the four rational witnesses directly in the production carrier
and graph. The positive-cost cycle then contradicts any global strict
potential. Finally, a `HasQuittingSimonFiniteCellLyapunovCertificate` with an
explicitly positive decrease coefficient feeds
`HasFiniteCellLyapunovCertificate.exists_globalPotential`, producing precisely
such a global potential. The cycle therefore excludes every strict
positive-coefficient instance requested by the question. It does not exclude
the vacuous constant-zero case permitted by the underlying generic predicate.

No stationarily-generated or instant-punishment branch exclusion and no
supplied Simon-necessity hypothesis is required: those belong to the positive
certificate route, whereas this packet falsifies the candidate before either
downstream condition is invoked.

## Lean handoff

The narrow first target is the rational `epsilon=1/2` theorem:

1. package membership of the four `v^k` in
   `QuittingSimonFiniteOrbitCarrier`;
2. package the four corresponding `QuittingSimonFEdgeAt` witnesses;
3. telescope a hypothetical positive-constant global potential around the
   cycle; and
4. compose with `HasFiniteCellLyapunovCertificate.exists_globalPotential`.

The stronger every-positive-tolerance algebraic subdivision should be a
separate theorem reusing the existing repaired-stress circulation data.

## Scope and nonclaims

This packet does not construct a Simon Lyapunov certificate, prove that every
quitting game lacks one, supply a terminal exploitability gap, or prove a new
uniform-equilibrium theorem. It excludes the repaired stress table, and its
natural cyclic circulation, from the strict-certificate route over the full
production graph.
