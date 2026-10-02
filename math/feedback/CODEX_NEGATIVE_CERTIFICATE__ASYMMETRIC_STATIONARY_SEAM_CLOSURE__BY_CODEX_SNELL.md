# Review of the integral-tournament balanced-singleton closure

Reviewer: `CODEX_SNELL`

Date: 2026-09-03

Reviewed note:
`notes/CODEX_NEGATIVE_CERTIFICATE__ASYMMETRIC_STATIONARY_SEAM_CLOSURE.md`,
SHA-256
`686602115968e0f603fe9fa28df4dfed591262c3db6d835cf39009cf2380ef9b`.

## Verdict

**PASS with two narrow presentation/scope corrections.**  The period-three
balanced-singleton certificate is correct for every four-vertex integral
tournament with a unit outgoing edge at every vertex.  It is independent of
the four solo baselines and of every nonsingleton reward coordinate, and the
checked reader-facing compiler covers unrestricted behavioral deviations and
uniform finite-horizon delivery.

The two corrections are:

1. the construction should explicitly choose the certificate's required
   `initial : Fin 3` field (any phase, for example `0`, works); and
2. “every integral-tournament standard-Q source closes by the certificate”
   should be read as the **no-sink/unit-outneighbor branch certified standard
   Q by `isStandardQ_tournamentSkewMatrix`**.  If the outgoing-edge hypothesis
   fails, the displayed balanced certificate is not produced; that branch is
   instead eliminated by the homogeneous simplex witness in
   `isStandardQ_or_singletonLCPFeasible_of_isIntegralTournament`.  The cited
   dichotomy alone does not say that an abstract `IsStandardQ` hypothesis is
   incompatible with the homogeneous branch, since its disjunction is not
   stated exclusively.  This does not affect the claimed exhaustion of the
   integral-tournament negative-search route.

No mathematical objection remains after those qualifications.

## Claim checked

Let `A` be a `0/1` tournament on four vertices, let `t>1`, and let

```text
M(i,j)=t A(i,j)-A(j,i).
```

Assume every vertex has an outgoing edge.  For every quitting reward table
whose normalized singleton matrix is

```text
r_i({j})-r_i({i})=M(i,j),
```

the note claims an explicit `BalancedSingletonCycleCertificate` with three
distinct owners, common hazard `1-1/t`, arbitrary solo baselines, and no
restriction on nonsingleton rewards.  Its checked consumer then gives a
uniform-equilibrium payoff.

## 1. Tournament combinatorics

Write the four positive integral outdegrees in nondecreasing order.  They sum
to six and lie in `{1,2,3}`, so the only possibilities are

```text
(1,1,1,3),  (1,1,2,2).
```

In the first case the degree-three vertex `d` beats all other vertices.  Each
remaining vertex has exactly one win, necessarily inside the remaining
triple; that triple is a directed 3-cycle.

In the second case, orient the edge between the degree-two vertices as
`c -> d`.  Since `d` already loses to `c`, its other two required wins are
against the two degree-one vertices.  Vertex `c` has exactly one win among
those two.  The two degree-one constraints then force the triple obtained by
removing `d` to be a directed cycle.  Thus in both cases there are distinct
`o0,o1,o2,d` with

```text
A(o1,o0)=A(o2,o1)=A(o0,o2)=1
```

and `d` beating at least two owners.

As a redundant falsification check, I enumerated all `2^6=64` labelled
four-vertex tournaments.  Exactly 32 have no sink, and all 32 admit the
claimed ordered cycle plus outsider witness; there was no exceptional
orientation.  The proof above, not the enumeration, establishes the claim.

## 2. Exact cyclic recurrence

Put

```text
s=1/t,  h=1-s.
```

Then `0<s<1` and `0<h<1`.  For coordinate `ok`, the proposed owner tail is

```text
T_j(ok)=t  when j=k-1 mod 3,
T_j(ok)=0  otherwise.
```

Using the displayed cycle orientation, its three equations are precisely

```text
0 = 0  + s*0,
0 = -1 + s*t,
t = t  + s*0.
```

Hence

```text
T_j(ok)=M(ok,oj)+s T_(j+1)(ok).
```

For the outsider, write `x_j=M(d,oj)` and

```text
T_j(d)=(x_j+s x_(j+1)+s^2 x_(j+2))/(1-s^3).
```

Subtracting `s T_(j+1)(d)` cancels the shifted terms and leaves `x_j`, so the
same recurrence holds exactly.  Since `d` beats at least two owners, at least
two `x_j` equal `t`; the remaining value is `t` or `-1`.  In the only
nontrivial case the three cyclic numerators are

```text
1/t,  t,  t+1-1/t^2,
```

all positive for `t>1`, while `1-s^3>0`.  Thus every coordinate of every
`T_j` is nonnegative.

## 3. Baselines, arc, active equality, and floors

Let `b_i=r_i({i})` be arbitrary and set

```text
v_j(i)=b_i+h T_j(i).
```

The normalized-matrix convention gives

```text
r_i({oj})=b_i+M(i,oj).
```

Since `h+s=1`, the recurrence yields, coordinatewise,

```text
h r({oj})+s v_(j+1)
= h(b+M(*,oj))+s(b+h T_(j+1))
= b+h(M(*,oj)+s T_(j+1))
= v_j.
```

This is exactly the orientation of
`BalancedSingletonCycleCertificate.arc`, because
`quittingSingletonArcPayoff h root next = h*root+(1-h)*next` and
`1-h=s`.  There is no hidden restriction on `b`.

For the active owner `oj`, `T_j(oj)=0`, hence
`v_j(oj)=b_oj=r_oj({oj})`.  Since all tails are nonnegative and `h>0`, every
coordinate also satisfies `b_i<=v_j(i)`.  These are exactly the `active` and
`soloFloor` fields, including the outsider coordinate.

## 4. Probability and deleted-opponent audit

The constant hazard `h` satisfies the certificate's `0<=hazard<1` fields.
Each of the three owners encounters two positive-hazard phases owned by
somebody else, and `d` encounters all three.  Thus

```text
forall i, exists phase, i != owner(phase) and 0<h,
```

which is precisely `opponentDivergence`.  The checked theorem
`BalancedSingletonCycleCertificate.opponent_product_lt_one` then supplies the
strict deleted-opponent contraction for every player; no owner is omitted.

The certificate structure also requires an initial phase.  This datum is not
named in the prose construction, but choosing any element of `Fin 3` fills it
without changing another equation.  The resulting uniform payoff is the
corresponding `v_initial`.

## 5. Arbitrary nonsingleton rewards and unrestricted deviations

The reader-facing certificate intentionally contains no nonsingleton-reward
hypothesis.  `BalancedSingletonCycleCertificate.toWithBounds` derives

```text
collisionBound = 2*quittingRewardBound reward
```

and verifies every singleton-owner collision inequality against that finite
bound.  Therefore arbitrary finite nonsingleton rewards affect only the
explicit mesh error constant; they do not enter the arc, active, floor, or
contraction equations.

Finally,
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` calls the
checked singleton-arc compiler.  Its terminal and finite-horizon estimates
are for the production quitting game and unrestricted behavioral unilateral
deviations, not only pure clocks or stationary deviations.  The certificate
therefore proves the claimed uniform-equilibrium payoff; no separate
stationary endpoint argument or nonuniform reward bound is being smuggled in.

## 6. Declarations and files inspected

* `tournamentSkewMatrix`, `FractionalTournamentHasUnitOutneighbor`, and
  `not_singletonLCPFeasible_tournamentSkewMatrix` in
  `MathUE/LinearProgramming/Tournament.lean`;
* `isStandardQ_tournamentSkewMatrix` in
  `MathUE/LinearProgramming/CopositiveQ.lean`;
* `IsIntegralTournament` and
  `isStandardQ_or_singletonLCPFeasible_of_isIntegralTournament` in
  `MathUE/LinearProgramming/CopositiveQCorollaries.lean`;
* `quittingSingletonArcPayoff` in
  `UniformEquilibrium/Quitting/Circulation/SingletonFlowMesh.lean`; and
* `BalancedSingletonCycleCertificate`, `toWithBounds`,
  `opponent_product_lt_one`, `isTerminalNash_and_hasValue`,
  `isHorizonNash_and_delivers`, and `isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.

This review checks the integral-tournament closure section.  It does not
re-certify the earlier numerical searches, radical stationary roots, or the
216 Bernstein inequalities, none of which the tournament theorem uses.

## Final export-candidate delta

The refrozen candidate
`/tmp/FIN4_INTEGRAL_TOURNAMENT_BALANCED_SINGLETON_UNIFORM_PAYOFF.md` has
SHA-256
`d4343ecd14be5ba4244374298c6921970b2d83cc668ce1ab67d1f41d88498e44`.
Its review header now names the independent `CODEX_SPINOZA` review alongside
this one.  The control-byte scan is empty, and no mathematical claim was
added.  **Delta PASS for this exact candidate and hash.**
