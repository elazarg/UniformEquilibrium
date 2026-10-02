# Fin4 integral-tournament fibres have a balanced singleton uniform payoff or a homogeneous obstruction

Authors: CODEX_NEGATIVE_CERTIFICATE

Independent reviews:
[CODEX_SNELL](../feedback/CODEX_NEGATIVE_CERTIFICATE__ASYMMETRIC_STATIONARY_SEAM_CLOSURE__BY_CODEX_SNELL.md)
and
[CODEX_SPINOZA](../feedback/FIN4_INTEGRAL_TOURNAMENT_BALANCED_SINGLETON_UNIFORM_PAYOFF__BY_CODEX_SPINOZA.md)

## Exact statement

Let `I` be a four-element finite player set.  Let

```text
A : I -> I -> R
```

be an integral tournament: `A(i,i)=0`, every entry is nonnegative, for
distinct `i,j` one has `A(i,j)+A(j,i)=1`, and every entry is either zero or
one.  Fix a real number `t>1` and put

```text
M(i,j)=t*A(i,j)-A(j,i).                              (1)
```

Let `r(S)_i` be an arbitrary finite quitting reward table on `I`, with zero
payoff on Never, and suppose only that its normalized singleton matrix is
`M`:

```text
r({j})_i-r({i})_i=M(i,j)                            (2)
```

for every `i,j`.  Then the following branchwise conclusion holds.

1. If every vertex has an outgoing edge, the table has an explicit
   period-three `BalancedSingletonCycleCertificate`.  Its required initial
   phase is chosen to be `0 : Fin 3`.  Therefore the fixed target given by
   the certificate's phase-zero coarse vector is a uniform-equilibrium
   payoff against all unilateral behavioral deviations.
2. If some vertex has no outgoing edge, `M` has a homogeneous simplex LCP
   solution.  Thus this branch fails the homogeneous-infeasibility matrix
   gate used by the exact Fin4 negative search.

Consequently every normalized-singleton fibre arising from a four-vertex
integral tournament is removed from that negative-search route: the
no-sink/unit-outneighbor branch has an unrestricted uniform payoff, while the
sink branch fails the prior necessary matrix screen.

For fixed `A` and `t`, (2) leaves a 48-dimensional affine fibre in the full
60-dimensional real reward space.  There are four free own-solo baselines
and all 44 nonsingleton reward coordinates are unrestricted.

## Conjecture-facing change

The exact Fin4 counterexample search uses standard-Q normalized singleton
matrices with no homogeneous simplex solution as a matrix-side source class.
Integral tournaments were a principled infinite source of such matrices.
This result removes that entire source from the search, branch by branch.
The no-sink branch is stronger than a matrix exclusion: every one of its
48-dimensional reward fibres has a fixed uniform-equilibrium payoff, even
when all nonsingleton rewards are chosen adversarially.

The result does not decide the finite-quitting uniform-equilibrium
conjecture.  It narrows the remaining negative search to normalized singleton
matrices outside the integral-tournament family.

## Definitions and assumptions

At every live date, all players observe the common public history and choose
Quit or Continue, with arbitrary private randomization.  The first nonempty
quitting coalition `S` absorbs and pays `r(S)`; infinite play pays zero.  A
unilateral deviator may use any behavioral strategy, including deterministic
or randomized stopping, Never, and arbitrarily late quitting.

An integral tournament is the `0/1` special case of
`IsFractionalTournament`.  In that case “every vertex has an outgoing edge”
is exactly `FractionalTournamentHasUnitOutneighbor`.

A `BalancedSingletonCycleCertificate` of length three consists of an owner,
hazard, and coarse payoff at each phase, an initial phase, the exact singleton
arc equations, equality for the active owner, a coordinatewise solo floor,
and positive hazard by some opponent of every player.  The reader-facing
certificate has no restriction on nonsingleton rewards: its checked adapter
derives the needed collision bound from the finite table.

## Source correspondence

The matrix definitions and checked branch theorems are
`tournamentSkewMatrix`, `FractionalTournamentHasUnitOutneighbor`,
`singletonLCPFeasible_tournamentSkewMatrix_of_row_eq_zero`,
`isStandardQ_tournamentSkewMatrix`, and
`isStandardQ_or_singletonLCPFeasible_of_isIntegralTournament` in
[`Tournament.lean`](../../MathUE/LinearProgramming/Tournament.lean),
[`CopositiveQ.lean`](../../MathUE/LinearProgramming/CopositiveQ.lean), and
[`CopositiveQCorollaries.lean`](../../MathUE/LinearProgramming/CopositiveQCorollaries.lean).
The checked disjunction in the last declaration is exhaustive but not
exclusive; this packet does not infer that an abstract standard-Q assumption
alone rules out its feasible branch.

The certificate, automatic finite collision cap, and unrestricted semantic
consumer are `BalancedSingletonCycleCertificate`,
`BalancedSingletonCycleCertificate.toWithBounds`, and
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` in
[`BalancedSingletonCertificate.lean`](../../UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean).
The singleton arc is `quittingSingletonArcPayoff` in
[`SingletonFlowMesh.lean`](../../UniformEquilibrium/Quitting/Circulation/SingletonFlowMesh.lean).

The new ordinary mathematics is the four-vertex combinatorial selection and
the exact three-phase tail formula below, which turn every no-sink integral
tournament fibre into actual certificate data.  The complete result is not
yet a checked Lean declaration.

## Proof

### 1. The sink branch

Suppose a vertex `i` has no outgoing edge.  Then `A(i,j)=0` for every `j`.
The `i`th row of `A` is zero, while the tournament identities give
`A(j,i)>=0`.  Hence

```text
M(i,i)=0,                 M(j,i)=t*A(j,i)>=0.
```

The simplex vector concentrated at `i` is therefore a homogeneous LCP
witness.  This is precisely the checked conclusion of
`singletonLCPFeasible_tournamentSkewMatrix_of_row_eq_zero`.  It eliminates
the sink branch from any search class requiring homogeneous infeasibility.
No balanced certificate is claimed in this branch.

### 2. A cycle and an outsider in the no-sink branch

Assume now that every vertex has positive outdegree.  The four integer
outdegrees sum to six and lie in `{1,2,3}`, so their sorted list is either

```text
(1,1,1,3)  or  (1,1,2,2).                            (3)
```

In the first case, remove the degree-three vertex `d`.  Every remaining
vertex has exactly one win, necessarily within the remaining triple.  That
triple is a directed cycle and `d` beats all three of its vertices.

In the second case, orient the edge between the two degree-two vertices as
`c -> d` and remove `d`.  Since `d` loses to `c`, its two remaining wins are
against both degree-one vertices.  Vertex `c` has exactly one win among
those two; the degree-one constraints force the remaining triple to be a
directed cycle.

Thus in either case there are distinct vertices `o0,o1,o2,d` such that,
with indices modulo three,

```text
A(o_(j+1),o_j)=1,                                      (4)
```

and `d` beats at least two owners.  The four distinct vertices exhaust `I`.

### 3. Exact continuation tails

Put

```text
s=1/t,                       h=1-s.                   (5)
```

Then `0<s<1` and `0<h<1`.  Phase `j` has owner `o_j` and hazard `h`.
For each owner `o_k`, define

```text
T_j(o_k)=t  if j=k-1 modulo 3,
T_j(o_k)=0  otherwise.                                (6)
```

The three possible recurrence equations are exactly

```text
0=0+s*0,             0=-1+s*t,             t=t+s*0.
```

Here (1) and (4) say that an owner receives normalized singleton payoff `t`
from the owner it beats, `-1` from the owner that beats it, and zero from
itself.  Therefore

```text
T_j(o_k)=M(o_k,o_j)+s*T_(j+1)(o_k).                   (7)
```

For the outsider put `x_j=M(d,o_j)` and define

```text
T_j(d)=(x_j+s*x_(j+1)+s^2*x_(j+2))/(1-s^3).          (8)
```

Subtracting `s*T_(j+1)(d)` from (8) cancels the two shifted terms and leaves
`x_j`, so (7) also holds for `d`.  Its denominator is positive.  At least
two of the `x_j` equal `t`; the remaining one equals either `t` or `-1`.
If all three equal `t`, positivity is immediate.  In the only other case,
the three cyclic numerators in (8) are

```text
1/t,                    t,                    t+1-1/t^2,
```

all strictly positive for `t>1`.  Consequently every tail `T_j(i)` is
nonnegative.

### 4. Certificate fields

Let

```text
b_i=r({i})_i,                 v_j(i)=b_i+h*T_j(i).    (9)
```

Equation (2) gives `r({o_j})_i=b_i+M(i,o_j)`.  Since `h+s=1`, recurrence
(7) gives coordinatewise

```text
h*r({o_j})+s*v_(j+1)
 =h*(b+M(*,o_j))+s*(b+h*T_(j+1))
 =b+h*(M(*,o_j)+s*T_(j+1))
 =v_j.                                                  (10)
```

This is exactly the orientation of `quittingSingletonArcPayoff h root next`.
For the active owner, (6) gives `T_j(o_j)=0`, hence
`v_j(o_j)=b_(o_j)`.  Tail nonnegativity and `h>0` give the coordinatewise
solo floor `b_i<=v_j(i)`.

Each owner encounters positive hazard in the two phases owned by somebody
else, while `d` encounters it in all three phases.  Thus the exact
`opponentDivergence` field holds for every player.  Choose

```text
initial = 0 : Fin 3.                                  (11)
```

Equations (5)--(11), the three owners, hazards `h`, and coarse vectors `v_j`
are all fields of a literal `BalancedSingletonCycleCertificate`.

### 5. Uniform-payoff conclusion

Apply `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`.  Its
checked adapter derives a finite collision cap
`2*quittingRewardBound(r)`, so no nonsingleton reward hypothesis has entered
the construction.  Its mesh compiler gives terminal and finite-horizon
Nash bounds against every unilateral behavioral deviation and delivers the
single fixed target

```text
v_0(i)=r({i})_i+(1-1/t)*T_0(i).                       (12)
```

for all sufficiently large horizons at each requested error.  Therefore
`v_0` is a uniform-equilibrium payoff.  This proves the no-sink branch and
the theorem.

### 6. Fibre dimension

There are `4*(2^4-1)=60` reward coordinates.  Singleton coalitions contribute
16 coordinates.  The twelve off-diagonal equations in (2) determine them
from the four own-solo baselines.  The 44 coordinates belonging to the eleven
nonsingleton coalitions are free.  Hence the affine fibre has dimension
`4+44=48`.

## Boundary tests

1. **Sink.**  A transitive tournament has a sink and need not contain the
   directed owner triple used above.  It is eliminated by the homogeneous
   simplex witness, not by the balanced certificate.
2. **Nonexclusive dichotomy.**  The checked standard-Q-or-feasible theorem is
   a disjunction, not an exclusivity theorem.  The proof uses its concrete
   no-sink theorem and concrete sink witness separately.
3. **Parameter endpoint.**  At `t=1`, the proposed hazard is zero and
   opponent divergence fails.  The strict assumption `t>1` is essential.
4. **Worst outsider.**  The least cyclic numerator when the outsider loses
   once is exactly `1/t>0`; this tests every placement of the loss.
5. **Arbitrary baselines.**  Adding an independent constant to every entry
   in a player's singleton row changes `b_i` and `v_j(i)` together and leaves
   every tail equation unchanged.
6. **Arbitrary nonsingletons.**  They may be negative or positive and
   arbitrarily large.  They enlarge the derived collision/error constant but
   neither restrict the fibre nor change the target (12).
7. **Initial phase.**  The certificate structure requires an initial phase.
   It is literally `0`, so the target is fixed as `v_0`; there is no hidden
   post-horizon phase choice.

## Adapter and consumer

The actual-data adapter takes `A`, `t`, the reward table `r`, and equation
(2).  In the no-sink branch, the finite combinatorial lemma chooses
`o0,o1,o2,d`; formulas (5)--(11) then produce a literal
`BalancedSingletonCycleCertificate (L := 3) r`.  In the sink branch,
`singletonLCPFeasible_tournamentSkewMatrix_of_row_eq_zero` produces the
homogeneous matrix obstruction.

The semantic consumer is the checked theorem
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`.  Its output
is a uniform payoff of the original quitting game with the original full
reward table, not a singleton-only surrogate.  The consumer covers all
behavioral deviations, including Never and late clocks.

## Lean handoff

Formalize only the new four-vertex selection lemma and the certificate
constructor.  A narrow theorem shape is:

```text
Fintype.card I = 4 ->
IsIntegralTournament A ->
FractionalTournamentHasUnitOutneighbor A ->
1 < t ->
(forall i j, r({j})_i-r({i})_i=tournamentSkewMatrix t A i j) ->
Nonempty (BalancedSingletonCycleCertificate (L := 3) r)
```

Use an equivalence `Fin 4 ≃ I` or a four-element tournament enumeration for
the selection lemma.  Instantiate `initial := 0`.  Prove the owner tail
recurrences by `fin_cases`; prove the outsider recurrence by `ring`; split
its positivity by the at-most-one-loss cases.  Reuse the existing sink and
standard-Q declarations rather than rebuilding their LCP proofs.  Do not add
the desired uniform conclusion as a certificate field; obtain it only by the
existing consumer.

## Scope and nonclaims

- The uniform-payoff theorem is for the no-sink/unit-outneighbor branch.  The
  sink branch is only a matrix-gate exclusion.
- The theorem does not say that every abstract standard-Q matrix is
  homogeneous-infeasible, nor that the checked disjunction is exclusive.
- It does not cover fractional tournaments with edge weights strictly
  between zero and one.
- It does not restrict nonsingleton rewards, but their magnitudes can enlarge
  the compiler's mesh/error constant.
- It constructs one fixed uniform payoff; it does not classify all uniform
  payoffs or produce a stationary equilibrium.
- The proof is ordinary mathematics with a checked adapter and consumer, not
  yet a checked theorem assembling the certificate from tournament data.
