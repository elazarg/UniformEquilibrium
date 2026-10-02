# Projective-Q deterministic kiloblock

Author: `CODEX_CEDAR`
Status: `UNIVERSAL ONE-ACTIVE ROUTE REFUTED; PARTIAL DERANDOMIZATION LEMMAS RETAINED`

Current conclusion: the conjecture-closing thesis originally pursued in this
note is false.  The Solan--Vieille boundary table is a checked full-normal,
standard-Q, no-homogeneous residual-hard instance, but every deterministic
profile with at most one positive hazard at each live date has terminal
exploitability at least one fixed positive constant.  The ordinary proof and
its exact source adapter are independently audited in
`feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CODEX_CEDAR__ROUND_2.md`.
The same table has the checked exact two-active period-two equilibrium
`periodTwo_isUniformEquilibriumPayoff`, so this is an architecture no-go, not
a counterexample to the full conjecture.

The active conjecture-facing thesis has moved to
`CODEX_CEDAR__ZERO_BOUNDARY_PHANTOM_CARRIER.md`: use zero-boundary provenance
in the compact exact Nash--Bellman relation to force either a divergent-clock
ordinary path or a strategically realizable endpoint from the remaining
all-Continue phantom.  The precise universal obligation is no longer a
singular-face scheduling lemma; it is to eliminate the summable-opponent-clock
phantom branch without assuming that stored Bellman annotations are realized
continuation payoffs.

Kill criterion met: `boundaryReward` satisfies the source-side residual-hard
matrix conditions by `periodTwo_residualHardClass`, while the audited positive
solo-hazard exploitability floor rules out every sufficiently accurate
one-active chronology, not only those supported on a singular zero stratum.

Next concrete check for this closed note: none.  Sections 2--9 remain valid
partial mathematics about regular building blocks and fixed packets, but they
cannot be promoted to a universal producer.  In particular, the production
`FaceCirculationCertificate` compiler serializes every phase into literal
one-active rows, so calling its phase mixture "multi-owner" does not evade the
no-go.

Everything below is ordinary mathematics unless a named production Lean
declaration is explicitly said to be proved in Lean.  The paper transcription
under `Literature/` is non-built and is used only as a faithful mathematical
source, not as an integrated Lean theorem.  No Lean file or export is
proposed.

## 1. Exact endpoint and source audit

The production repository already proves the deterministic half under a
stronger input.

- `balancedWord`, `mixDeficit_invariant`, and
  `abs_wordDrift_balancedWord_le` in
  `UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationOrbit.lean`
  turn a phase mixture into a predictable owner word with bounded prefix
  drift.
- `exists_supportRationalDivergentPath_of_multiCirculation` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_multiCirculation` in
  `UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationCompactPath.lean`
  compile a supplied `FaceCirculationCertificate` into an ordinary
  support-rational divergent path and a uniform-equilibrium payoff.  The
  support statement is consumed against unrestricted behavioral deviations.
- `faceCirculation_mixWeight_ne_packetMass` in
  `UniformEquilibrium/Quitting/Classification/SingletonPacketPreferenceLassoCirculation.lean`
  proves that a strict preference-lasso packet cannot simply use its complete
  packet mass as one face-circulation phase.

Thus predictable low-discrepancy sampling is not the missing theorem by
itself.  The production certificate additionally requires every phase source
and phase target to pin every active owner's coordinate to its own singleton
value.

The mathematical source for the universal Q branch is Solan and Solan,
*Quitting Games and Linear Complementarity Problems* (2020), Theorem 2.13(2)
and Section 3.  The faithful non-built transcription is
`Literature/SolanAndSolan2020.lean`.  Its relevant objects are:

- `BuildingBlock` and `theorem3_3`: for a boundary point `y`, a new boundary
  point `w`, owner-specific attempt values `w^i`, and simplex weights
  `(z_0,z_i)`;
- `theorem3_6` and `exists_buildingBlock_approximationWitness`: arbitrarily
  large displacement with small inter-block tracking error; and
- `theorem2_13_sunspot`: the paper's public-signal equilibrium conclusion.

That lane is not a production library.  The present question is whether the
finite building-block data can be consumed by the already checked ordinary
support-path endpoint without a fresh public signal.

The ordinary finite-quitting target remains one fixed payoff, all positive
accuracies, all sufficiently long finite horizons, and arbitrary unilateral
behavioral deviations.  A deterministic finite word must therefore enter a
named all-behavior consumer; pointwise stationary or one-shot optimality is
not silently enough.

## 2. Necessary local pinning for a predictable owner

Normalize singleton self rewards to zero and let `M_{.i}` be owner `i`'s
singleton column.  At one row only owner `i` quits, with hazard `h in (0,1)`,
and let `x` be the reached continuation after this row.  The owner's pure-Quit
endpoint is `M_ii=0`, while its pure-Continue endpoint is exactly `x_i`.

### Proposition 2.1: active-tail pinning

If both Quit and Continue are supported within error `epsilon` at this row,
then

```text
|x_i| <= epsilon.                                    (2.1)
```

For exact support optimality, `x_i=0`.

#### Proof

Positive Quit probability gives `Quit-Continue<=epsilon`, hence
`-x_i<=epsilon`.  Positive Continue probability gives
`Continue-Quit<=epsilon`, hence `x_i<=epsilon`.  This is exactly the
singleton-row specialization recorded by `gainValue_singletonRow_self` and
the support-perfect predicate in the production circulation module.  ∎

This condition concerns the **conditional tail at the actual calendar
date**.  A global frequency estimate for owner labels or an averaged Bellman
identity does not imply it.  It is the first place where knowing future labels
can matter to a deviator.

## 3. Exact restart/advance reduction of a paper building block

Fix one `BuildingBlock M y epsilon` and suppress `epsilon`.  Its data satisfy

```text
w = z_0 y + sum_i z_i w^i,                            (3.1)
```

where the nonnegative weights sum to one and `sum_i z_i>0`.  For each owner
`i`, the approach clause says that for a uniquely usable scalar `q_i in
(0,1]` one has one of the two forms

```text
w^i = (1-q_i) w + q_i M_{.i}       (restart type),    (3.2R)
w^i = (1-q_i) y + q_i M_{.i}       (advance type).    (3.2A)
```

Existence of some `q_i` follows from segment membership, and `q_i>0` follows
from the stipulated inequality between `w^i` and its segment base.  If a
segment representation is nonunique because its endpoints coincide, the
stipulated inequality rules that case out.

Let `R` and `A` be the restart and advance owner sets and put

```text
rho = sum_{i in R} z_i(1-q_i).
```

### Proposition 3.1: collapsed terminal-lottery identity

One has `rho<1` and

```text
w = a y + sum_i theta_i M_{.i},                       (3.3)

theta_i = z_i q_i/(1-rho),
a = [z_0 + sum_{i in A} z_i(1-q_i)]/(1-rho),
a + sum_i theta_i = 1.
```

All displayed coefficients are nonnegative.

#### Proof

Substitute (3.2R)--(3.2A) in (3.1) and move the restart-survival term
`rho*w` to the left.  Moreover

```text
1-rho = z_0 + sum_{i in A}z_i + sum_{i in R}z_i q_i > 0.
```

Strict positivity follows from `sum_i z_i>0` and `q_i>0`.  The numerator of
`a` plus `sum_i z_iq_i` equals this same denominator, proving the simplex
identity.  ∎

So public restart draws do not create a new attainable payoff vector at the
level of terminal lotteries: `w` is an ordinary convex combination of `y`
and singleton columns.  The hard point is strategic conditioning, not payoff
feasibility.

### Proposition 3.2: exactly what complementarity pins

If `z_i>0`, the building-block complementarity condition gives `w^i_i=0`.
Because `M_ii=0`, (3.2R)--(3.2A) imply:

- for a restart type with `q_i<1`, `w_i=0`;
- for an advance type with `q_i<1`, `y_i=0`; and
- for a sure-exit type `q_i=1`, neither base coordinate is constrained.

It does **not** follow that the mixed singleton target in (3.3) has zero
`i`-coordinate whenever `theta_i>0`.  That extra simultaneous target-pinning
condition is precisely what a production `FaceCirculationCertificate`
requires.  The checked strict-lasso obstruction cited in Section 1 is an
actual source example of this loss for the complete packet mass.

## 4. Why payoff derandomization is not yet strategy derandomization

Given the probability vector `(a,theta_i)`, elementary sequential hazards can
realize the terminal lottery (3.3): order its atoms, give each owner a
conditional hazard equal to its remaining desired first-hit mass, and leave
`a` as final survival to tail `y`.  This exactly matches the on-path expected
payoff `w`.

At owner `i`'s actual row, however, the nonquit continuation is the
conditional mean of the atoms scheduled after that row.  Proposition 2.1
requires its `i`-coordinate to be near zero.  Equation (3.3) only makes the
**unconditional** mean equal to `w`; it supplies no such condition for every
ordered residual mean.  Splitting an atom into many small pieces reduces each
hazard but does not automatically reduce a same-sign residual-coordinate
bias.

The missing deterministic object can therefore be stated without game
jargon.  Split the masses `theta_i` into a finite or countable ordered word.
Before emitting a piece labelled `i`, let `T` be the normalized mean of all
later singleton atoms plus the final `y` atom.  Required:

```text
|T_i| <= meshError                                   (4.1)
```

at every emitted piece, with one all-suffix error bound, while the emitted
mass is large enough to force absorption.  Floor coordinates of every such
`T` must remain above the normalized punishment floor up to the same error.

This is a conditional-residual discrepancy problem, stronger than bounded
prefix discrepancy of label counts.  Production `balancedWord` solves it
when a face-circulation phase has already supplied source and target pinning.
The universal Q-matrix building block supplies (3.1)--(3.2), not that phase
pinning.

## 5. Proved and unproved separation

Proved here in ordinary mathematics:

- active owners require the actual conditional tail pinning (2.1);
- every restart/advance building block collapses to the exact ordinary
  terminal-lottery identity (3.3);
- complementarity pins the appropriate restart or advance base only when
  `q_i<1`; and
- terminal-lottery implementability alone does not establish the local
  support inequalities needed by the ordinary path compiler.

Checked production facts are only the named circulation producer/consumer and
strict-lasso obstruction in Section 1.  The Solan--Solan declarations are in
the non-built literature lane and are not described as production-checked.

Unproved:

- every Q-matrix building-block chain admits the ordered residual-pin schedule
  (4.1);
- the schedule retains the punishment floor and compatible reached tails;
- its joint and all player-deleted clocks contract as required by the chosen
  all-behavior compiler; and
- the resulting payoff target can be selected independently of accuracy.

The next exact experiment is the three-owner cyclic matrix, where the active
zero-coordinate faces and all residual means can be solved by rational
algebra.  A positive result would identify the invariant needed in general;
a negative result must survive arbitrary atom splitting and ordering, not
only one greedy word.

## 6. Generic blocks admit an exact two-phase ordering

The source contains a stronger fact than the abstract segment statement used
in Section 3.  Under the negative-column margin used in the Q branch,
`BuildingBlock.exists_attempt` in `Literature/SolanAndSolan2020.lean`
extracts for every owner with relevant positive type mass an attempt weight

```text
0 < q_i < 1,                                         (6.1)
```

not merely `q_i<=1`.  The strict upper bound follows because a column has a
coordinate below `-epsilon`, whereas every attempted value is at least
`-epsilon`.  Thus the sure-exit loss of base pinning in Proposition 3.2 is an
abstract boundary case, not a case reached by the source Q-branch block.

Fix one such block.  Write `R` and `A` for its restart and advance owners,
respectively.  Suppose

```text
ZeroCoordinates(y) = {a},
ZeroCoordinates(w) = {r}.                            (6.2)
```

Here equality is literal: `y,w` are nonnegative and have unique zero
coordinates `a,r`.  Owners of zero public mass can be discarded.

### Proposition 6.1: regular two-phase derandomization

Every positive-mass restart type is owner `r`, and every positive-mass
advance type is owner `a`.  After summing the restart loop, there is a vector
`U` and weights `theta,phi in [0,1)` such that

```text
w = theta M_{.r} + (1-theta) U,                      (6.3)
U = phi M_{.a} + (1-phi) y.                          (6.4)
```

Moreover

```text
U_r=0,  U_a=0,  and  U_j >= -epsilon for every j.    (6.5)
```

Consequently the terminal lottery of the block has the deterministic order

```text
owner r phase  -->  owner a phase  -->  tail y,      (6.6)
```

with an absent phase deleted when its mass is zero.  Throughout the first
phase the reached continuation has coordinate `r` equal to zero; throughout
the second it has coordinate `a` equal to zero.  Every intermediate value is
coordinatewise at least `-epsilon`.

#### Proof

If `z_i>0`, complementarity says `w^i_i=0`.  For a restart attempt,

```text
0=w^i_i=(1-q_i)w_i,
```

and (6.1) gives `w_i=0`, hence `i=r`.  For an advance attempt the same
calculation gives `y_i=0`, hence `i=a`.  This proves the support reduction.

Put

```text
rho = sum_{i in R} z_i(1-q_i),
d   = z_0 + sum_{i in A} z_i,
u   = z_0 y + sum_{i in A} z_i w^i,
b   = sum_{i in R} z_i q_i.
```

The original balance identity becomes

```text
(1-rho)w = u + b M_{.r},
1-rho = d+b.                                         (6.7)
```

One has `d>0`.  Otherwise all positive public mass is the single restart
type `r`; (6.7) and `q_r>0` force `w=M_{.r}`.  But `w` belongs to `D`, while
`column_not_mem_D_of_no_nontrivial_zero_solution` in the same source file
excludes every singleton column from `D` on the no-homogeneous branch.

Define

```text
U=u/d,                 theta=b/(1-rho).
```

Then `theta<1` and (6.3) follows.  Since `w_r=M_rr=0`, (6.3) gives `U_r=0`.
Every advance type is `a`; both `y_a` and `w^a_a` vanish, so `U_a=0`.
The source inequalities `y_j>=0` and `w^a_j>=-epsilon` give `U_j>=-epsilon`.

Finally, if the advance type has positive mass, its attempt identity gives

```text
U = [z_0 y+z_a((1-q_a)y+q_aM_{.a})]/(z_0+z_a)
  = (1-phi)y+phi M_{.a},
phi=z_a q_a/(z_0+z_a)<1.
```

If it has zero mass, take `phi=0`.  This proves (6.4).  Splitting `theta`
and `phi` into arbitrarily fine per-stage hazards implements (6.3)--(6.4)
in the displayed chronological order.  Both endpoints of the first segment
have coordinate `r` zero, and both endpoints of the second have coordinate
`a` zero.  The first segment lies between `w>=0` and `U>=-epsilon`; the
second lies between `U>=-epsilon` and `y>=0`, proving the final lower bound.
∎

### Strategic error of the two phases

At an owner phase, the active owner's Quit payoff is its normalized diagonal
zero and its actual Continue tail has the same coordinate zero.  Thus the
active owner is exactly indifferent.  A different normal player has
continuation at least `-epsilon`; its own singleton payoff is zero, and the
effect of joining the active owner is proportional to the fine mesh hazard.
With reward bound `M` and stage hazard `h`, the same calculation packaged by
`isSupportPerfectRow_singletonRow_approx` in
`UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationOrbit.lean`
gives an error of the form

```text
epsilon + 2 M h.                                     (6.8)
```

Normal players' punishment values are nonpositive in the paper's translated
coordinates, so the lower bound in Proposition 6.1 is also the correct
individual-rationality scale.  This paragraph is an adapter calculation,
not yet a full construction for ambient abnormal players; that ambient
adapter remains to be tied to the paper's corresponding positive-payoff
bounds.

The source chain is ordered from a high-index block to the preceding block.
Survival through block `k` ends at `y_k`, while Theorem 3.6 makes `y_k`
close to `w_{k-1}`.  Hence the existing tracking correction pays the only
inter-block seam.  Proposition 6.1 removes the public draw inside every
regular block without introducing another seam.

## 7. Small cyclic test and the surviving singular obstruction

For the oriented three-cycle

```text
M_{.0}=(0,2,-1),  M_{.1}=(-1,0,2),  M_{.2}=(2,-1,0),
```

Proposition 6.1 gives the exact face order.  For example, if `w_0=0` and
`y_1=0`, a regular block has

```text
w = a y + theta_0 M_{.0} + theta_1 M_{.1}.
```

Coordinates zero and one force

```text
theta_0=w_1/2,
theta_1=a y_0.
```

After removing the owner-zero atom one reaches

```text
w-theta_0 M_{.0}=a y+theta_1 M_{.1},
```

whose coordinate one is zero; removing owner one then reaches `a y`.
The opposite proposed terminal face cannot occur with positive owner-zero
mass: if `y_2=0` and the only types are zero and two, coordinate two gives
`w_2=-theta_0`, so nonnegativity forces `theta_0=0`.  This exact check is the
smallest instance of the restart-then-advance rule, rather than an additional
cyclic hypothesis.

The genuine unresolved set is therefore

```text
Sigma(M)={x in DZero(M): at least two coordinates of x vanish}.   (7.1)
```

At a singular endpoint, several restart or advance owners may have positive
mass.  An ordered terminal-atom realization is a boundary-control path for
the unnormalized residual `R`:

```text
R starts at w,
R changes by -dmu_i M_{.i},
dmu_i>0 is allowed only when R_i=0,
R ends at a y.                                      (7.2)
```

This is stronger than the static complementarity at the two endpoints.  A
balanced owner word controls unconditional column drift, but does not by
itself enforce (7.2) at every suffix.

Regular points are dense in a coordinate face only when that face is not
identically contained in another zero-coordinate face.  Even when they are
dense, density alone does not finish the route: the selected map
`y |-> w(y)` in Theorem 3.6 is an arbitrary choice and need not be continuous,
so perturbing `y` need not preserve the next tracking endpoint.  A valid
proof now needs one of two stronger statements:

1. a face-control theorem deriving an approximate path (7.2) on every
   singular block from standard Q and nonhomogeneity; or
2. a finite-stratum descent showing that any unbounded-displacement chain
   whose regular-block displacement stays bounded yields a lower-dimensional
   standard-Q/nohomogeneous carrier on one fixed zero set.

Neither statement is proved here.  This is a smaller and source-matched
universal obligation: generic building blocks, restart loops, conditional
tail pinning, and the cyclic sanity test have all been discharged.

## 8. Updated proved and unproved separation

In addition to Sections 2--3, proved here in ordinary mathematics:

- source-relevant attempt weights satisfy `q_i<1` under the named negative
  column hypothesis;
- every building block with unique-zero input and output has the exact
  restart-owner/advance-owner two-phase representation (6.3)--(6.6);
- the active coordinate is exactly pinned throughout both deterministic
  phases, and all normal-coordinate values remain at least `-epsilon`; and
- the three-owner oriented cyclic packet obeys the same order by exact
  coordinate algebra.

Still unproved:

- singular-stratum face control or dimension descent;
- preservation of arbitrarily large absorption after discarding or reducing
  singular blocks;
- the ambient abnormal-player support/floor adapter for the deterministic
  block chain; and
- the final all-errors ordinary path family and fixed target.

## 9. A mesh-independent precedence obstruction on singular packets

There is an exact necessary condition stronger than global frequency
matching and weaker than constructing the full face path.  It applies to the
multi-restart projective packet which remains after Section 6.

Let

```text
w = c y + sum_i lambda_i M_{.i},
c>=0, lambda_i>=0, c+sum_i lambda_i=1,             (9.1)
lambda_i>0  ==>  w_i=0.
```

Split each `lambda_i` into finitely many positive terminal masses `alpha_m`
and put them in an arbitrary deterministic order with labels `ell_m`.  Let

```text
u_m = sum_{p<m} alpha_p e_{ell_p},
R_m = w-Mu_m.                                        (9.2)
```

`R_m` is the unnormalized residual payoff mass immediately before atom `m`.
Because the diagonal is zero, the owner coordinate is unchanged by removing
its own current atom.  Thus an `epsilon` support-pin at every emitted atom
implies

```text
|(R_m)_{ell_m}| <= epsilon.                          (9.3)
```

Using the exact remaining survival mass instead of the coarse right side
only strengthens this inequality.

### Proposition 9.1: pairwise precedence interval

Put `m=sum_i lambda_i`.  Every ordered atom splitting satisfying (9.3)
obeys

```text
dist(0,[L(lambda),U(lambda)]) <= epsilon*m,           (9.4)
```

where

```text
L(lambda)=sum_{i<j} lambda_i lambda_j min(M_ij,M_ji),
U(lambda)=sum_{i<j} lambda_i lambda_j max(M_ij,M_ji). (9.5)
```

In particular, exact suffix pinning requires

```text
L(lambda) <= 0 <= U(lambda).                         (9.6)
```

If, for example, `U(lambda)<0`, every possible ordering and every atom mesh
has support error at least `-U(lambda)/m>0`.

#### Proof

Multiply (9.3) by `alpha_m` and sum.  Since every used label has `w_i=0`,

```text
E := sum_m alpha_m (R_m)_{ell_m}
   = -sum_{p<m} alpha_m alpha_p M_{ell_m,ell_p},
|E| <= epsilon*m.                                    (9.7)
```

Fix two distinct owners `i,j`.  Every ordered pair consisting of one
`i`-piece and one `j`-piece contributes exactly once.  If the `i`-piece is
later, its coefficient in the sum without the leading minus sign is `M_ij`;
if the `j`-piece is later, it is `M_ji`.  The total cross-product mass is
`lambda_i lambda_j`.  Hence this pair's contribution lies in

```text
lambda_i lambda_j
  [min(M_ij,M_ji),max(M_ij,M_ji)].
```

Summing the finitely many pair intervals shows that the sum in (9.7) lies in
`[L(lambda),U(lambda)]`.  Its distance from zero is at most `|E|`, which is
(9.4).  ∎

This obstruction is genuinely conditional.  The endpoint identity (9.1)
and global atom frequencies determine `lambda`, but do not choose the
pairwise precedence parameters hidden between the two endpoints of every
interval in (9.5).  Conversely, (9.6) is only one aggregate necessary
condition; it does not construct a schedule whose owner coordinate is small
at every suffix.

The source-level consequence is now exact.  A universal positive
derandomization must show that the projective-LCP packet in the Lemma 3.4
branch can always be selected with (9.6), and then solve the stronger
all-suffix ordering problem.  A universal negative answer to the predictable
single-owner question would follow from one actual standard-Q,
no-homogeneous source packet for which the interval is separated from zero,
followed by a full-game adapter showing that the resulting owner refusal is
not neutralized by the other branches.  No such actual packet is asserted
here.

Sanity checks:

- singleton support gives `L=U=0`, agreeing with Proposition 6.1;
- an exact duplicated coordinate gives `M_ij=M_ji=0` for the duplicate pair,
  so duplication creates no precedence obstruction and can be collapsed to
  the quotient cyclic block; and
- the three-cycle has both signs available across its active pairs, which is
  consistent with the explicit oriented schedule in Section 7.

`faceCirculation_mixWeight_ne_packetMass` does not imply Proposition 9.1:
that checked theorem rules out one complete-packet face-circulation weight at
a strict preference entrance, whereas (9.4) quantifies every deterministic
atom ordering of a fixed complementary projective packet.
