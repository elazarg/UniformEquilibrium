# Independent review of complete Klein-four coverage

Reviewer: CODEX_KREIN. Ordinary mathematical review, not a Lean build.
Scope: the frozen section **Complete Klein-four coverage: frozen candidate
for independent review** of
`../notes/CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`, together with its
referenced common-hazard polynomial and reward-coordinate definitions.
No other review was read before this assessment.

Current scope: the proof remains mathematically valid, but the entire
existence class is already supplied by implemented criteria, including
the subgroup response quotient in the formerly proposed new branch.
The retained mathematical packet is now
`../notes/CODEX_BROUWER__KLEIN_FOUR_EQUIVARIANT_QUITTING_GAMES.md`.
This review does not support export as new existence coverage.

## Verdict

The claimed uniform-equilibrium existence theorem for every finite real
Klein-four-equivariant quitting table is proved by the displayed argument.
I found no mathematical gap or counterexample. In particular, the triangle
construction gives the four INDIVIDUAL Nash conditions, and the response
argument covers arbitrary complete behavioral deviations. This review does
not assert Lean verification, external priority, or existence outside the
stated equivariant class.

## Exact claim and reduction checked

The hypothesis is invariance under simultaneous translation of the player
and the quitting coalition by every element of (Z/2Z)^2. All-Never pays
zero. The output is one fixed uniform-payoff target, with profiles allowed
to depend on accuracy and without shared randomization.

Translation makes all own singletons equal to s. For s≤0 the all-Never
profile is exact Nash for both terminal and finite-average payoffs: a lone
deviator can receive only s or zero. For s>0 division of ALL rewards by s
is legitimate, including signed nonsingleton rewards and the zero Never
value. No invalid additive normalization is used.

For normalized singletons, D=Σa_t−3 splits the proposed cases exhaustively.
The data a_t,p_t,f_t,h_t,h0,g are the fourteen free coordinates after fixing
the common own singleton to one. Pair and triple rewards are not being
silently reconstructed from singleton symmetry.

## Independent check of the triangular producer

Fix a_t<1 with D>0. In the paired row (x,x,y,y), translation by t preserves
the row and swaps the two members of each pair. Thus their individual
face numerators coincide. Translation by a complementary group element
swaps the two pairs and gives exactly F1(x,y)=F0(y,x). This uses the full
reward equivariance, not a grouped-player payoff or a correlated action.

With A=1−a_t>0 and B=a_u+a_v−2, one has B−A=D>0. The individual deleted
opponent law contains one same-pair hazard x and two opposite-pair hazards
y, so expansion gives

    F0(x,y)=Ax−By+O((x+y)^2),
    F1(x,y)=Ay−Bx+O((x+y)^2).

In 0≤y≤x, the second linear term is at most −D*x. Since the field is a
fixed polynomial, a sufficiently small common delta gives F1<0 everywhere
in the punctured cutoff triangle, as well as F0(x,0)>0. Arbitrarily large
or badly signed nonsingleton coefficients merely shrink delta; they do
not invalidate these strict signs.

For metric projection onto T={0≤y≤x≤1}, the fixed-point convention is
correct:

    z=P_T(z+v)  iff  v·(w−z)≤0 for every w∈T.

The perturbation adds phi(x)≥0 only to coordinate 0. I checked every
cutoff face separately:

- At the origin, a positive horizontal direction contradicts the VI.
- At 0<y<x≤delta, both vertical signs are feasible, forcing F1=0.
- At y=0 and 0<x≤delta, both horizontal signs are feasible, forcing
  F0+phi=0 although it is positive.
- On x=y>0, if phi>0 the feasible direction (1,−1) has strictly positive
  field product. If phi=0, the feasible direction (−1,−1) has strictly
  positive field product because both field coordinates are negative.

All directions can be scaled to stay in T because delta<1. The line
x=delta is not an extra triangle face, and the same reasoning excludes
it even when phi vanishes there. Hence the selected point satisfies
x>delta, where the field is literally the original reward-table field.

At the remaining faces, ordinary feasible coordinate directions yield
the stated lower/upper complementarity signs. The only places where the
triangle does not provide both individual directions are its diagonal:

- At 0<x=y<1, both diagonal directions give F0+F1=0, and exact symmetry
  gives F0=F1, hence both vanish.
- At (1,1), the inward diagonal gives F0+F1≥0, and symmetry gives each
  coordinate nonnegative.

At (1,0), the independent inward directions give F0≥0 and F1≤0.
Thus every individual hazard satisfies the correct cube condition. The
proof does not infer individual incentives from an equilibrium of teams.
Since both members of the x-pair have x>delta, every player has a
positive-hazard opponent, even if y=0 or x=1.

## Complete deviations and the fixed target

For one individual, write alpha for its opponents' one-date Continue
probability, Q for its Quit endpoint, A for its unconditional absorbing
Continue reward, and b=1−(1−c)alpha. The actual stationary value is

    U=[cQ+(1−c)A]/b.

Direct multiplication verifies

    Q−(A+alpha*U)=[(1−alpha)Q−A]/b=F/b.

Therefore the selected complementarity signs imply BOTH pure-action
payoffs at continuation U are at most U. An arbitrary behavioral deviator
still faces the same independent opponents. Iterating these inequalities
leaves a bounded remainder multiplied by alpha^N, which vanishes because
alpha<1. This proves the full terminal cap, not only stationary optimality.

The same argument controls the terminal-to-finite-average bridge uniformly
over deviations. If |r|≤M and p_i=1−alpha_i>0, unchanged opponents give
an expected absorption-date bound at most 1/p_i up to the harmless indexing
convention. The difference between terminal and H-date average payoff is
bounded by 2M/(H*p_i). One fixed selected profile therefore works for every
sufficiently large H at its single actual payoff U.

The other branches also retain their fixed targets:

- D<0: the common-hazard face polynomial has L(0)=−D>0. If g<h0,
  L(1)=g−h0<0 supplies an interior exact root; otherwise the full sure
  coalition is exact Nash. At sure absorption, all later deviations equal
  the corresponding withdrawal payoff h0, so g≥h0 is sufficient.
- D=0: Q(q)→1 and A(q)/(1−alpha(q))→Σa_t/3=1. The full pure-time cap
  is the maximum of those two endpoints, so both prescribed values and
  all full regrets converge to the fixed all-ones target. Choosing q first
  and the horizon threshold second is permitted; no uniform-in-q duration
  bound is required.
- D>0 and every a_t≥1: with one rare solo owner, the prescribed terminal
  vector is exactly its singleton reward at every q. An outsider's
  Quit-now payoff is 1+q(p−1); its Never payoff is a≥1, so full gain is
  at most q*max(p−1,0). The owner has no positive-hazard opponent, but
  this is handled separately: every finite-average unilateral payoff is
  at most one, while its prescribed average tends to one. The other
  players retain the owner's geometric absorption bound.

Scaling back multiplies the bounds and target by the same positive s.
The target never depends on requested accuracy.

## Attempted falsifiers and precise source boundary

I tested the likely failure points: reversing the projection sign;
counting team deviations instead of individual deviations; a fixed point
on the cutoff seam; escape through either diagonal endpoint; y=0 with a
noncontracting deviator; zero singleton scale; negative reward entries;
the rare owner's lack of opponent absorption; and a horizon bound that
would need to be uniform as q→0. Each is explicitly resolved above. No
additional sign condition on nonsingleton rewards is needed.

The following source declarations were inspected, without rebuilding:

- `quittingFaceNumerator`, `continuous_quittingFaceNumerator`, and
  `quittingFaceNumerator_eq_gainValue`, in
  `UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`;
- `heterogeneousFaceNumerator_update_self` and
  `heterogeneousFaceNumerator_congr_off_self`, in
  `UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`;
- the target-family definitions and semantic endpoint in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

These support the stated semantics but do not themselves implement the new
triangle producer. The ordinary proof needs only finite polynomial algebra,
Euclidean projection, Brouwer, and geometric absorption. Its genuinely
additional hypothesis is full Klein-four reward equivariance; singleton
symmetry alone does not yield the exact diagonal identity used in the VI.

## Corrected implementation-overlap assessment

The earlier bounded source check missed the stronger subgroup response
quotient. I have now read
`responseInvariant_of_reward_subgroup_automorphisms` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientPlayerOrbits.lean`
and `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.

In the positive-surplus branch with a_t<1, translation by t gives two
two-element orbits and actual response invariance on their hazard cube.
With A=1−a_t>0 and B=a_u+a_v−2>A, the quotient singleton matrix is

    [[−A,B],[B,−A]].

Its determinant is A²−B²<0 and its inverse is
[[A,B],[B,A]]/(B²−A²), entrywise positive. The named criterion directly
produces original-game UE from these raw data. It requires no preselected
stationary root, supplied R0 proof, or behavioral witness. Combined with
the existing branches already audited for the other parameter regions,
this covers the full Klein-four class.

The independent triangle proof and the full-behavior checks above remain
valid ordinary mathematics. Their correct status is an alternative direct
proof within an implemented existence class. My mathematical PASS is
unchanged; any earlier implication of new existence-class coverage is
withdrawn. No Lean build was performed for this source audit.
