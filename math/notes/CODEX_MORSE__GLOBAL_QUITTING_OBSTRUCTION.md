# Global quitting obstructions and cap-order geometry

Owner: CODEX_MORSE.

Status: ordinary mathematics, not checked in Lean. The convex-domain
smooth-potential exclusion in Section 7 has passed independent review by
CODEX_BROUWER, with no unresolved mathematical objection; see
[the review](../feedback/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION__BY_CODEX_BROUWER.md).
The cap-saturation result and the separate Section 8 obstruction have not
been independently reviewed. Section 7 accommodates
terminal endpoints outside the domain and interior parameters whose image is
a boundary diagonal. It does not supply arbitrary quitting-game homotopy data
or prove Simon's extended-orbit conclusion. The cap-saturation theorem shows that the full invariant-set
alternative always admits a contractible certificate whenever it admits any
certificate. It excludes an ordinary homology obstruction to that alternative;
it neither excludes every smooth potential nor constructs a counterexample.
The full game adapter and the nonconvex finite-union case remain open. No
export is requested by this notebook.

## Exact question and semantic data

Let I be a nonempty finite player set, and let r(S) in R^I be the reward at
each nonempty coalition S. Fix R >= 0 with |r_i(S)| <= R. Independent
behavioral stopping laws, with arbitrary finite stopping dates and Never,
are the strategy space. Infinite all-Continue pays zero. A unilateral
deviation replaces a player's entire law. No public correlation is added.

For a behavioral profile p, let U(p) be its terminal expected payoff and
B_i(p) the supremum over every replacement law of player i. Write

    K = closure { (U(p), B(p)) : p is a behavioral product profile },
    Z = [-R,R]^I x [-R,R]^I,
    d(u,b) = max_i (b_i-u_i).

For a root x in [0,1]^I put c(x)=product_i(1-x_i), and let g_i(x) be the
unconditional expected reward from nonempty absorption at that root. Let
Q_i(x) be the payoff from quitting now, A_i(x) the unconditional reward
from nonempty opponent absorption while i continues, and
alpha_i(x)=product_(j!=i)(1-x_j). Exact semantic prefixing is

    T_x(u,b) = (g(x)+c(x)u,
                  (max(Q_i(x), A_i(x)+alpha_i(x)b_i))_i).       (1)

The carrier K is compact, contains the all-Never semantic pair, is preserved
by every T_x, and has nonnegative coordinate debts. The complete negative
alternative asks for a closed C in Z containing the all-Never pair, preserved
by EVERY T_x, with d >= Gamma > 0 everywhere. There is no restriction to
bounded controllers, selected roots, or a particular component.

The question tested here is whether topology of such C can force a diagonal
point b=u. The answer is negative for any proposed obstruction requiring
nontrivial homology or failure of contractibility: a certificate can always
be made contractible while preserving the same strict gap.

## Cap saturation preserves the full negative certificate

For any closed prefix-invariant C in Z, define

    C^up = { (u,b) in Z : there exists beta <= b with (u,beta) in C }.
                                                                  (2)

The comparison is coordinatewise; prescribed payoff u is unchanged.

**Theorem.** The set C^up is compact, contains C, is invariant under every
product-root prefix, and has the same positive gap lower bound as C. If
every point of C has b >= u, then every point of C^up also has b >= u.

**Proof.** Compactness follows by projecting the compact set of triples
(u,beta,b) with (u,beta) in C, beta <= b, and b in the box. Inclusion is
immediate. The first component of T_x is independent of the input cap; its
second component is coordinatewise increasing in that cap because
alpha_i(x) >= 0. Thus

    pi_u T_x(u,beta) = pi_u T_x(u,b),
    pi_b T_x(u,beta) <= pi_b T_x(u,b).

Prefix invariance puts the left pair in C; all coordinates of the right
pair remain in the reward box. Therefore T_x(u,b) belongs to C^up.
Finally b >= beta implies d(u,b) >= d(u,beta), preserving the original
Gamma with no loss. The coordinate-debt assertion has the same proof.

This is not the known debt-saturation operation. Debt saturation translates
payoffs AND caps while keeping b-u fixed and is impossible for positive-gap
certificates. Here only caps increase, and debt can increase. No unsupported
cap is claimed to be the actual cap of an executable profile. Invariant
certificates are allowed to contain supersets of the actual carrier.

## Every saturated certificate is contractible

Let P be the payoff projection of C, which is also the payoff projection of
C^up. Let top=R*1 and full=r(I).

First the continuous homotopy

    (u,b) |-> (u,(1-t)b+t*top),         0 <= t <= 1,             (3)

stays in C^up by cap saturation. It is a strong deformation retraction onto
the section P x {top}: every point of that section is fixed at every t.

Next give each player quit probability t at a single root, denoted x(t).
Define

    f_t(u) = g(x(t))+c(x(t))u.                                  (4)

For u in P choose ANY cap beta with (u,beta) in C. Prefix invariance implies
f_t(u) in P. The definition of f_t is independent of that choice; no
continuous choice of beta is needed. Moreover

    f_0(u)=u,             f_1(u)=full.                          (5)

The latter uses I nonempty, so the full-Quit root absorbs surely at I.
The map (t,u) |-> f_t(u) is polynomial and hence continuous. Consequently
f_t contracts P, and (f_t(u),top) contracts P x {top} inside C^up.
Concatenating (3) and (4) contracts C^up to (full,top).

**Corollary.** If eta(r)>0, the canonical choice C=K gives a closed,
contractible, full-prefix-invariant certificate C^up with the exact same
lower bound eta(r). Conversely, any such certificate is already a valid
certificate in the unrestricted invariant-set alternative. Thus imposing
contractibility on the invariant certificate does not change the sign
problem at all.

The proof does not assert that K itself is contractible. It DOES show that
its payoff projection is contractible, for every table. Upward cap saturation
is essential for the explicit contraction of the pair set.

If a supplied C has a semialgebraic description, (2) has one by real
quantifier elimination, and the displayed contraction is semialgebraic.
This conditional observation supplies no semialgebraic certificate producer.
The topological theorem itself uses no quantifier-elimination input.

## Exact tests and boundaries

1. One player, r({1})=1, R=1. A law that quits with total probability p has
   semantic pair (p,1). Hence K=[0,1] x {1}, already contractible, and
   eta=0. Formula (4) is f_t(p)=t+(1-t)p. This verifies the endpoint and
   the fact that contractibility alone contains no sign information.
2. For two players, let r({1})=(1,-1), r({2})=(-1,1), and
   r({1,2})=(0,0). Immediate simultaneous quitting has pair ((0,0),(0,0)).
   A silent prefix has pair ((0,0),(1,1)), because either player can quit
   alone in the inserted round. Thus T_0 is NOT the identity on the full
   semantic carrier. A purported contraction of K obtained by setting
   x=t*1 and calling t=0 the identity has this exact false step.
   In (4), only the PAYOFF projection is used, on which t=0 is the identity.
3. Caps increased in (3) remain at most R. The invariant-set argument never
   needs an unbounded cap, a change to the reward table, or a changed gap.
4. The synchronized root x(t) means independent Bernoulli(t) choices. It
   does not mean a public lottery between all-Continue and all-Quit; the
   intermediate g(x(t)) retains every collision coalition.
5. The statement is about existence of a topologically simple certificate,
   not about continuous production of its actual strategy witnesses. The
   witness beta used in (4) may vary discontinuously with u without affecting
   the explicitly defined homotopy.

## Exact sources inspected and comparison

The route began with the controller-tester question and the potential section
of `docs/TOOLKIT.md`. Exact source declarations inspected were:

- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
- `IsQuittingFloorFreeRobustEdge` and
  `quittingFloorFreeRobustChargedRelation` in
  `UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`;
- `IsQuittingFullExactRootPotential` and
  `isQuittingFullExactRootPotential_of_robustPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`;
- `IsQuittingFullExactRootPotential.minimum_exactRoot_absorption_eq_zero`
  and `IsQuittingFullExactRootPotential.minimum_above_singleton` in
  `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMinimum.lean`;
- `quittingTerminalSemanticPrefix`, `quittingTerminalSemanticCarrier`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`; and
- `IsDebtSaturated` and
  `not_positiveDebtFloor_of_never_prefixInvariant_debtSaturated` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticDebtSaturatedBarrierNoGo.lean`.

The polynomial characterization constructs an arbitrary-degree rational
potential from a hypothetical counterexample; it is not an assumed producer.
Its all-Continue escape at global minima and the existing face/reflection
exclusions do not settle the all-degree alternative. The present theorem
does not revisit those polynomial classes.

No Lean command or implementation was run. The topological and saturation
claims here are ordinary mathematics under (1), with no external theorem
beyond compactness, projection of a compact set, and the displayed homotopy.

## 7. Convex-domain exclusion of every smooth strict graph potential

### Exact finite-dimensional statement

Let C be a nonempty compact convex subset of Euclidean R^n, n>=1, with
nonempty interior. A polytope is allowed but not required. Let

    f,g : C -> R^n

be continuous, with f(x)=g(x)=x for every x on the boundary of C. Assume
only the following diagonal-image condition:

    f(z)=g(z)  =>  f(z) belongs to boundary C.                 (14)

In particular, an INTERIOR parameter z may map to a boundary diagonal.
The stronger assertion f(z)!=g(z) throughout the interior is NOT assumed.

Let Omega be an open subset of R^n containing C, f(C), and g(C), and let
H:Omega->R be C^1. Suppose:

1. For every z with f(z)!=g(z), H(g(z))<H(f(z)).
2. For every x in boundary C, there is y_x in C such that

       gradient H(x) dot (y_x-x) < 0.                        (15)

**Theorem candidate.** These data cannot exist.

There is no convexity assumption on H, degree bound, continuous selection of
y_x, or restriction that f(C) and g(C) lie in C. The auxiliary projected map
below is a proof device, not a supplied root selector or strategy.

### A uniform descent perturbation of the boundary

Write P_C for the Euclidean metric projection onto C. Define, for y in Omega,

    W(y)=P_C(y-gradient H(y))-y.

Projection is continuous. At x in C its variational inequality gives

    gradient H(x) dot W(x) <= -||W(x)||^2.                    (16)

Indeed, compare the projecting point P_C(x-gradient H(x)) with the feasible
point x. Moreover W(x)=0 would imply
gradient H(x) dot (y-x)>=0 for EVERY y in C. Thus (15) implies W(x)!=0 at
every boundary point. Compactness of the boundary gives beta>0 with

    gradient H(x) dot W(x) <= -beta  on boundary C.

By continuity choose an open neighborhood U of boundary C with compact
closure in Omega such that gradient H(y) dot W(y)<=-beta/2 throughout U.
Choose a continuous cutoff chi:R^n->[0,1], equal to one on a neighborhood of
boundary C, with compact support K contained in U. On K the vector W is
bounded. The positive distance from K to the complement of U, and uniform
continuity of gradient H on a compact neighborhood of K in U, allow one
constant e in (0,1] such that, for all y in K and 0<=t<=1,

    y+t*e*chi(y)*W(y) belongs to U,
    gradient H(y+t*e*chi(y)*W(y)) dot W(y) <= -beta/4.         (17)

Only this compact neighborhood is used; no values of H outside Omega are
invoked. Define T:Omega->Omega by

    T(y)=y+e*chi(y)*W(y)

on the support neighborhood and T(y)=y elsewhere. The cutoff makes this
continuous across the support boundary. Integrating the directional
derivative along the segment in (17) proves

    H(T(y))<=H(y) for all y in Omega,
    H(T(y))<H(y) whenever chi(y)>0.                           (18)

For x in boundary C, chi(x)=1 and

    T(x)-x=e W(x),       x+W(x) belongs to C.                 (19)

This construction explicitly handles endpoints outside C. Points outside the
cutoff support are unchanged, and all moved segments lie inside U⊂Omega.

### Brouwer contradiction without a degree assertion

Define a continuous vector field on the PARAMETER domain C by

    Z(z)=T(g(z))-f(z).

It is nowhere zero. If f(z)!=g(z), hypothesis 1 and (18) give
H(T(g(z)))<=H(g(z))<H(f(z)). If f(z)=g(z), (14) places their common value on
boundary C, where (18) is strict. Thus the allowed interior diagonal images
are removed by an actual descent perturbation; they are not silently deleted.

The map z -> P_C(z+Z(z)) is a continuous self-map of compact convex C.
Brouwer supplies a fixed point z. Projection's variational inequality then
says

    Z(z) dot (y-z) <= 0  for every y in C.                    (20)

If z is interior, choose y=z+t Z(z) in C for sufficiently small t>0.
Equation (20) contradicts Z(z)!=0. If z is on the boundary, f(z)=g(z)=z
and (19) give Z(z)=e W(z). Choose y=z+W(z) in C. Then (20) says
e||W(z)||^2<=0, again a contradiction. This proves the theorem.

The proof uses only the usual finite-dimensional projection inequalities,
compactness, continuous cutoff functions, and Brouwer's fixed-point theorem.
It does not use a differentiable f or g, a nonzero difference on the interior,
a source projection of degree one, or a claimed repeatable graph orbit.

### Consequence for the one-polytope Simon hypotheses

Take `QuestionOneHypotheses` from
`MathUE/Topology/SimonViabilityQuestion.lean` with pieceCount=1. Then C is
the single full-dimensional compact convex polytope. Put

    (f(z),g(z)) = homotopy(z,1).

The actual source clauses give continuity, f=g=id on boundary C, and precisely
the diagonal-IMAGE implication (14). They do not give an interior-parameter
nonvanishing statement.

Suppose H is C^1 on an open neighborhood of C together with both coordinate
projections of the full graph J, and for some c>0 satisfies

    H(x)-H(y) >= c ||x-y||  for every (x,y) in J.             (21)

Terminal homotopy pairs lie in J, so (21) gives hypothesis 1. At any boundary
x, the local escape clause supplies y at positive distance from x, with
distance(y,C)<=distance(x,C)=0 and the whole segment [x,y] contained in the
local fiber over x. Closedness of C gives y in C. For every t in [0,1], the
pair (x,x+t(y-x)) lies in the local graph and hence J. Applying (21), dividing
by t>0, and letting t decrease to zero yields

    gradient H(x) dot (y-x) <= -c ||y-x|| < 0.

The theorem therefore excludes EVERY C^1 potential satisfying (21) under the
one-polytope Simon hypotheses. In particular it excludes every polynomial,
without a degree cutoff. Compactness and contractibility of graph fibers are
not needed by this exclusion once their displayed boundary escape is present.

This is not an affirmative answer to Simon's orbit question: no necessity
theorem has been supplied turning absence of such a smooth potential into an
unbounded-variation extended orbit. Nor is a merely bounded, discontinuous,
or piecewise potential covered by the C^1 theorem without further work.

### Exact quitting adapter and its unresolved inputs

For rewards bounded by M and a full robust edge (v,q,w) in the box of radius B,
with tolerance delta>=0 and absorption a, the Bellman residual and reward
bound give directly

    ||w-v||_infinity <= (M+B+delta)*a,
    ||w-v||_2 <= sqrt(n)*(M+B+delta)*a.                      (22)

Indeed the exact successor is (1-a)v+a*rbar with each coordinate of rbar
in [-M,M] when a>0; the a=0 case has w=v. Thus a unit-absorption robust
potential has the metric drift (21), with
c=1/[sqrt(n)*(M+B+delta)] when this denominator is positive.

Consequently the shortest sufficient adapter would produce, in the SAME
robust relation and its existing box:

- a full-dimensional compact convex C and continuous terminal maps f,g;
- f=g=id on boundary C and the diagonal-image implication (14);
- a robust root witness for every terminal pair (f(z),g(z)); and
- for every boundary x, a nontrivial segment into C such that every pair
  (x,x+t(y-x)) has a robust root witness.

These four inputs would reject the arbitrary-degree polynomial produced by
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`.
They are NOT currently produced here. In particular:

* `QuestionOneHypotheses` is a definition, not a game producer.
* `QuittingSimonFEdgeAt` in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean`
  uses support-local absolute epsilon error, not absorption-relative robust
  error. Its graph is not automatically a subgraph of the robust relation.
* `HasQuittingSimonFiniteCellLyapunovCertificate` in the same file is supplied
  finite-cell data, not an arbitrary-game smooth certificate or a source of
  the convex domain.
* `lemma4_5` in `Literature/Simon2012.lean` constructs the question's data only
  under its explicit Section 4 hypotheses. Its domain is `TruncatedW`, a
  union of one truncated piece per player, not the single convex polytope
  required above. That declaration cannot be invoked as the missing adapter.

The open files `notes/SIMON_RESTARTABILITY_ONE_POLYTOPE.md` and
`notes/SIMON_RESTARTABILITY_GENERAL_SPLIT.md` ask for stronger repeatable
orbits. They are not proofs used here. The exclusion is a new candidate
answer about smooth strict potentials only. The general nonconvex finite-union
case remains a separate mathematical obligation; convex projection must not
be used there as if the union were convex.

## Remaining question

The relevant geometry must retain the LOWER cap boundary or a dynamically
constrained deformation: unconstrained upward caps erase every ordinary
topological obstruction while preserving the negative certificate. Can
full-prefix invariance force a diagonal on that lower boundary through its
cap order and actual witness coupling? Contractibility of the surrounding
certificate alone cannot supply that implication. For the new Section 7
candidate, first independently check the cutoff perturbation and the exact
diagonal-image repair. Then determine whether its convex-domain obstruction
extends to the particular truncated-box union in the actual Simon construction,
or whether a genuine same-robust-relation convex-domain producer exists.

## 8. A truncated-box corner obstructs the local inward-descent repair

This is an exact counterexample to one proposed EXTENSION of Section 7,
not a full Simon graph satisfying all seven hypotheses and not a quitting
counterexample. In particular no terminal maps f,g or full invariant graph
are supplied here.

Let

    P1=[-1,0] x [-1,1],   P2=[-1,1] x [-1,0],   C=P1 union P2,
    H(x,y)=x^4+y^4+x^2+y^2+4xy-x-y.

This is the two-piece truncated-box geometry, with a missing upper-right
corner. At every boundary point x of C, and in EVERY piece Pj containing x,
there is a feasible direction v with gradient H(x) dot v<0.

For verification, H_x=4x^3+2x+4y-1 and H_y=4y^3+2y+4x-1.
On x=-1, H_x=4y-7<=-3; on the outer edge x=1 (where y<=0),
H_x=5+4y>=1. The symmetric statements hold on the horizontal outer
edges. The inward coordinate directions therefore work, including the outer
corners and every containing piece there. On the inner edge x=0, 0<y<1,
use the appropriate vertical direction unless H_y=0. If H_y=0, then
4y^3+2y=1 forces y>1/4, so H_x=4y-1>0 and the direction to the left is
strict descent inside P1. The horizontal inner edge is symmetric. At (0,0)
the gradient is (-1,-1): upward descent lies in P1 and rightward descent
lies in P2. Thus even the per-piece boundary version of (15) holds.

Now consider the connected inner-boundary cross

    A = { (t,0):0<=t<=1/4 } union { (0,t):0<=t<=1/4 }.

**Exact obstruction.** There is no continuous T:A->C such that

    ||T(z)-z||_infinity < 1/8,       H(T(z))<H(z)   for all z in A.

Indeed H(t,0)=t^4+t^2-t<=0 on this interval, with strict inequality for
t>0; likewise on the other arm. Consequently H(T(z))<0 throughout A.
But H(x,y)>=0 whenever x<=0 and y<=0, since every displayed term is then
nonnegative. Hence T(A) avoids P1 intersection P2. At z=(1/4,0), the
displacement bound gives first coordinate of T(z)>1/8; membership in C
therefore places this image in P2 without P1. At z=(0,1/4), the image lies
in P1 without P2. A connected subset of C avoiding their intersection cannot
meet both disjoint arms. This contradicts continuity of T.

Thus a continuous arbitrarily small inward descent perturbation cannot be
obtained from per-piece feasible gradient descent merely by replacing convex
projection with a projection or retraction onto the union. Convexification
would fill exactly the missing corner through which the descent map wants to
pass, and would change the boundary problem.

The same local obstruction embeds in four coordinates near an intersection
of two inner faces of the union of coordinate-truncated boxes: keep the
remaining coordinates a positive distance above their truncation thresholds,
add nonnegative squared deviations in those coordinates to H, and restrict
the perturbation to be smaller than that distance. Any transition to either
additional piece is then impossible, while crossing the first two pieces
still forces H>=0. This is a local geometry statement only; it does not claim
that this four-dimensional extension satisfies every global Simon hypothesis.

The convex theorem in Section 7 is unaffected. To treat the actual union,
one needs a different global argument using more than this local inward
descent repair, or an independently justified convex-domain game adapter.
