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
The full game adapter and the nonconvex finite-union case remain open.
Section 10 is a new, complete UNREVIEWED actual-table proof draft: with
nonnegative participant premiums confined to two players, a strict preference
of either core player for the other's singleton over their pair excludes
every smooth full-root potential. It imposes no outsider no-join condition.
Its proposed Fin4 UE consequence uses the existing polynomial obstruction
producer; source non-overlap has only been checked as specified there.
Section 9 shows that the local corner obstruction persists with compact,
contractible local fibers and uniform metric drift. This ends the proposed
local repair by fiber contractibility; it is not a counterexample to the
full homotopy hypotheses. Further work should use the actual four-player
root relation rather than refine that local repair. No export is requested
by this notebook.

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
  error. Its literal graph is not a subgraph of the robust relation. This
  error-mode difference is nevertheless handled by the EXISTING upward
  translation described at the end of Section 9; it is not an additional
  open conversion problem when the translated endpoints fit the box.
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
certificate alone cannot supply that implication. Section 7's cutoff
perturbation and diagonal-image repair have passed independent review.
Sections 8 and 9 now retire the local inward-descent extension to the
truncated-box union, even after using contractible fibers. A genuinely global
argument or an actual same-robust-relation convex-domain producer remains
necessary; neither has been constructed here.

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

## 9. Contractible local fibers do not repair the corner

This is a completed local test and a decision to retire one proof mechanism,
not a new global topological conjecture or a full Simon counterexample. The
reason for testing it is specific: the full source hypotheses include compact,
contractible local fibers, which Section 7 did not use. Those clauses might
have supplied the continuous inward-descent map missing in Section 8. They
do not do so, even with uniform metric drift and long segment escapes.

Keep the two pieces and polynomial H of Section 8. Put rho=1/64 and

    V=[-rho,rho]^2,
    G_x = (x+[0,rho]e1) union (x+[0,rho]e2),   x in V,
    G = { (x,y) : x in V, y in G_x }.

The graph G is compact: it is the union of the two continuous images of
the compact set V times [0,rho]. Every fiber contains its source and is
contractible by the explicit homotopy

    (y,t) |-> x+(1-t)(y-x).

Every fiber is thus a two-arm tree, not a disconnected set of escape
choices. Take J=G; the small-step inclusion into G then holds at every
positive scale.

On the square [-1/32,1/32]^2 both partial derivatives of H are at most

    4(1/32)^3 + 6/32 - 1 < -3/4.

All the displayed fiber segments lie in that square. Integration along
either coordinate segment consequently gives

    H(x)-H(y) >= (3/4)||x-y||_2     for every (x,y) in G.

For every x in V, moving by rho*e2 leaves its distance to P1 unchanged;
moving by rho*e1 leaves its distance to P2 unchanged. Indeed the unconstrained
coordinate remains inside [-1,1], and the other coordinate, which determines
distance to the relevant truncated piece, is unchanged. Both moves have
length rho and their entire segments lie in the fiber. Thus the local
distance-nonincreasing escape clause holds for BOTH pieces at EVERY source
in V, a stronger local assertion than requiring it only at sources within
rho of the relevant boundary piece.

Nevertheless no continuous map T from

    A_rho = ([0,rho] times {0}) union ({0} times [0,rho])

into C can satisfy both

    ||T(z)-z||_infinity < rho/2,      H(T(z))<H(z).

The Section 8 proof applies verbatim at this scale. H is nonpositive on
A_rho and nonnegative on P1 intersection P2. The image must therefore avoid
the intersection. The horizontal endpoint's image has positive first
coordinate and lies only in P2; the vertical endpoint's image has positive
second coordinate and lies only in P1. This contradicts connectedness.

This test supplies all the just-listed LOCAL properties simultaneously.
It deliberately does not supply terminal maps f,g, a neighborhood of the
ENTIRE boundary, or the global homotopy diagonal-image condition. Those are
exactly the remaining possible sources of a global obstruction. Fiber
contractibility alone cannot be invoked to select a short, inward, strictly
decreasing perturbation at a multiple-piece corner. No existence or
nonexistence assertion about quitting equilibria follows from this example.

### Actual-relation boundary for the next attempt

The relevant current source is
`exists_finFour_no_uniformPayoff_iff_exists_boundedSinglePivotPolynomialObstruction`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourBoundedSinglePivotPolynomialObstruction.lean`.
Its right-hand side uses an actual real unit-bounded four-player reward table,
own singleton vector lambda*e_p with lambda>0, no sure-quitter punishment
Nash root, and ONE rational polynomial with full robust drift on box three.
That same polynomial has degree at least three, is not multiaffine, and
satisfies the stated adaptive minimum restrictions. The equivalence neither
assumes nor concludes rational reward entries.

I also inspected the literal definitions `IsQuittingFloorFreeRobustEdge`
and `quittingFloorFreeRobustChargedRelation` in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`, and
`IsQuittingFullExactRootPotential.minimum_exactRoot_absorption_eq_zero`,
`IsQuittingFullExactRootPotential.minimum_singleton_le`, and
`IsQuittingFullExactRootPotential.minimum_above_singleton` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMinimum.lean`.
The robust constraints are absorption-relative in BOTH Bellman residual and
ordinary coordinate Nash regret. There is no support-rationality condition
that may be substituted for them. All roots at a global potential minimum
are silent, and every such minimum lies strictly above all own singletons.

An existing exact conversion must be retained in this comparison. In
`UniformEquilibrium/Quitting/Root/UpwardTranslation.lean`,
`coordinateNashDefect_upwardTranslate_le_absorption` converts a support-local
epsilon-Nash root at v into ordinary regret at most 3*epsilon*a at
v+2*epsilon*1. The same source's
`quittingPayoffUpwardTranslate_sub_successor_eq` gives residual exactly
2*epsilon*a when its exact successor w is translated by the same vector.
Thus an exact `QuittingSimonFEdgeAt` edge yields an ACTUAL full robust edge
for the unchanged table after that common endpoint translation, whenever
3*epsilon<=delta and both translated endpoints are in the robust box.
This is already consumed for packets by `QuittingFiniteForwardPacket.upwardTranslate`
in `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketTranslation.lean`.
No new theorem or improved constant is claimed.

For the unit-bounded Fin4 table and its near-feasible Simon carrier,
epsilon<=delta/3 with delta<=1/4 guarantees these endpoints lie in box
three: each untranslated coordinate has absolute value at most 1+epsilon,
and the translation increases that bound to at most 1+3*epsilon.
Consequently the SAME produced robust polynomial P pulls back to

    H_epsilon(v)=P(v+2*epsilon*1)

and obeys `H_epsilon(v)-H_epsilon(w)>=a` on every such Simon edge.
Since `||w-v||_2<=2(2+epsilon)*a`, this is a global positive metric drift
on that carrier. These are direct consequences of the inspected source
inequalities, not a newly discovered game producer. In particular, a
further support-to-relative-error adapter is not the missing global step.
This observation alone does not extend the potential to the artificial
glue in Simon's full topological graph or produce a charged return.

The next concrete question is whether the actual Nash-root relation for this
single-pivot table forces a positive charged return around its silent region.
Any usable answer must preserve the same table, tolerance, box, and potential
and explicitly use joint-coalition incentives. The singleton-face constraints
and the local topological fiber conditions alone have already been shown
insufficient for the proposed mechanisms. No answer or new producer is
claimed here, and no further generic local-repair lemma is proposed.

## 10. A two-player premium core with a strict preference to leave the pair

**Frozen candidate for independent review.** Complete ordinary proof draft;
not independently reviewed, not Lean-checked, and not exported. This is an
actual joint-coalition argument, separate from the retired topological repair.
The claimed conclusion is a full-root exclusion and, for four players, a
uniform-equilibrium existence theorem for the stated raw class. No broader
two-core theorem or arbitrary Fin4 theorem is asserted.

### Self-contained raw statement

Let I be a finite set with distinct players i,j. Each nonempty coalition
S has a finite real reward vector r(S). Write s_k=r_k({k}). Assume:

1. Every participant premium is nonnegative:
   `r_k(S)>=s_k` whenever k belongs to S.
2. For every k outside `{i,j}`, its participant reward is constant:
   `r_k(S)=s_k` whenever k belongs to S.
3. One designated core player strictly prefers the other singleton to their
   pair:

       r_i({i,j}) < r_i({j}).                              (40)

All nonparticipant rewards are arbitrary. The two core players may receive
independent, arbitrarily large nonnegative premiums on every coalition
containing them; nothing about triples or the grand coalition is suppressed.
Singletons may have arbitrary signs for the analytic statement below.

Choose M>=0 with every |r_k(S)|<=M and choose B>M. Put K=[-B,B]^I.
For an independent product root q in [0,1]^I define

    c(q)=product_k(1-q_k),       a(q)=1-c(q),
    T_q(v)=sum_(S nonempty) Pr_q(S) r(S)+c(q)v.

Let Q_k(q) and C_k(q,v) be the expected rewards when k respectively Quits
or Continues, with annotation v after all Continue. An exact root Nash
equilibrium at v means

    (T_q(v))_k=max(Q_k(q),C_k(q,v))  for every k.          (41)

This is a finite simultaneous-move Nash condition. An annotation need not
be an attainable terminal payoff or the value of a supplied strategy.

**Analytic theorem.** No C^1 function H on a neighborhood of K satisfies

    H(v)-H(T_q(v)) >= a(q)                               (42)

for every v in K and every exact root Nash q at v. This excludes every
polynomial degree, not merely a chosen ansatz.

**Four-player consequence.** If I has four players and all s_k>=0, the
actual quitting game has a uniform-equilibrium payoff. Its strategies use
independent private randomization and observe the public survival history.
Never pays zero. Every unilateral deviation may replace a player's whole
behavioral strategy, including all stopping dates and Never. There is one
fixed payoff target before accuracy; the approximating profile and common
finite-horizon threshold may depend on accuracy. No public correlation or
stationary-deviation restriction is introduced.

### An exhaustive full-root return property

Let

    C=product_k[s_k,B],
    L={x in C : x_k=s_k for at least one k}.

Every exact root Nash successor w=T_q(v) has w_k>=s_k, because
`Q_k(q)>=s_k` by assumption 1 and (41) dominates that Quit endpoint.
If v is in K, then w is also in K: it is a convex combination of v and
the finite reward vectors. Thus w belongs to C.

Suppose now ONLY that v_i>=s_i and v_j>=s_j; the other annotations may
lie below their singletons. For every exact root q at v with a(q)>0,

    T_q(v) belongs to the SAME set L.                     (43)

Here is the exhaustive check, retaining all other players' hazards.

* If any player k outside `{i,j}` has q_k>0, exact Nash and support of
  Quit give w_k=Q_k(q)=s_k. This uses its constant participant reward on
  EVERY coalition containing k, including triples and the grand coalition.
  Other players' hazards and the two core players' premiums may be arbitrary.
  Since w is already in C, this proves w in L in this entire case.
* Otherwise every outside hazard is exactly zero. Only in THIS case is
  the core player's endpoint gap the two-player expression

      Q_i(q)-C_i(q,v)
        =(1-q_j)(s_i-v_i)+q_j[r_i({i,j})-r_i({j})].      (44)

  If both q_i and q_j were positive, (40) and v_i>=s_i would make (44)
  strictly negative, contradicting player i's supported Quit action.
  Thus at most one core player is active. Positive absorption forces
  exactly one active core player k, whose opponents all Continue. Its
  Quit endpoint and hence its actual successor coordinate equal s_k.
  Again w is in L.

In particular, (44) is NEVER applied after ignoring a positive outsider
hazard. Such a hazard has already closed the first case through its own
exact coordinate equality. Formula (43) is a return to L with its original
singleton floors and common upper bound B, not to a different face or to
the boundary of another box.

### The singleton-face derivative inequality

Assume for contradiction that H satisfies (42). Whenever x belongs to C
and x_k=s_k,

    gradient H(x) dot (x-r({k})) >= 1.                    (45)

For completeness, first suppose every other coordinate is strictly above
its singleton. Let k alone quit with probability t>0. It is indifferent,
and every nonowner strictly prefers Continue for sufficiently small t:
its endpoint difference at t=0 is s_l-x_l<0. These are the ACTUAL endpoint
comparisons, including r_l({k,l}) when the nonowner deviates. Hence the
root is exact Nash, its absorption is t, and its successor is
`x+t(r({k})-x)`. Apply (42), divide by t, and let t decrease to zero.

For weak nonowner inequalities, replace each nonowner coordinate x_l by
`(1-epsilon)x_l+epsilon B`, retaining x_k=s_k. Because B>M, all nonowner
inequalities become strict. Apply the preceding argument at each perturbed
point and then use continuity of the gradient as epsilon decreases to zero.
The admissible root rate may depend on epsilon; no uniform eligibility at
intersections of singleton faces is assumed. Upper-box coordinates cause
no difficulty because the successor segment remains in K.

This is also the precise conclusion of
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`.

### The minimizer must have a constant-payoff binding player

Choose x minimizing H on the nonempty compact set L, and let

    J={k:x_k=s_k},       g=gradient H(x).

If J is a singleton `{k}`, the small sole-owner root in the preceding
argument is exact Nash at x, has positive absorption, and returns to L
by (43). Minimality of H on L contradicts (42). Thus |J|>=2.

Increasing one binding coordinate slightly then keeps another coordinate
pinned at its singleton. Therefore g_k>=0 for every k in J. If k is not
in J and x_k<B, two-sided feasible changes give g_k=0. If x_k=B,
one-sided feasible decrease gives g_k<=0.

Suppose J contained no player outside `{i,j}`. Then J is exactly `{i,j}`.
Apply (45) with owner j. Its owner-coordinate term vanishes. Its i-term is

    g_i(s_i-r_i({j})) <= 0,

because g_i>=0 and
`r_i({j})>r_i({i,j})>=s_i`. Every nonbinding interior coordinate has zero
gradient. Every upper-box coordinate contributes a nonpositive term,
since its gradient is nonpositive and `B-r_k({j})>0`. The entire left side
of (45) is consequently nonpositive, contradicting its lower bound one.

It follows that

    J0=J outside {i,j} is nonempty.                       (46)

This is where the actual strict pair-leave preference changes the
minimizer argument. It is not inferred merely from a positive premium.

### Force positive absorption while preserving the two core annotations

For sufficiently small epsilon>0 put

    v_epsilon=x-epsilon*1_J0.

The point remains in K, and its two core coordinates are unchanged and
remain at least their singleton levels. Differentiability gives

    [H(v_epsilon)-H(x)]/epsilon
          tends to -sum_(k in J0) g_k <= 0.               (47)

Choose ANY exact Nash equilibrium q_epsilon of the finite root game at
v_epsilon. Finite Nash existence supplies it without a continuous selector.
All-Continue is not Nash: any k in J0 would gain epsilon by quitting alone.
Hence a_epsilon>0, and the exhaustive argument (43) puts the actual
successor w_epsilon=T_(q_epsilon)(v_epsilon) in the original set L.

For k in J0, `w_epsilon,k>=s_k=v_epsilon,k+epsilon`. The elementary
absorption motion estimate gives

    epsilon <= w_epsilon,k-v_epsilon,k
            <= (M+B)*a_epsilon.                          (48)

Indeed `T_q(v)-v=a(q)(rbar-v)` for a(q)>0, with every coordinate of the
conditional absorption payoff rbar in [-M,M]. Minimality on L and (42)
now imply

    epsilon/(M+B) <= a_epsilon
        <= H(v_epsilon)-H(w_epsilon)
        <= H(v_epsilon)-H(x).

Divide by epsilon and use (47). The positive constant `1/(M+B)` cannot
be at most a nonpositive limit. This proves the analytic theorem.

The proof quantifies over the FULL finite root game at each perturbed
annotation, permits all simultaneous coalitions, and requires neither a
root branch nor a particular active support. It does not assert that an
arbitrary root can be repeated as a terminal Nash strategy.

### The actual four-player semantic consumer

Assume now I has four players and s>=0. Immediate Quit guarantees at least
s_k against every opponent behavior, by nonnegative participant premiums.
Against all-Never opponents the full response cap is exactly s_k. Therefore
the unrestricted punishment vector is exactly s. This agrees with
`quittingPunishmentValue_eq_singleton_of_nonnegativePremium` in
`UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`.
All players are consequently normal.

If all s_k=0, all-Never is already exact Nash at every finite horizon.
Otherwise some singleton is positive. Were there no uniform-equilibrium
payoff, the inspected declaration
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in
`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
would produce a rational polynomial with unit absorption drift on EVERY
full robust edge in box M+2. Every exact Nash/Bellman edge in that box has
zero residual and zero regret, so the same polynomial satisfies (42) with
B=M+2. The analytic theorem excludes it. Thus the original four-player
game admits the stated fixed uniform-equilibrium payoff. No sure-root
alternative is assumed away as an extra raw-table hypothesis: it is part
of the same no-UE implication and the polynomial arm alone is contradicted.

This composition excludes all degrees and uses an actual-table producer
already present in the source. The new mathematical input is the selective
perturbation of binding constant-payoff players, justified by (40)-(46).
Neither a strategy nor a hypothetical good child is supplied to the raw
class theorem.

### Exact tests and bounded source-overlap check

The following fully specified rational table is a useful falsification test.
Let the possible premium recipients be 0 and 1. For every nonempty S let
their reward depend only on its core membership:

| Core membership | r_0(S) | r_1(S) |
| --- | ---: | ---: |
| neither | 0 | 2 |
| only 0 | 1 | -1 |
| only 1 | 3 | 0 |
| both | 2 | 1 |

Set r_2(S)=0 when 2 belongs to S, -1 when 2 does not belong and the core
pattern is only 1, and 3 in all other cases. Set r_3(S)=0 when 3 belongs
to S and 1 otherwise. The own-singleton vector is `(1,0,0,0)` and
`r_0({0,1})=2<3=r_0({1})`. Every participant premium is nonnegative and
only players 0 and 1 have nonconstant participant rewards.

At the product root `(1/2,1/2,0,0)`, both active Quit endpoints strictly
exceed their singletons: they are 3/2 and 1/2. This directly violates
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.
Therefore neither `not_differentiable_absorptionDrift_of_nonnegative_productLow`
in `UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSmoothDrift.lean`
nor `exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`
applies by its displayed premium hypothesis. Under nonnegative premiums,
the checked equivalence in
`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`
also excludes an inference through weak premium support peeling.

More strongly, at annotation `(0,2,3,1)` this table has the unique exact
root `(1/2,1/2,0,0)`. The core endpoint differences are `1-2q_1` and
`4q_0-2`, independent of the outside hazards. Player 3 strictly Continues,
and at the forced core mixture player 2 gets 2 from Continue and zero
from Quit. Its successor is `(3/2,1/2,2,1)`, strictly above every singleton.
Thus the class does NOT satisfy the existing universal boxed-root return
condition: (43) deliberately retains the two core source inequalities.
The source `(0,2,3,1)` violates the pivot's such inequality. This exact
example was independently recomputed here; it is also the table in
`CODEX_HILBERT__TWO_PREMIUM_CORE_STATIONARY_AND_ROOT_CHOICE_BOUNDARY.md`.
That PARTICULAR table already has a UE by a three-player safe-spectator
lift; it is a boundary test, not claimed new coverage of that instance.

The declaration
`weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary` in
`UniformEquilibrium/Quitting/Classification/NonnegativePremiumBoxBoundary.lean`
accordingly does not contradict the theorem: it concerns all annotations
in the box, while (43) is proved only on the specified core-annotation
region and (46) is what permits the carefully chosen perturbation there.
The exact root existence input is `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`.

The raw assumptions impose no outsider joining inequalities and no safe
spectator, response symmetry, selected passive inverse, stationary root,
or supplied F/J weights. I have NOT claimed an exhaustive search proving
that no other implemented producer subsumes this entire class. Independent
review must check both the full-root split in (43) and the selective
boundary perturbation, and separately examine source subsumption before
any export or new-coverage assertion.
