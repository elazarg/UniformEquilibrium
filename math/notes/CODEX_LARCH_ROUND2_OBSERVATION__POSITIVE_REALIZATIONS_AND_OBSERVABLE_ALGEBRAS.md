# Positive realizations and observable algebras

Author: CODEX_LARCH_ROUND2_OBSERVATION. Internal theory sketch, 2026-09-07.

## Current mathematical conclusion

The [linear-observability sketch](CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT.md)
has a useful finite positive-realization extension. Four structures should
remain distinct:

1. an invariant linear space of observables, which preserves their means;
2. its canonical positive state polytope, which always has a finite
   stochastic cover intertwining the mean dynamics;
3. an observable algebra, which gives a genuine deterministic quotient of
   states without adding observables; and
4. a factorized strategy realization, which has additional independence
   and information constraints not supplied by any positive cover.

The core results below are elementary ordinary mathematics and primarily
consolidate established ordered-vector-space and lumpability ideas. They
are not claimed as foundational novelty or a general positive-realization
theorem for arbitrary infinite processes. Their value is to explain why
linear invariance, probabilistic lifting, and independent strategy
factorization are different interfaces in this codebase.

No Lean changes, exports, or UE proof-search are part of this investigation.
The central statements passed
[independent mathematical review](../feedback/CODEX_LARCH_ROUND2_OBSERVATION__POSITIVE_REALIZATIONS_AND_OBSERVABLE_ALGEBRAS__BY_CODEX_LARCH_JOINT.md),
with no unresolved objection. The scope remains ordinary mathematics, not
Lean verification.

## 1. The canonical positive state polytope

Let S be a nonempty finite set and let W⊆ℝ^S be a linear subspace containing
the constant function 1. Let e_s∈W* be evaluation at s. Define

    K = conv{e_s : s∈S},
    C = {w∈W : w(s)≥0 for every s∈S}.

The quotient of a state distribution μ is its restriction to W:
q(μ)=sum_s μ(s)e_s. Thus K is exactly the image of the probability simplex.
It has affine dimension dim(W)−1, even when many source states have distinct
evaluations that are affinely dependent or interior points.

**Positive-state characterization.** K is also exactly the set of linear
functionals z∈W* with z(1)=1 and z(C)≥0.

One direction is immediate. Conversely, if a normalized positive z lies
outside K, finite-dimensional convex separation gives some w∈W with
z(w)>max_s w(s), after changing its sign if necessary. But
(max_s w(s))1−w belongs to C, contradicting positivity. This identifies the
correct cone intrinsically; entrywise positivity in an arbitrary coordinate
basis of W is not the right condition.

If a stochastic kernel P satisfies PW⊆W, its restriction A=P|W is positive
and unital. The dual map T(z)=z∘A is affine and preserves K, and

    q(μP)=T(q(μ)).                                      (1)

Conversely every positive unital operator A:W→W can be extended to SOME
stochastic kernel on S. For each s, the functional e_s∘A is in K; choose
one probability vector representing it and use that vector as row s. The
extension need not be unique and need not satisfy any prescribed strategic
factorization. This is a finite rowwise feasibility argument, not a claim
that an arbitrary positive operator comes from the original game actions.

## 2. Finite stochastic covers exist without a simplex assumption

Let V be the finite vertex set of K and let

    π:Δ(V)→K,        π(λ)=sum_{v∈V}λ_v v.

For an affine T:K→K, choose for each v a convex representation of T(v) in
the vertices. Put those coefficients in the column of a stochastic matrix
M corresponding to v. Then

    πM = Tπ                                             (2)

on the ENTIRE simplex Δ(V), hence on every representation of every point
of K. Vertex representations of interior points need not be unique. No
simplex assumption is used.

The same construction works for each member of any finite supplied family
of affine maps. The intertwining identity then composes for every fixed
sequence of their labels. If several controls induce the same T, arbitrary
adaptive switching among their chosen stochastic lifts still gives the same
projected mean evolution: at each vertex every row has the same projected
image T(v).

This is a stochastic COVER of the linear quotient. It need not be a
deterministic pushforward of the original trajectory, and the vertex chain
need not reproduce joint laws of observed outputs. Treating its latent
vertices as new public game states or signals would add information.

Among simplex covers whose image is exactly K and whose pure abstract states
map into K, at least |V| abstract states are necessary: every extreme vertex
must be the image of some pure abstract state. Thus the vertex cover has
the minimum size in this specified class. This is not a minimality claim
among every conceivable enlarged positive realization.

### When can one encode the quotient affinely and positively?

There is an affine map E:K→Δ(V) with πE=id_K if and only if K is a
simplex. If K is a simplex, take its unique barycentric coordinates.
Conversely extremality forces E(v) to be the unit vector at v. An affine
dependence among distinct vertices would then become the same nonzero
dependence among distinct unit vectors, which is impossible.

For a nonsimplex polytope one may choose a nonaffine barycentric encoder, or
encode an original distribution using additional source information. What
fails is a positive affine encoder depending ONLY on its quotient point.
Equation (2) still holds. These statements should not be conflated.

## 3. Deterministic quotients require an observable algebra

Define s∼s' when w(s)=w(s') for every w∈W, and let χ map states to these
classes. Let K₀ be the number of distinct evaluations e_s. There is always
an inclusion

    W ⊆ {all functions constant on χ-classes}.

The following conditions are equivalent:

1. W equals all functions constant on χ-classes;
2. W is closed under pointwise multiplication;
3. W is closed under pointwise maximum and minimum;
4. dim(W)=K₀;
5. the distinct evaluations e_s are exactly the vertices of a simplex.

For multiplication closure, finite interpolation builds every class
indicator: for each other class choose a function separating it from the
desired class, normalize that function to be 1 at the desired class and 0
at the other, and multiply the finitely many factors. Conversely class
functions plainly form an algebra. Dimension and simplex characterizations
follow from the independence of the class evaluation functionals.

For the lattice condition, finite minima of nonnegative separating functions
produce class indicators. Explicitly, for two different classes choose w
separating them and normalize its difference to be 1 at the desired class
and 0 at the other, then apply max(0,·). Taking the minimum over other
classes gives the desired indicator. The singleton-class-space case is
just the constants. Hence a unital vector lattice also equals the full
class-function space.

When these conditions hold, PW⊆W is exactly strong lumpability through χ:
apply P to every class indicator to obtain the quotient transition
probabilities. A controlled row difference annihilates W exactly when the
corresponding next quotient-state distributions agree. Thus the original
mean-transport lemma becomes equality of quotient event laws and then of
quotient trajectory laws.

The phrase "without adding observables" is essential. Any finite chain has
the trivial identity quotient, and some kernels admit a useful partition
quotient whose class-function algebra is strictly larger than a given W.
The equivalence above classifies when W ITSELF already supplies the full
event algebra of that quotient.

### Minimal event-compositional completion

Starting from supplied observables and finitely many kernels, close their
linear span under 1, pointwise products, and all the kernels. Each strict
growth increases dimension, so this process stabilizes in ℝ^S after finitely
many rank increases. The result is the smallest invariant observable algebra
containing the original outputs, equivalently the coarsest stable partition
retaining them. This is the algebraic form of familiar partition refinement,
not a newly discovered lumpability theorem.

### Conditioning gives an exact composition test

Let g∈W be a nonnegative likelihood. Unnormalized conditioning sends a
probability law μ to the finite measure gμ. The induced operation on its
retained observables is well-defined from q(μ) alone if and only if

    gW⊆W.                                               (3)

Sufficiency follows from (gμ)·w=μ·(gw). For necessity, differences of
probability laws agreeing on W span its annihilator: since 1∈W, every
annihilating signed vector has total mass zero, and its positive/negative
parts, after normalization, are two such probability laws. If gw were
outside W, finite-dimensional separation would give two laws agreeing on
W but with different expectations of gw. Thus (3) is necessary.

For normalized conditioning, the denominator μ·g is already retained, so
the same criterion applies on the domain where it is positive. In the
necessity argument, a separating pair with different gw expectations must
have positive common normalizer: if μ·g=ν·g=0, nonnegativity of g forces
both laws onto its zero set and both gw expectations vanish. Requiring
conditioning closure for EVERY nonnegative g∈W is equivalent to W being
an observable algebra: shift any h∈W by a sufficiently large constant to
make it nonnegative, then subtract the constant multiplication operator.
For a specified smaller likelihood family, only closure under those
multipliers is required; a full algebra need not be necessary.

The interval example in Section 4 makes the difference exact. The laws
δ_0 and (δ_{−1}+δ_1)/2 agree on W=span{1,x}; the likelihood g=1+x has
normalizer one under both. Their posterior x means are respectively 0 and
1. A simplex state image and positive affine encoder therefore do not
ensure conditioning-compatible observation. This calculation was suggested
by the coordinating reviewer; its finite necessity argument is included
above.

Newly added product/event observables may expose controls that annihilated
the smaller linear W. One must recheck row agreement after completion.
Preserving a specified finite list of maxima can require less than the full
algebra; no necessity claim for every individual cap calculation is made.

## 4. Exact examples separate all three quotient notions

**Signed coordinates can represent positive dynamics.** Let
S={−1,0,1}, W=span{1,x}, x(s)=s. Its cone is a≥|b| for functions a+bx.
The map x↦−x has a negative matrix coefficient in this basis but is a
perfectly positive unital map: it comes from swapping states −1 and 1.
Rejecting signed reduced matrices would confuse coordinates with positivity.

**A simplex image is not enough for a deterministic quotient.** In the same
example K is the interval with vertices e_{−1},e_1. It has an affine
positive encoder, but e_0 is their midpoint. The encoder sends original
state 0 to a half-half distribution on abstract vertices. It preserves the
mean of x, not the law of its observed value. Since x separates the three
states, its deterministic event quotient has three states and function
space span{1,x,x²}. Hence W is not an observable algebra despite K being
a simplex.

With P the identity, the source distributions
μ=(δ_{−1}+δ_1)/2 and ν=δ_0 agree on W for all times, but
E_μ[x(X₀)x(X₁)]=1 and E_ν[x(X₀)x(X₁)]=0. Multiplication exposes a
distinction invisible to every single-time linear mean.

**A nonsimplex positive realization.** Let S={−1,1}² and
W=span{1,x,y}. Then K is a square, with four vertices and linear dimension
dim(W)=3. Every positive induced affine map has a four-state vertex cover,
but there is no affine positive encoder K→Δ(4) inverse to π. The two
decompositions of its center into opposite corners already contradict such
an encoder. Completing W by products adds xy and yields the full
four-state event algebra.

**Small linear rank need not reduce positive-state count.** For any N≥3,
take S={1,…,N}, x(s)=s, and W=span{1,x,x²}. Its dimension is three,
but all N evaluations are exposed vertices of K: the nonnegative observable
(x−j)² belongs to W and uniquely vanishes at state j. Identity propagation
preserves W. Therefore any exact positive simplex cover whose image is K
needs at least N states, and the vertex cover attains that bound. This
distinguishes low linear prediction rank from a small stochastic-state
realization, without a complexity conjecture or an asymptotic approximation.

## 5. Why positivity does not supply independent strategy factorization

In the square example, a point (m_x,m_y) has an independent product
realization with four masses (1±m_x)(1±m_y)/4. This is a legitimate but
nonlinear choice of encoder. Arbitrary convex representations of that same
point are generally correlated. At the center, a half-half lottery on the
two equal-sign corners has the same x and y means as two independent fair
coins, but it has E[xy]=1 instead of 0.

If xy is also retained, independent realizability imposes the extra equation

    E[xy] = E[x]E[y],

or equivalently, in four joint masses,

    p_{00}p_{11}=p_{01}p_{10}.

This is not a positivity constraint on a polytope. Thus a positive Markov
cover or a probabilistic fiber lift cannot silently supply an independent
product action profile. A supplied nonlinear product encoder may be enough
for one observation point, while compatibility with several controlled
transitions or interventions requires additional identities.

Support constraints are also relevant to lifts: if a quotient vertex is
extreme, every representing source distribution is supported on its
evaluation fiber. At nonextreme points the representation may mix different
original evaluation fibers. This distinguishes deterministic fiber lifts
from generic barycentric covers and explains why support information cannot
be inferred from matching means.

## 6. Control and composition boundaries

The original observable-space criterion handles every adaptive unilateral
intervention whose row differences annihilate W. Its proof remains valid
in the polytope representation because all such interventions have the SAME
induced map T. No hidden vertex information is needed to choose an action.

For controls inducing different maps T_a, a finite family of vertex lifts
immediately realizes fixed/open-loop action-label sequences. It does not
automatically preserve policies that choose labels using full original state
or newly introduced latent vertices. Which feedback policies descend is a
separate information condition. The
[feedback and memory sketch](CODEX_LARCH__OBSERVABLE_FEEDBACK_CLOSURE_AND_MEMORY.md)
treats that rowwise-feedback question; its theorem is not reproduced here.

Likewise, closure under baseline propagation explains preservation under
temporal composition of linear outputs; closure under products or lattice
operations explains arbitrary event tests and nonlinear composition.
The quitting common-witness regression fails already at propagation
closure. The square example passes linear propagation but fails event
composition. These are different reasons for a purported statistic to be
insufficient.

## 7. Code correspondence, overlap, and novelty verdict

`IsStronglyLumpable` and `QuotientGluingInterface`
(`MathUE/Probability/QuotientShadowLift.lean`) assume a supplied deterministic
χ and actual quotient transition laws. `heterogeneousFiberLift` then
disintegrates a full-state law over those literal fibers. The file explicitly
does not construct χ or assert strategic legality. A barycentric map from
distributions into K is not such a χ; applying that interface directly to a
linear observable quotient would have the wrong type of input.

The neighboring note identifies exact invisibility and residual-account
declarations, and the common-witness regression. Those remain examples of
linear transport and its failure. The present addition explains when that
linear object upgrades to the deterministic probabilistic quotient required
by the existing lift interface, and when only a stochastic cover exists.

A bounded search of the adjacent probability sources and conference notes
did not find this four-way distinction packaged as one interface. Generic
strong lumpability and product-factorization obstructions are already
present. The candidate contribution is their common finite ordered-space
organization, including the simplex section criterion and the algebraic
completion procedure. These are standard mathematical facts assembled into
a potentially useful theory layer, not novelty claims about positive
realization, state minimization, or the UE conjecture.

Independent review checked the vertex-cover intertwining, affine-section
criterion, observable-algebra and conditioning equivalences, and their
examples, including the difference between simplex K and deterministic
encoding of every original state. The zero-normalizer clarification was
incorporated. No equilibrium source-production task is proposed.
