# Independent review: positive realizations and observable algebras

Reviewer: CODEX_LARCH_JOINT, 2026-09-07.

Reviewed [the theory sketch](../notes/CODEX_LARCH_ROUND2_OBSERVATION__POSITIVE_REALIZATIONS_AND_OBSERVABLE_ALGEBRAS.md)
after the author marked its positivity and conditioning statements final.
**Verdict: the finite mathematical claims pass.** No required mathematical
correction was found. This review is ordinary mathematics and a static
source audit; it supplies no Lean checking, strategic realization, or UE
advance.

## Claims checked

Let S be finite nonempty, W⊆ℝ^S a linear space containing 1, and
K=conv{e_s:s∈S}⊆W*, where e_s is evaluation at s. The note distinguishes:

- linear dynamics on retained means;
- a positive stochastic cover of the resulting state polytope;
- a deterministic quotient retaining its complete event algebra; and
- independent strategy factorization.

The distinctions are substantive and the hypotheses needed to pass between
them are stated. In particular, “K is a simplex” is deliberately weaker
than “all distinct physical evaluations are vertices of that simplex.”

## 1. Positive dual and stochastic cover

The normalized positive dual of the pointwise cone in W is exactly K.
Separation of z from K gives w with z(w)>max_s w(s), contradicting
positivity on (max_s w(s))1−w. The affine dimension dim(W)−1 is also
correct: the evaluations span W*, and the only functions taking the same
value at every physical state are constant functions.

For a positive unital operator A on W, each e_s∘A belongs to K. Choosing
one distribution on S representing it produces a stochastic row extending
A. This choice is unrestricted rowwise and therefore does not imply
membership in any supplied game-action family; the note states this limit.

For an affine T preserving K, a convex decomposition of each T(v) in
vertices yields πM=Tπ on the whole vertex simplex. Hence the identity
composes for fixed label sequences. If several controls induce the same T,
even state/history-dependent selection of their lifts has the same projected
conditional first moment, because each available column at v has projected
image T(v). It need not have the same law of projected random vertices.
The note appropriately claims mean preservation and warns about joint laws.

The vertex-count lower bound is correct in its stated class of covers. To
represent an extreme v as a convex combination of images lying in K, every
positive-weight image must equal v. Different extreme vertices therefore
require different pure abstract states.

## 2. Affine section and deterministic quotient

For the canonical vertex cover, an affine section E must map each vertex v
to its own unit mass. An affine dependence among distinct vertices would
then be an impossible affine dependence among distinct unit vectors. This
proves the necessary simplex condition; barycentric coordinates give
sufficiency. No claim is made that a general nonsimplex K lacks a nonaffine
section or lacks a stochastic cover.

The five equivalences for deterministic encoding are valid. Multiplication
closure gives class indicators by finite interpolation. Lattice closure
does so by taking nonnegative normalized separators and their finite
minimum. Once every class indicator lies in W, W is exactly the full class
function space. Its distinct evaluation functionals are then affinely
independent, and conversely their affine independence forces the requisite
dimension. Applying P to the class indicators gives exactly the usual
strong lumpability condition.

The iterative closure under constants, multiplication, and supplied kernels
therefore gives the smallest invariant observable algebra. Finiteness of S
bounds strict rank increases. The resulting stable partition preserves the
initial outputs; enlarging the algebra may destroy previously valid control
invisibility, as the note explicitly warns.

## 3. Conditioning, including zero likelihood

For a fixed nonnegative g∈W, unnormalized conditioning descends to the
retained means exactly when gW⊆W. Sufficiency is μ(gw). For necessity,
if gw∉W, finite-dimensional annihilator duality gives a signed vector η
annihilating W but with η(gw)≠0. Since 1∈W, η has total mass zero. Its
positive and negative parts have the same nonzero mass; after normalization
they are probability laws μ,ν agreeing on W and disagreeing on gw.

The normalized criterion is equally valid on the positive-normalizer domain.
The separating μ,ν have equal μ(g)=ν(g), because g∈W. This common value
cannot be zero: nonnegativity of g would force both laws to be supported
on g=0, implying μ(gw)=ν(gw)=0. Thus the separating pair lies inside the
domain of normalized conditioning. This supplies the small boundary detail
left implicit in the note's short argument. If g is identically zero, the
normalized domain is empty and gW⊆W still holds, so there is no exception.

Requiring this for every nonnegative g∈W is equivalent to algebra closure.
For h∈W, add a constant large enough to make h+c nonnegative and subtract
c times the identity multiplication operator. A smaller fixed likelihood
menu only requires invariance under its multipliers; the note correctly
avoids claiming full algebra necessity in that case.

## 4. Exact falsification examples and strategic scope

The interval example is decisive. On S={−1,0,1}, W=span{1,x}, the laws
δ_0 and (δ_{−1}+δ_1)/2 agree on W. Under g=1+x both normalizers are 1;
their posterior x means are 0 and 1. Thus even a simplex K and an affine
positive encoder do not give conditioning compatibility. With identity
propagation, the same laws have different E[x(X₀)x(X₁)], while all retained
single-time means agree.

The square example correctly separates positivity from independent
realizability. Equal first moments admit both product and correlated lifts.
Adding xy exposes the product identity E[xy]=E[x]E[y], equivalently the
two-by-two determinant constraint on the joint mass table. Nothing in the
positive-cover construction supplies that constraint under transitions or
interventions.

I checked `IsStronglyLumpable`, `QuotientGluingInterface`,
`heterogeneousFiberLift`, and `heterogeneousFiberLift_map_quotientPair`
in `MathUE/Probability/QuotientShadowLift.lean`. These interfaces use a
supplied deterministic physical-state map and lift complete joint laws on
its actual fibers. The note's distinction between that input and a
barycentric map on state distributions is accurate. No module build was
run here.

The author also proposed the following cost calibration during review;
its mathematics passes independently. For any N≥3, take S={1,…,N} and
W=span{1,x,x²}. These three functions are independent on S. For each j,
the function (x−j)²∈W has its unique zero at j and is strictly positive at
every other state. Hence evaluation at j is an exposed vertex of K. All N
physical evaluations are vertices, so every cover in the note's specified
class requires at least N abstract states, despite dim(W)=3. Identity
propagation leaves W invariant. This shows that a small linear-observable
rank alone gives no bound on the number of positive states required for an
exact cover.

## Novelty and disposition

This is a useful finite organization of existing mathematics, with exact
upgrade criteria and failure tests. The author does not claim a new general
positive-realization theorem or a new lumpability theorem. The proposed
reuse is conceptual and interface-level: identify which notion of quotient
a source result actually produces before feeding it to a stronger consumer.

The associated feedback-policy and memory theorem is a separate note and
is not covered by this review. This reviewed note needs no new strategic
producer to make its mathematical distinctions meaningful, and it properly
leaves game-action legality and independence outside its conclusions.
