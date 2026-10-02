# Punishment-free polynomial edges for the normal-game negative certificate

Identity: CODEX_RENY. This is a separate ordinary-mathematics composition,
not part of FRECHET's frozen separator theorem and not independently reviewed
as a combined statement. The analytic mechanism is FRECHET's; ROOT suggested
the finite floor-removal step derived from HILBERT's deficit argument. No
export or Lean claim is made.

## 1. Exact game and the edge relation

There are four players I={0,1,2,3}. A nonempty quitting coalition S pays
r(S)∈ℝ^4, with |r_i(S)|≤M for one fixed M>0. Infinite all-Continue
pays zero. Each player uses an independent private stopping law on
ℕ∪{Never}; unilateral deviations may replace the entire law. Define

    P_i=inf_[independent opponent laws] sup_[own laws] U_i,
    s_i=r_i({i}).

For q∈[0,1]^4 write p_q(S)=∏_[i∈S]q_i ∏_[i∉S](1−q_i),
c(q)=p_q(∅), a(q)=1−c(q), and

    F(q,v)=Σ_[S≠∅] p_q(S)r(S)+c(q)v.

With p_(q,−i)(T) the corresponding opponent coalition probability, put

    Q_i(q)=Σ_[T⊆I\{i}] p_(q,−i)(T) r_i(T∪{i}),
    C_i(q,v)=Σ_[∅≠T⊆I\{i}] p_(q,−i)(T) r_i(T)
                 +p_(q,−i)(∅)v_i,
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

For B≥M and δ>0 let ℛ_δ(B) contain every triple (v,q,w) satisfying

    v,w∈[−B,B]^4, q∈[0,1]^4,
    |w−F(q,v)|∞≤δ a(q),
    e_i(q,v)≤δ a(q)                  for every i.        (R)

There are NO punishment floors in this relation. Its inequalities use only
the raw reward table, root coordinates, annotations, B and δ. A path has
any finite length, any initial state in the box, and successive edges from
this relation; its charge is the sum of a(q). Empty paths are permitted.
Let Cap⁰_δ(B) be the supremum of all such free-start path charges.

Define the separate semantic sure-root condition

    C_sure: ∃k,q, q_k=1 and max(Q_i(q),C_i(q,P))=F_i(q,P)
                        for every i.                    (C)

It is not part of (R). In particular deleting P from (R) does not delete P
from the assumptions of the resulting game characterization.

## 2. Exact combined statement

Assume punishment normality P_i≤s_i for every i and s_j>0 for some j.
Set B=M+2. Then

    no uniform-equilibrium payoff
      ⇔
    not C_sure and there exist δ∈ℚ, 0<δ≤1/4,
      and H∈ℚ[X_0,X_1,X_2,X_3] such that
      H(v)−H(w)≥a(q) for EVERY (v,q,w)∈ℛ_δ(B).          (N0)

The polynomial degree is finite but unbounded across possible certificates.
All roots and all endpoints satisfying (R) must be covered. A finite sample,
selected equilibrium branch, reached component, or positive-absorption
cutoff is not equivalent to this universal condition.

This theorem does not compute P, decide C_sure, give a degree bound or
algorithm, find a positive-gap table, or prove the nonexistence of these
certificates for arbitrary reward tables. A verified certificate together
with the stated hypotheses would imply an unrestricted positive terminal
gap by the existing target-free terminal-Nash/UE equivalence; no quantitative
gap formula from H is asserted.

## 3. Analytic separator without floors

The following statement uses no normality or P:

    Cap⁰_ε(B+1)<∞, 0<ε≤1
      ⇒ ∃H∈ℚ[X_0,X_1,X_2,X_3],
           H(v)−H(w)≥a(q) on every ℛ_(ε/4)(B) edge.     (A0)

Here is the full adjustment to FRECHET's floor-bearing proof. At every
x∈[−B−1,B+1]^4, finite-length capacity maxima exist by compactness of
the finite path fibers, including length zero. Each finite-horizon capacity
is USC by compact subsequence extraction. Their countable supremum Φ is
Borel and bounded by the complete free-start capacity; it need not be USC.
Concatenation gives Φ(v)−Φ(w)≥a(q) on all outer edges.

For h≥0 with |h|∞≤ε/4, simultaneously translating v and w gives

    (w+h)−F(q,v+h)=(w−F(q,v))+a(q)h;
    e_i(q,v+h)≤e_i(q,v)+a(q)|h|∞.

The second inequality follows because the Quit gain drops by c h_i and
the Continue gain increases by (α_i−c)h_i≤a h_i. Thus every translated
inner edge belongs to ℛ_ε(B+1). No floor comparison is needed.

Extend Φ by zero off the outer box and convolve with a smooth probability
density supported in (0,ε/4)^4. The result V is smooth. A neighborhood
of the inner box samples only points in the outer box, and pointwise
integration of the translated inequalities gives V(v)−V(w)≥a(q) for
every inner edge. This is the same one-sided convolution, not a claim of
regularity of Φ itself.

Each inner edge obeys |w−v|∞≤La(q), where L=M+B+ε/4. Approximate V
on [−B,B]^4 in gradient norm by a polynomial p with
sup_x Σ_i|∂_i(p−V)(x)|≤1/(2L). Tensor Bernstein approximation supplies
such a polynomial: its derivative formula averages finite differences of V,
which are averages of ∂_iV on grid segments; uniform continuity and the
vanishing binomial variance give uniform convergence of all four derivatives.
Choose a strict approximation margin first, then perturb its finitely many
coefficients rationally while retaining the bound. The segment formula gives
|(p−V)(v)−(p−V)(w)|≤a/2. Therefore H=2p proves (A0).
At a=0, (R) forces w=v, so the inequality remains exact.

Conversely an all-edge H bounds every finite path charge by its oscillation
on the fixed box. This converse applies in particular to the polynomial H,
whose extrema are attained. These arguments establish (A0) and its converse
without using the floor-removal theorem.

## 4. The game-semantic bridge supplied by finite burn-in

Write WP⁰(B) for the existence of paths from (R) at every positive
tolerance and every requested charge, with B fixed before both choices.
Write WP(B) for the existing producer with its endpoint floors P−δ.
Under normality, the finite burn-in theorem proves

    WP⁰(B) ⇔ WP(B).                                     (B0)

For clarity, the nontrivial direction keeps the SAME word and box after
one request. Given desired floor/tolerance τ>0, choose
0<e≤min(τ,τ/4,τ²/(16M)). Weighted error e supplies each pure endpoint
at most its displayed outward successor plus ζ=2e. A deficit greater than
τ propagates toward construction index zero with increment greater than
κ=τ²/(8M). Since every deficit is at most M+B, all endpoints after L
rows meet P−τ whenever Lκ>M+B. Request charge Q+L, then delete rows
0,…,L−1. Retained error is at most τa, retained charge is at least Q,
and every retained endpoint has the floor. This includes both end cuts.
The reverse of (B0) simply forgets floors.

The existing weighted-packet consumer therefore gives WP⁰(B)⇒UE under
normality. This implication alone does not require a positive singleton.

## 5. Proof of the characterization

If there is no UE, C_sure is absent by its one-player punishment consumer.
By (B0) and the weighted UE consumer, WP⁰(B+1) is false. Negating its
all-tolerance/all-charge statement supplies one t>0 and one unattainable
finite charge target. Hence Cap⁰_t(B+1)<∞. Choose rational
0<ε≤min(1,t); inclusion of relations gives Cap⁰_ε(B+1)<∞. Apply (A0)
to obtain δ=ε/4 and H as in (N0).

Conversely suppose the right side of (N0) holds but UE exists. The reviewed
normal-positive-singleton necessity theorem gives either C_sure or weighted
packets in the EXPLICIT box [−M−2,M+2]^4. The first is excluded. Forget
the packet floors to obtain arbitrarily charged ℛ_δ(B) paths at the very
δ and B of the certificate. Telescoping H bounds all their charges by
one finite oscillation, a contradiction. This proves (N0).

No root or punishment continuation is selected in this contradiction.
Actual full behavioral responses enter through P, the previously proved
sure-root consumer, and the existing packet-to-UE consumer. The polynomial
relation itself uses abstract bounded annotations and literal product roots.

## 6. Dependencies, boundary, and remaining work

The analytic dependency is
[FRECHET's frozen separator](CODEX_FRECHET_CYCLE__WEIGHTED_CAPACITY_POLYNOMIAL_SEPARATOR.md),
SHA `0bef325a34314ffc7e81ab4251c4dfb622ffecff17eaacc426b868f37b4ee2c6`.
Its [independent RENY review](../feedback/CODEX_FRECHET_CYCLE__WEIGHTED_CAPACITY_POLYNOMIAL_SEPARATOR__BY_CODEX_RENY.md)
includes all boundaries and the fixed-box negative characterization.

The new semantic bridge is
[finite forward punishment-floor burn-in](CODEX_RENY__FINITE_FORWARD_PUNISHMENT_FLOOR_BURN_IN.md),
SHA `8b88941767cc9278725140d1e02e3dc14771e95ac75b942b65efd2178876066f`,
with [HILBERT's independent review](../feedback/CODEX_RENY__FINITE_FORWARD_PUNISHMENT_FLOOR_BURN_IN__BY_CODEX_HILBERT.md).
The fixed M+2 necessity and separate C_sure branch are reviewed in
[the complete coverage report](../feedback/CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT__BY_CODEX_RENY.md).
The current checked consumer is
`quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
in `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketProducer.lean`.

FRECHET's exact H-table forward cycle remains a falsification test here:
its three exact floor-respecting edges are also floor-free edges, and charge
3/2 around their cycle contradicts any candidate H. Removing floors cannot
turn that solved cyclic table into a negative example. A zero-absorption
edge is a self-loop and imposes no spurious strict inequality.

The strict change relative to the frozen separator is removal of every
semantic P coordinate from the universal polynomial EDGE TEST. Normality
and the separate not-C_sure hypothesis still depend on P. No inference
that P is jointly realizable, rational, or computed by this argument is
permitted. Earlier complete finite-clock gap searches already provide a
different finite negative-certificate language for rational tables; this
does not claim a first semidecision theorem or an efficiency advantage.

The combined surface still needs its own bounded independent confirmation
before any final assembly. The live mathematical task remains to rule out
all such certificates under not C_sure, or produce one for an actual table.
