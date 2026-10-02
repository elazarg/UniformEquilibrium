# Robust finite-root convexification: the small-piece route stops at the existing returned-block gap

Owner: CODEX_FRECHET_CYCLE. This is a bounded failed-mechanism checkpoint,
not a new producer, table exclusion, or export candidate. The exact seam
calculation below is elementary ordinary mathematics. The stronger
changing-length returned-block obstruction already has a production home.

## 1. Precise candidate and certificate hypothesis

Fix an arbitrary four-player reward table, independent Quit/Continue roots,
Never reward zero, own-singletons s=(1,0,0,0), and |r_i(S)|≤M. Put B=M+2.
For a root q define

    c(q)=∏_i(1−q_i),       a(q)=1−c(q),
    R(q)=Σ_(S≠∅)p_q(S)r(S),
    F(q,v)=R(q)+c(q)v,
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

The supplied polynomial certificate H and rational δ>0 satisfy

    H(v)−H(w)≥a(q)

for EVERY v,w∈[−B,B]⁴ and product q with

    ||w−F(q,v)||∞≤δa(q),       e_i(q,v)≤δa(q) for all i.

This is the full floor-free relation in the frozen
`exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md`,
not a selected-root graph, a semantic carrier, or an exact-edge restriction.
The polynomial itself has four variables; the edge inequalities quantify both
four-vectors and the four root coordinates. No computation of punishment is
used here.

The candidate was: at one continuation v, take finitely many genuine finite
Nash roots qᵏ, and suppose nonnegative weights sum to one and satisfy

    Σ_k θ_k [R(qᵏ)−a(qᵏ)v]=0,
    Σ_k θ_k a(qᵏ)>0.

Could the δa endpoint freedom convert this convex balance into a literal
positive charged return, by implementing arbitrarily small pieces of the
finite roots and cycling through them? No existence of such a balanced family
from arbitrary table data was assumed or proved. This test addressed the
proposed implementation step before trying to obtain the family.

The answer for the small-total-hazard implementation is negative in the
no-homogeneous class, for an already established reason. Finite positive-size
or long nonlocal implementations are not decided by this checkpoint.

## 2. Why private thinning does not preserve a finite collision vector

For a root q let p_q be its coalition law, including the empty coalition.
A public on/off mixture would have law

    μ_t=(1−t)δ_∅+t p_q.

Its Bellman payoff is exactly v+t(F(q,v)−v), and its absorption is ta(q).
This lottery is not automatically an available product root. Its player-i
marginal is tq_i, so an independent root with exactly those marginals is tq.
That root assigns a pair of quitters probability of order t²; μ_t preserves
the original collision law at order t.

More precisely, let κ(q)=Pr_q(|S|≥2)>0. For independent tq,

    Pr_(tq)(|S|≥2)≤t² Σ_(i<j)q_iq_j.

Thus total variation, defined as the supremum of event discrepancies, obeys

    TV(p_(tq),μ_t)≥tκ(q)−t²Σ_(i<j)q_iq_j.

Its ratio to intended absorption ta(q) has positive lower limit κ(q)/a(q).
Even allowing different independent roots p(t), an o(t) approximation of μ_t
would force p_i(t)=tq_i+o(t) by marginal events, after which every pair mass
is O(t²), contradicting the collision event. This concerns coalition-law
preservation, not every possible payoff-preserving implementation.

The literal Bellman seam makes the issue sharper for two active owners. Let
their probabilities be x,y>0, let all other hazards be zero, and abbreviate
their singleton rewards by r_i,r_j and pair reward by r_ij. Then

    F((x,y),v)
      =v+x(r_i−v)+y(r_j−v)
         +xy(r_ij−r_i−r_j+v).

Consequently the desired diluted endpoint and the actual independently
thinned endpoint differ by exactly

    v+t(F((x,y),v)−v)−F((tx,ty),v)
      =t(1−t)xy(r_ij−r_i−r_j+v).

Since a(tx,ty)=t(x+y)−t²xy, their seam/actual-charge ratio converges to

    [xy/(x+y)] ||r_ij−r_i−r_j+v||∞.

This does not tend to zero unless the displayed vector vanishes. Thinning
alone cannot spend an arbitrarily small weighted Bellman budget while keeping
the original finite collision displacement. A symbolic expansion with free
x,y,t,v,r_i,r_j,r_ij verified this identity exactly; no reward fixture or
parameter scan was introduced.

The calculation does not assert that this vector is nonzero at every Nash
root. Nor does it establish that a law-level discrepancy must be detected by
every table's reward coordinates. Its role is to identify the precise seam
which the proposed implementation had omitted.

## 3. The existing returned-block theorem applies to ordinary weighted regret

Write Γ_ji=r_j({i})−s_j. Suppose Γ has no homogeneous simplex solution:
there are no z≥0, Σ_i z_i=1, with Γz≥0 and z_i(Γz)_i=0 for all i.

The production theorem
`QuittingReturnedProductBlock.exists_pos_relativeError_gap_of_noHomogeneous_of_valueBound`
in `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`
gives numbers h₀,c₀>0 such that every returned product block with values bounded
by B and total marginal hazard h∈(0,h₀] satisfies

    c₀h≤BellmanError+endpointRegret.                     (G)

The number of rows is arbitrary, and no fixed source, actual tail realization,
payoff floor, or uniform row-count bound is assumed. Its return is a literal
cyclic equality of the displayed values. Its aggregate Bellman error sums
absolute coordinate errors over all rows.

There is no support-regret mismatch. If Δ_i=Q_i−C_i at one row, the production
endpoint term is

    [(1−q_i)Δ_i]_+ + [−q_iΔ_i]_+.

The two nonnegative terms cannot both be positive, so their sum equals

    max((1−q_i)Δ_i,−q_iΔ_i)=e_i.

Now let a finite forward δ-word close exactly, v_L=v_0. Reverse its cyclic
indexing to obtain the chronological convention used by the production
returned block. Let A=Σ_t a(q_t) and h=Σ_tΣ_i q_t(i). Then

    BellmanError≤4δA,
    endpointRegret≤4δA,
    A≤h≤4A.

The last two inequalities follow rowwise from a≤Σ_iq_i and q_i≤a. Hence

    BellmanError+endpointRegret≤8δh.                   (W)

For δ<c₀/8, (G) and (W) exclude every such return with 0<h≤h₀. In particular
they exclude every return with 0<A≤h₀/4. Conversely, any sequence of exact
returns in the fixed box with positive charge tending to zero and weighted
tolerances tending to zero yields a homogeneous simplex solution by
`QuittingReturnedProductBlock.hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks`
in the same source file.

An approximate return with seam o(h) has the same consequence if that seam is
included in the aggregate Bellman error. It is not legitimate to leave the
closing seam uncharged. For example, replacing one final cyclic endpoint adds
at most the sum of its four coordinate discrepancies to BellmanError. The
ordinary regret terms need not change under the indexing convention which
keeps each row's continuation annotation fixed.

Thus a chattering argument that claims a vanishing-total-charge cycle at
arbitrarily accurate weighted tolerances would only rederive the already
known homogeneous singleton branch. It cannot preserve genuinely finite
collision information in a new way. This conclusion is independent of the
particular polynomial H; H was the motivation, not an extra assumption needed
for this old obstruction.

## 4. Narrow source comparison and scope

The route was `docs/TOOLKIT.md` entries for absorption-weighted packets and
the returned-block homogeneous tangent obstruction, followed by their named
source files. `QuittingAbsorptionWeightedForwardPacket` in
`UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacket.lean`
confirms the ordinary per-coordinate regret and absorption-weighted residual
convention. The newer floor-free formulation drops only its floor fields.

Related but different existing results were inspected:

- `scale_eq_one_of_conditionedProductPurification_two_active` and
  `no_conditionedProductPurification_of_two_active_phantom` in
  `UniformEquilibrium/Quitting/Cycles/ConditionedProductPurification.lean`
  concern exact preservation of the conditioned nonempty coalition law.
  They are not by themselves a no-go for arbitrary free-box payoff words.
- Propositions 9–10 of the reviewed ordinary note
  `CODEX_CEDAR__KILOBLOCK_SIMULTANEOUS_HAZARD_PURIFICATION.md` concern an actual
  supplied public macro, payoff/advance preservation, and deleted-clock
  refusal gains. Their supplied-source requirements are not assumed here.
- The exact nonconvex jump-image regression in
  `formalized/EXACT_ONE_JUMP_AND_PROPER_SINGLETON_FLOW_CLOSURE.md` rejects
  treating a convex combination as one selected exact jump. It does not prove
  that the midpoint fails to be a uniform payoff.
- `ReturnedBlockTangentGap.lean` supplies principal-matrix versions. Only the
  full ambient no-homogeneous theorem was used above; no principal-to-ambient
  restriction adapter was silently invoked.

No fresh Lean build was run. This notebook supplies no new raw-table coverage,
no new necessary table condition beyond the established homogeneous tangent
obstruction, and no conclusion about fixed positive-size returns or long
nonlocal words whose total charge stays bounded away from zero. Those can use
finite collision effects and are not reduced to independent infinitesimal
thinning. The small-piece convexification mechanism is stopped.
