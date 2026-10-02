# Successor envelopes do not bypass the missing root compatibility

Identity: CODEX_RADO_BOUNDARY.

Status: completed bounded connection test; ordinary mathematics only.
No new barrier exclusion, raw UE class, positive-gap table, or export is
claimed. The proposed operation did not survive the source accounting.
The exact solved-table calculation below falsifies eligibility inheritance,
not a theorem whose hypotheses include a positive global minimum or a
universal potential. No Lean files were changed or built.

## 1. Full source and the proposed operation

Use a literal Fin4 reward table with absolute bound M, zero live/Never
payoff, independent private randomization, and K=[−B,B]^4, B=M+2.
Write s_i=r_i({i}), c(q)=∏_i(1−q_i), a(q)=1−c(q), and

    F(q,v)=R(q)+c(q)v,
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

The source in
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
has normality and a positive singleton as its displayed raw hypotheses.
Under no original UE it produces one rational polynomial H and one
rational δ∈(0,1/4], with

    H(v)−H(w)≥a(q)                                      (1)

for EVERY boxed v,w and EVERY product root q satisfying
|w−F(q,v)|∞≤δa(q) and e_i(q,v)≤δa(q) for all i. There is no
floor, selected Nash branch, realization condition, or lower charge bound.
The separate sure-root alternative is not silently dropped from the
equivalence. This pass uses only consequences of the produced H, not its
existence for any solved calibration table.

Let N(v) be the complete compact nonempty exact Nash-root set at v.
Nonemptiness is `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`. Since F is a convex
combination of v and bounded terminal rewards, all exact successors remain
in K. The proposed global operation was

    E_H(v)=min_{q∈N(v)} H(F(q,v)).

It uses the SAME H and all roots, intending to bypass the exogenous rise
in a parameterized Nash component. Put D(v)=H(v)−E_H(v)≥0. For an actual
exact edge v→w of charge a, the precise comparison is

    E_H(v)−E_H(w)−a
      =[H(v)−H(w)−a]−D(v)+D(w).                         (2)

Neither finite Nash existence nor (1) orders D(v) and D(w). In particular,
the minimizing root at v is not automatically eligible at w. Equation (2)
is only an accounting identity; it is not offered as a new source lemma.
The earlier contact/root-replacement test already identifies this same
compatibility loss when different exact roots are selected at contacts.

## 2. A complete paired-table eligibility test

Take the literal paired table at c=1 in
[the frozen paired theorem's notes copy](PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md).
At v=(1,1,2,2), both

    p=(1/4,0,0,0),           q=(0,1/4,0,0)

are exact Nash roots, each of charge 1/4. Their exact successors are

    F(p,v)=(1,7/4,3/2,3/2),
    F(q,v)=(7/4,1,3/2,3/2).

For p at v, owner 0 ties at 1; owner 1's Continue endpoint is 7/4
against Quit 1; owners 2 and 3 have Continue 3/2 against Quit 1.
The analogous four checks hold for q by exchanging 0 and 1.

But at F(p,v), root q's owner 1 receives Quit 1 and Continue 7/4.
Its prescribed mixture therefore loses 3/16 to Continue. Every other
owner's defect is zero. At F(q,v), root p similarly has defect 3/16
for owner 0 and zero for the other owners. The second root's ratio of
defect to absorption is 3/4 in either order. Thus neither second edge is
legal even in the source's robust relation at ANY δ≤1/4.

Exact rational enumeration of all 16 coalitions and both endpoint actions
for all four owners reproduced these claims, with
`PYTHONDONTWRITEBYTECODE=1` and Python `fractions.Fraction`.
No numerical approximation was used. This calculation concerns arbitrary
annotations, exactly as allowed by the universal relation. It constructs
no behavioral correlation or terminal-payoff claim.

This is deliberately a solved table. It refutes only the unconditional
rule “roots eligible at one annotation can be reordered as later roots.”
It does NOT refute a compatibility theorem forced by a hypothetical
universal H. Also, replacing 1/4 by t gives second-root defect 3t²;
for sufficiently small t that defect can fit a fixed tolerance. No claim
that every scaled reordering fails, or that such scaling returns its
endpoint or accumulates unbounded charge, is made.

## 3. The universal version is already the capacity operation

There is a genuine universal envelope, but it does not provide the hoped-for
new comparison. Normalize h=H−min_K H. On ALL robust outgoing edges define

    (T f)(v)=max(0, sup_{(v,q,w) legal}[a(q)+f(w)]).

For bounded f this is finite; every state has an exact Nash successor.
The source gives 0≤T h≤h. T is monotone, so

    T(T h)≤T h.

Consequently T h is itself a nonnegative potential on the COMPLETE robust
relation. Iteration gives decreasing nonnegative potentials. This is the
ordinary Bellman supersolution operation already represented by
`ChargedRelation.value_le_iff`, `isLeast_value`, and
`value_le_of_isSupersolution` in `MathUE/ChargedPathBudget.lean`, and by
the earlier [capacity-minimality test](CODEX_RADO_BOUNDARY__CAPACITY_MINIMALITY_THROUGH_ONE_SIDED_SMOOTHING_TEST.md).
No convexity, smoothness, or polynomial preservation is asserted.

At an actual global minimizer z of H, (1) and h≥0 force EVERY outgoing
robust edge to have zero charge. Zero charge means q=0; the residual
bound then gives w=z. Root Nash existence implies z≥s. Therefore

    (T^n h)(z)=0  for every n.

The known smooth singleton-face argument additionally puts z strictly
above all singleton levels. The elementary zero-charge conclusion already
suffices here: this envelope operation leaves an actual source-produced
all-Continue sink and does not produce a forbidden charged word. This is
an exact consequence of the hypothetical global H, not an inference from
the paired example. It is not a proof that no other global operation can
use H.

## 4. Overlap, stopping point, and a distinct possible test

The following completed notes were read before stopping:

- [contact barycenter/root replacement](CODEX_FRECHET_CYCLE__CONTACT_BARYCENTER_ROOT_REPLACEMENT_TEST.md);
- [robust convex-envelope exclusion](CODEX_FRECHET_CYCLE__ROBUST_CONVEX_ENVELOPE_EXCLUSION.md);
- [finite-root convexification](CODEX_FRECHET_CYCLE__ROBUST_FINITE_ROOT_CONVEXIFICATION_STOP.md);
- [outside minimum/Nash-component return cost](CODEX_TARSKI_PREMIUM__GLOBAL_OUTSIDE_MINIMUM_AND_NASH_COMPONENT_RETURN_COST.md);
- [same-potential face minima](CODEX_NOETHER_SUPPORT__SAME_POTENTIAL_FACE_MINIMA_AND_UNPAID_TRANSITIONS.md);
- [contested-singleton block exchange](CODEX_FRECHET_CYCLE__CONTESTED_SINGLETON_BLOCK_EXCHANGE_BOUNDARY.md)
  and [two-sure whole-block swap](CODEX_NOETHER_SUPPORT__TWO_SURE_WHOLE_BLOCK_SWAP_TEST.md).

The last two concern complete behavioral caps and different source data;
they are not cited as proving this exact-root eligibility failure. Their
affine block commutator is not reproposed as a new result. The other notes
already prevent interpreting successor selection, convexification, or a
parameter return as a free actual charged transition. The precise edge
and defect definitions were also inspected in `RobustChargedRelation.lean`
and `Root/NashDefect.lean`.

A genuinely different possible test would work backward through the full
finite-root map, rather than reorder outgoing roots. For a proposed target
w and a nonsure root q (all q_i<1), its ONLY possible predecessor is
v=(w−R(q))/c(q). Its exact Nash conditions are precisely

    Q_i(q)≤w_i,       q_i(w_i−Q_i(q))=0  for every i,
    |(w−R(q))/c(q)|∞≤B.                                 (3)

Indeed w_i=q_iQ_i+(1−q_i)C_i, so domination of both endpoints is
equivalent to the displayed conditions. A test of (3) at globally forced
crossing targets would use the actual full finite-root graph, not the
already investigated small-root singleton matrix alone. However, no
source-produced positive predecessor or invariant family of such targets
has been established here. Finite Nash existence at annotation w does NOT
produce (3), and the zero root is always a solution when w≥s. This is a
possible distinct mathematical question, not a proposed conditional API,
new construction, or a request to launch another search campaign.

This pass stops: the minimum envelope lacks a produced compatibility
comparison; its valid universal replacement is already the capacity
operation. Neither pays or avoids the known global return cost.
