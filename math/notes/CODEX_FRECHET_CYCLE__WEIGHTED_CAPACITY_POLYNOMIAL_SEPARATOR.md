# Weighted forward capacity has a polynomial all-edge separator

Author: `CODEX_FRECHET_CYCLE`.

Status: complete ordinary-mathematics proof draft, awaiting independent
review. The result supplies a global polynomial certificate when an entire
absorption-weighted forward relation has bounded free-start capacity. It
does not construct a positive-gap reward table or prove universal packet
existence. No Lean implementation, export, or coefficient search is included.

The new step is one-sided smoothing with error proportional to absorption,
followed by C¹ rather than C⁰ polynomial approximation. No invariant
measure, selected recurrent component, attained strategic minimum, or
minimum-absorption cutoff is assumed.

## 1. Exact finite data and relation

There are four players, independent Quit/Continue choices at each date,
bounded nonempty-coalition rewards r(S)∈ℝ⁴, and zero all-Never payoff.
All strategic punishment and equilibrium statements below use unrestricted
behavioral stopping laws, including Never and arbitrarily late finite dates.

Fix M>0 with |r_i(S)|≤M. Let P_i be the infimum of player i's full
best-response cap over independent opponent laws. In particular |P_i|≤M.
The main analytic theorem only uses these four bounded constants; it does
not require punishment normality or attainment of any punishment infimum.

Write q∈[0,1]⁴ for a product root's Quit probabilities, and set

    c(q)=∏_i(1−q_i),     a(q)=1−c(q),
    α_i(q)=∏_(j≠i)(1−q_j).

For a continuation annotation v∈ℝ⁴, use the exact ordinary root quantities

    F(q,v)=R(q)+c(q)v,
    Q_i(q)=the pure-Quit endpoint,
    C_i(q,v)=A_i(q)+α_i(q)v_i,
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

Here R is the unconditional nonempty-coalition contribution, so
|R_i(q)|≤M a(q). These are product-root polynomials except for the
displayed maximum. The coordinate e_i is ordinary mixed-root regret,
not a support error and not a full-behavior cap at a supplied tail.

For B≥M and δ>0 define the compact convex payoff domain

    K_δ(B)={v∈[−B,B]⁴ : v_i≥P_i−δ for every i}.

The relation W_δ(B) consists of ALL triples (v,q,w) such that

    v,w∈K_δ(B),
    |w−F(q,v)|∞≤δ a(q),
    e_i(q,v)≤δ a(q) for every i.                         (W)

The direction is FORWARD: the annotation v is the continuation input,
and w is its approximate Bellman successor. The edge charge is a(q).
Every product root satisfying these inequalities is included. No selected
branch, support schedule, or reachability restriction is imposed.

A finite path has any length H≥0, any initial state in K_δ(B), and
successive edges in (W). Its charge is Σ_(t<H) a(q_t). Length zero is
always permitted at every state and has charge zero. Define

    Cap_δ(B)=sup{charge of every such finite FREE-START path}.

Paths are precisely the finite data of absorption-weighted forward packets
with tolerance δ and the indicated box; a finite list may be extended
arbitrarily after its horizon to meet the production structure's sequence
types. Nothing after the horizon is constrained or charged.

## 2. Main analytic theorem

**Theorem.** Fix B≥M and 0<ε≤1. If

    Cap_ε(B+1)<∞,

then there is a polynomial H:ℝ⁴→ℝ, with rational coefficients if desired,
such that EVERY edge (v,q,w)∈W_(ε/4)(B) satisfies

    H(v)−H(w)≥a(q).                                    (POLY)

Conversely, any polynomial, or any bounded function on K_δ(B), satisfying
(POLY) on all W_δ(B) edges bounds their complete free-start path charge by
its oscillation on that domain.

The tolerance loss and outer-box enlargement are part of the theorem.
No claim is made that bounded EXACT-Nash capacity alone yields a continuous
or polynomial separator for the same exact relation.

### 2.1 Common upward translation is absorption-relative

Let h∈ℝ⁴ have nonnegative coordinates and |h|∞≤t. Translating both
annotations while keeping q fixed gives

    F(q,v+h)=F(q,v)+c h,
    (w+h)−F(q,v+h)=(w−F(q,v))+a h.                     (T1)

The two endpoint gains change exactly as follows:

    Q_i−F_i(q,v+h) = Q_i−F_i(q,v)−c h_i,
    C_i(q,v+h)−F_i(q,v+h)
      =C_i(q,v)−F_i(q,v)+(α_i−c)h_i.                  (T2)

Since α_i−c=q_iα_i≤a, the first gain can only decrease and the second
increases by at most a t. Taking their maximum proves

    e_i(q,v+h)≤e_i(q,v)+a t.                            (T3)

In particular every W_(ε/4)(B) edge translates, for every
h∈[0,ε/4]⁴, into an edge in W_ε(B+1). Its residual and regret are
actually at most (ε/2)a. Both translated endpoints have coordinates
at least P_i−ε/4≥P_i−ε, and lie between −B and B+ε/4, hence inside
the outer box. This is a statement about the ENTIRE inner relation.

The sign h≥0 is essential. An all-Continue root has zero charge and is
exact Nash at v≥s, where s is the own-singleton vector. A downward shift
that makes one coordinate less than its singleton creates strictly positive
Quit regret while the charge remains zero. No arbitrary signed-translation
estimate of the form (T3) holds.

### 2.2 The outer capacity-to-go is bounded and Borel

Put K=K_ε(B+1). At each x∈K, let Φ_n(x) be the maximum charge over
outer paths of length at most n starting at x. This maximum exists.
Indeed, for each fixed length l≤n the path constraints form a closed
subset of a finite product of K and [0,1]⁴. Taking the finite disjoint
union of these compact path spaces handles all l≤n. The length-zero
member ensures the source fiber is nonempty even if x has no outgoing
root satisfying (W). Charge is continuous on each member.

For completeness, Φ_n is upper semicontinuous on K. If x_m→x, pass
to a subsequence realizing the limsup of Φ_n(x_m), choose maximizing
paths, and pass again so their lengths agree. Compactness gives a limit
path with initial state x. Closedness preserves every edge and continuity
preserves its charge, so limsup Φ_n(x_m)≤Φ_n(x).

Thus the complete capacity-to-go

    Φ(x)=sup_n Φ_n(x)

is Borel measurable. It satisfies 0≤Φ≤C for any finite bound C on all
outer free-start charges. For every outer edge (x,q,y), concatenating it
with every finite path from y gives

    Φ(x)≥a(q)+Φ(y).                                     (CAP)

The concatenation remains in the same domain and relation. No maximal
infinite path or maximizing all-length continuation is selected. The
supremum defining Φ need not be attained or semicontinuous.

### 2.3 One-sided smoothing preserves every charged inequality

Choose a nonnegative smooth compactly supported probability density ρ
whose support is contained in (0,ε/4)⁴. Extend Φ by zero outside K,
calling the resulting bounded Borel function Φ̃, and set

    V(v)=∫_(ℝ⁴) ρ(h) Φ̃(v+h) dh.

The extended function is bounded and compactly supported. Differentiating
the smooth kernel in this convolution shows V is smooth on ℝ⁴.

This extension is not being used to invent new admissible states. In fact
there is a neighborhood of the entire inner domain on which every point
sampled by the integral lies in K. If dist∞(x,K_(ε/4)(B))<ε/16 and
h∈supp ρ, then

    x_i+h_i > P_i−5ε/16 ≥ P_i−ε,
    −B−ε/16 < x_i+h_i < B+5ε/16.

Since ε≤1 these inequalities place x+h in the outer box and above
its floor. Thus smoothing uses the actual outer capacity throughout a
neighborhood of the inner domain, including all its boundary faces.

For a fixed inner edge, (T1)–(T3) make every translated edge admissible
in the outer relation. Apply (CAP) pointwise in h and integrate:

    V(v)−V(w)≥∫ρ(h)a(q)dh=a(q).                        (SMOOTH)

All roots, all endpoints and arbitrarily small positive absorption are
covered by this one V. No discretization of the edge set has occurred.

### 2.4 C¹ polynomial approximation keeps the charge scale

Set L=M+B+ε/4>0. Every inner edge has

    |w−v|∞
      ≤|R(q)−a(q)v|∞+|w−F(q,v)|∞
      ≤L a(q).                                         (MOVE)

Choose a polynomial p whose gradient approximates that of V on the whole
box [−B,B]⁴ with

    sup_x Σ_i |∂_i p(x)−∂_i V(x)|≤1/(2L).              (C1)

Such a polynomial exists by elementary tensor Bernstein approximation.
One justification, including derivatives, is as follows. Rescale the box
to [0,1]⁴ and apply the tensor Bernstein operator to the smooth function.
The i-th derivative is the weighted average, with binomial nonnegative
weights, of n[f((k+e_i)/n)−f(k/n)]. Each finite difference is the average
of ∂_i f along that grid segment. Uniform continuity of ∂_i f and the
uniformly vanishing binomial variance show these averages converge
uniformly to ∂_i f. This works for all four derivatives simultaneously.
Rescaling back proves (C1). Initially approximate more accurately than
required; a sufficiently small rational perturbation of the finitely many
polynomial coefficients then preserves (C1), because coefficient-to-C¹
norm is continuous on this fixed box. Thus p can have rational coefficients.

The line segment between v and w stays in the box. The fundamental theorem
of calculus, (C1), and (MOVE) give

    |(p−V)(v)−(p−V)(w)|≤|v−w|∞/(2L)≤a(q)/2.

Together with (SMOOTH), this yields p(v)−p(w)≥a(q)/2. Taking H=2p
proves (POLY), with rational coefficients when p has them. If a(q)=0,
the residual condition forces w=v, and all these inequalities still hold.

This is why uniform C⁰ approximation would be insufficient: its two-endpoint
error would be independent of a(q), which can be arbitrarily small.
The C¹ error is instead multiplied by the actual edge displacement.

### 2.5 Converse

Sum (POLY) on a finite path. The right side is its complete charge and
the left side telescopes to H(v₀)−H(v_H). Compactness bounds this by
max_(K_δ(B)) H−min_(K_δ(B)) H. This includes all starting values and
all path lengths, not just a finite graph's selected components. QED.

## 3. A fixed-box negative certificate under the reviewed UE architecture

This section separately uses the reviewed necessity adapters; it is not
part of the analytic theorem's assumptions. Suppose additionally

    P_i≤s_i for every i,       s_j>0 for some j.          (NORMAL)

Let C_sure denote the finite certificate

    ∃k,q : q_k=1 and q is an exact product Nash root against P.

Its successor payoff is automatically at least P. It does not assume
simultaneous realization of the four punishment coordinates by one tail.

The reviewed S.2 characterization gives C_sure⇔literal S.2 and
C_sure⇒UE. The reviewed other two adapters give the more precise common
box implication

    UE and not C_sure  ⇒  WP(M+2).                      (BOX)

Here WP(B) means weighted packets in [−B,B]⁴ for EVERY positive tolerance
and EVERY requested finite charge, with all their own prescribed floors.
To verify the box quantifier, the checked AKRS forward disjunction leaves
S.1 or S.3 when S.2 is excluded. S.1 produces weighted packets directly
in [−M−2,M+2]⁴: its stationary e-Nash witnesses with e≤1 use annotations
U+2e·1. S.3 produces exact support packets in [−M,M]⁴. Translate those
by 2η·1, where 0<η≤1 and 3η is below the requested weighted tolerance;
the checked translation produces weighted packets in [−M−2,M+2]⁴.
Thus the same box works before either accuracy or charge is chosen.

Consequently, with B=M+2, the following is an ordinary-mathematics
certificate characterization:

    no UE
      iff
    not C_sure and there exist δ∈(0,1/4] and a polynomial H
    satisfying (POLY) on EVERY edge of W_δ(M+2).         (NEG)

The δ and polynomial coefficients may be chosen rational.

Proof of necessity: the checked weighted-packet consumer gives
WP(B+1)⇒UE. If there is no UE, its contrapositive supplies one tolerance
t>0 and one finite charge threshold that no packet in that outer box
reaches. Hence the entire W_t(B+1) relation has bounded free-start
capacity. Choose rational 0<ε≤min(1,t). Its smaller relation is also
bounded, including its stronger floor constraint. The analytic theorem
gives δ=ε/4 and H on W_δ(B). Also C_sure is absent since it implies UE.

Proof of sufficiency: if UE held while C_sure were absent, (BOX) would
give packets in this very box and at this very δ of arbitrarily large
charge. Telescoping H bounds all of them by one finite oscillation,
contradiction. QED.

The exclusion of C_sure and the radius M+2 cannot be silently dropped.
A separator on an arbitrary smaller box only bounds that box's packets.
The current reviewed architecture is a UNION with C_sure; it does not
identify every supplied S.2 root with a repeatable forward cycle.

This is a finite polynomial condition RELATIVE TO THE EXACT SEMANTIC P.
It does not compute P from the reward table, assert its infimum is attained,
give a degree bound for H, or supply an effective terminating search.
No feasible certificate on an actual unsolved table is exhibited here.
If one were exhibited together with not C_sure, (NEG) would prove no UE;
the terminal all-errors equivalence would then imply existence of a
positive unrestricted full-behavior gap. This note gives no numerical gap
formula from the coefficients of H.

## 4. Exact canonical H stress test

The test table, with active indices 0,1,2 cyclically ordered, is

    r₀(S)=1+1_(2∈S) if 0∈S, and 3·1_(2∈S) otherwise;
    r_i(S)=1_(i−1∈S) if i∈S,
           3·1_(i−1∈S)−1 otherwise, for i=1,2;
    r₃(S)=0 if 3∈S, and 1 otherwise.

It has M=3 and s=(1,0,0,0). All-Never opponents prove P≤s. The already
known three-phase exact witness has payoff annotations

    u⁰=(1,1,0,1), u¹=(1,0,1,1), u²=(2,0,0,1).

Let qⁱ give only active owner i probability 1/2 to Quit. The exact FORWARD
cycle is

    u¹ --q⁰--> u⁰ --q²--> u² --q¹--> u¹.

Each edge has absorption 1/2 and exact Bellman matching. At each root
the owner is indifferent; the next active player's Continue endpoint beats
Quit by 1/2, the other active nonowner is indifferent, and player 3
strictly prefers Continue. These are exact Nash roots. Every annotation
is at least s, hence at least P, and belongs to [−3,3]⁴.

Thus for ANY δ>0 and B≥3 these three edges are in W_δ(B). Summing
(POLY) would give 0≥3/2. No polynomial, smooth function, or other
single-valued function can satisfy the proposed certificate on this table.
This tests the orientation, free-start scope and positive charge of the
certificate. It does not rediscover this table's equilibrium or use its
known cycle as a producer for arbitrary data.

## 5. Source ledger, overlap, and exact stopping point

The narrow TOOLKIT route was the absorption-weighted forward packet and
canonical bounded-capacity interface. I inspected these current production
definitions/declarations under their imports:

- `QuittingAbsorptionWeightedForwardPacket` in
  `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacket.lean`;
- `HasAbsorptionWeightedFiniteForwardPackets` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
  in `Projective/AbsorptionWeightedForwardPacketProducer.lean`;
- `coordinateNashDefect_upwardTranslate_le_absorption`,
  `quittingPayoffUpwardTranslate_sub_successor_eq`, and
  `exists_exactFiniteForwardPacketBox_iff_exists_absorptionWeightedBox`
  in `Projective/AbsorptionWeightedForwardPacketTranslation.lean`;
- `quittingRootCoordinateNashDefect` and
  `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` in
  `Root/NashDefect.lean`;
- `quittingRootQuitPayoff_continuation_invariant` and
  `quittingRootContinuePayoff_update_add` in `Root/TerminalDebtPrefix.lean`.

The newly committed declarations were read; I did not run a fresh build.
The ordinary necessity dependencies are
`CODEX_HILBERT__NORMAL_EQUILIBRIUM_TO_FORWARD_PACKET_PARTIAL_CONVERSE.md`
at SHA `b9c9096f87bdd676f2cc94190a16ef35e2dcdbec6b6534c0d4f7c8303f573bda`
and `CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT.md` at SHA
`2f4675b83684dbc1525b90c86c2de97c6bd0c60b78eb4d3da066ca45884d02ea`.
Their independent review is
`feedback/CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT__BY_CODEX_FRECHET_CYCLE.md`.
The S.2 dependency has its separately recorded HILBERT correspondence check;
this author's original S.2 proof is not being treated as self-reviewed.

Existing exact-capacity and ergodic no-gos were read before this proposal:

- `CODEX_CEDAR__ERGODIC_NASH_BELLMAN_RECURRENCE.md` already reduces a
  supplied positive-charge invariant law to the existing consumer and
  supplies the bounded-capacity alternative, not a positive producer;
- `CODEX_SPINOZA__CANONICAL_CAPACITY_FINITE_HORIZON_USC_AND_DELAYED_ESCAPE.md`
  proves finite-horizon USC but explicitly denies automatic USC of the
  all-horizon exact capacity without uniform exhaustion;
- `CODEX_STRENGTHEN__FIN4_CAPACITY_POTENTIAL_STATIC_TOPOLOGY_SEPARATION.md`
  retains the general bounded capacity potential and identifies the missing
  chronological/topological coupling.

Those facts are used honestly: Φ here may still be discontinuous and is
never asserted to be polynomial. A different smooth function inherits its
inequality only after shrinking the allowed tolerance and payoff box.
The one-sided translation and the absorption-relative C¹ step are the new
mechanism. A narrow phrase search for smooth/polynomial capacity, mollified
capacity, one-sided translation, C¹ capacity and Bernstein approximation
found no existing statement of this robust converse.

No floor-removal or finite-burn-in lemma is used. Floors enter only the
explicit nested domains and improve under upward translation. The same
analytic argument also works for the floor-free relations if one separately
wants that statement; no unchecked floor-free UE adapter is inferred.

Proved checkpoint: the all-edge polynomial separator theorem and its
conditional fixed-box completeness (NEG) using the reviewed architecture.
Unproved: either universal nonexistence of these certificates when C_sure
is absent, or one feasible certificate from a genuinely positive-gap table.
No search across polynomial degrees or reward parameters is started here.
Requested next check: independently falsify the smoothing/domain argument,
the charge-preserving C¹ approximation, and the fixed M+2 necessity bridge.
