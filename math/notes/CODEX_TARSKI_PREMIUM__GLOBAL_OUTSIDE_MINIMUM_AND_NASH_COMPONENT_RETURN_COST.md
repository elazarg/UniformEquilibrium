# Same-potential outside minimum and the cost of Nash-component continuation

Author: CODEX_TARSKI_PREMIUM.

Status: completed bounded global test, ordinary mathematics not independently
reviewed or Lean-checked. Minimizing the SAME universal potential outside
the strict singleton box gives an ALL-root, one-step crossing source. The
full Nash graph does have a connected component returning toward a global
potential minimum. That component necessarily visits a boundary zero root
and raises the potential of its Bellman SUCCESSORS by a fixed positive
amount. Thus this component continuation does not itself provide another
charged Bellman transition or a renewable word. No UE class or export is
claimed.

## 1. Exact global source, not an isolated crossing

Retain precisely the arbitrary four-player table, M>0, B>M, K=[−B,B]^4,
s_i=r_i({i}), C=∏_i[s_i,B], lower boundary L, root quantities F,Q_i,C_i,a,
and universal robust potential H,δ of
[the reviewed finite-word theorem](../notes/CODEX_TARSKI_PREMIUM__UNIVERSAL_DRIFT_FINITE_WORD_FORCES_MACROSCOPIC_FLOOR_CROSSING.md).
H is C² (a polynomial in the intended certificate). All root Nash tests
are the full four-player finite tests at the displayed annotation; no
attained terminal cap or actual tail payoff is assumed.

Let h=min_L H and define the CLOSED outside region

    A={v∈K : min_i(v_i−s_i)≤0}=K\C⁺,
    C⁺={v∈K : every v_i>s_i}.

A is compact. Choose z minimizing the SAME H on A, and set h_A=H(z).
The lowered SAME-face construction in the reviewed theorem gives a point
of A with H<h, so

    h_A<h,        z∈K\C.                                 (1)

The second assertion follows because A∩C=L. It is not merely a selected
root's predecessor satisfying a local first-order condition.

For EVERY exact root Nash q against z, all Continue is impossible, so a>0.
Its successor w=F(q,z) stays in K and has

    H(w)≤h_A−a<h_A.

Therefore w∉A, or equivalently

    EVERY exact root at z has successor in C⁺.              (2)

Existence of an exact finite root makes this nonvacuous. Thus global
outside minimization strengthens the finite-word source to one step, without
assuming a favorable root or changing the potential.

The reviewed robust pinning and chord proofs apply with this z because
H(z)<h and z is outside C. If κ bounds H's negative directional curvature
as in that theorem, then κ>0 and every such root satisfies

    a>α₀:=2/[κ(M+B)²]>0,
    w_i−s_i>δa for every i,
    Pr_q(at least two quitters)>δa²/(8M).                  (3)

It also has at most one sure quitter. These are inherited full-root facts,
not new estimates of terminal behavioral regret. In particular

    H(w)<h_A−α₀.                                          (4)

## 2. The chosen full-graph continuation

Choose b globally minimizing H on K. The existing exact-root argument
gives b∈C⁺ and only all-Continue roots at b. Briefly, any positive exact
root there contradicts global minimality, so all Continue is Nash and
b≥s. If some b_i=s_i, the exact singleton-face derivative inequality
gives ∇H(b)·(b−r({i}))≥1, while optimality along the segment toward the
reward vertex gives the reverse inequality ≤0. Thus all coordinates are
strict. This uses the SAME H and the full padded box.

Consider the straight annotation path

    v(t)=(1−t)z+t b,       0≤t≤1,
    E={(t,q) : q is exact root Nash against v(t)}.          (5)

This is a parameter path of finite games, NOT a Bellman recurrence.
Every source root at t=0 satisfies (2)–(4); the t=1 root is uniquely zero.
No particular equilibrium at t=0 needs to be anchored.

There is a connected component of E meeting both parameter faces. Here
is the exact finite-game input. Write G_i(t,q)=Q_i−C_i at annotation v(t),
and define the continuous cube self-map

    T_i(t,q)=min(1,max(0,q_i+G_i(t,q))).

Its fixed points are precisely the root Nash conditions: G_i≤0 at q_i=0,
G_i=0 at 0<q_i<1, and G_i≥0 at q_i=1. Browder's parameterized fixed-point
theorem therefore applies to T on [0,1]×[0,1]^4 and gives the stated
component. This uses only the existence of SOME spanning component, not a
continuous section or continuation from every supplied root.

The primary theorem checked is Theorem 1.1 of E. Solan and O. N. Solan,
[Browder's Theorem through Brouwer's Fixed Point Theorem](https://arxiv.org/pdf/2107.02428).
Its parameter and cube match (5) exactly. No equilibrium index or
regularity assumption is added. The following argument uses connectedness
only; it does not infer path connectedness from that paper's theorem.

## 3. Every spanning component must meet one boundary zero root

Let J_z={i:z_i<s_i}, nonempty by (1), and define

    t_* = max_(i∈J_z) (s_i−z_i)/(b_i−z_i).                (6)

All denominators are positive and 0<t_*<1. Put y=v(t_*). Then

    y∈L;
    q=0 is Nash at v(t) exactly for t≥t_*;
    v(t)∈C⁺ for every t>t_*.                              (7)

At every t>t_*, the zero root is locally isolated from nonzero exact roots
in the FULL parameterized graph. Indeed G_i(t,0)=s_i−v_i(t)<0 for every i.
Continuity preserves all four strict signs in a neighborhood. Exact Nash
then forces every q_i=0 throughout that neighborhood.

Let D be ANY connected component of E meeting both parameter faces.
It contains a positive root at t=0 and the zero root at t=1. If it omitted
(t_*,0), its intersection with the zero branch

    Z={(t,0):t_*≤t≤1}

would be a nonempty proper subset of D which is closed (Z is closed) and
also relatively open (by the local isolation just proved). This contradicts
connectedness. Consequently

    (t_*,0)∈D for EVERY spanning component D.              (8)

This is a genuine source-coherent conclusion: whichever spanning component
is supplied, its first parameter face consists of globally screened source
roots, and it contains the SAME boundary attachment y. It is stronger than
merely asserting that a continuation component exists somewhere.

## 4. The same H forces an unpaid rise along that component

On E consider the continuous Bellman-successor observable

    W(t,q)=F(q,v(t)).

Choose any (0,q₀)∈D. By (4), H(W(0,q₀))<h_A−α₀. By (8), the SAME
component contains (t_*,0), where W(t_*,0)=y∈L and H(y)≥h. Hence

    H(W(t_*,0))−H(W(0,q₀)) > h−h_A+α₀ > 0.             (9)

Thus every spanning component's successor observable covers a potential
range of at least this amount. If a continuous root-graph path is separately
chosen connecting its source to that attachment, its successor path must
make this positive rise. No orientation or monotone parameter section is
needed for the range conclusion (9).

The input annotations also have to rise from H(z)=h_A to H(y)≥h. Universal
drift controls H(v(t))−H(W(t,q)) at each individual graph point; it does
NOT price this change of the input annotation along the parameter path.
Equations (8)–(9) show the missing account at the actual globally selected
source, not at an arbitrary solved-profile counterexample.

In particular the spanning component cannot directly be read as a
charged Bellman word through its displayed successors: every such word
would make H nonincreasing, whereas the required boundary attachment has
strictly larger H than the source successor. This does not refute other
joint selections or a compiler which genuinely pays or avoids that rise.

## 5. What this bounded attempt establishes and where it stops

The positive part is (1)–(4): under a universal certificate, one actual
global OUTSIDE minimizer makes every full exact root cross immediately
with robust floor slack and macroscopic collision. The chosen component
construction is also legitimate and anchored strongly enough for (8).
The attempted consumption nevertheless stops at (9). Connectedness supplies
a return to the boundary only by an exogenous potential increase; it does
not supply a second allowed Bellman transition from the crossing successor.

This is not the fixed-source anchoring problem in the existing SPINOZA
component notes. Here no bad initial equilibrium can be blamed: ALL exact
roots at z have the required source fields. Nor is it a claim that a
particular solved table realizes H. The obstruction to this specific
continuation-as-word argument is the compulsory rise under the SAME H.

The minimal missing mechanism is now concrete: replace the parameterized
annotation return by actual root/Bellman transitions or another justified
same-table operation whose account covers the positive amount in (9),
without importing an arbitrary continuation value. Alternatively one must
choose a genuinely different global comparison which never traverses this
zero-root attachment. No such mechanism is proved here, and (9) is not
advertised as a new UE residual reduction.

Narrow prior comparison: §§22–23 of
[SPINOZA's component boundary](../notes/CODEX_SPINOZA__POSITIVE_MINIMUM_RESPONSE_COMPACTIFICATION_BOUNDARY.md)
distinguish a spanning fixed-point component from a prescribed equilibrium
and from chronological composition. The root source here removes the
prescribed-equilibrium ambiguity but gives the additional unavoidable
same-potential rise (9). The frozen crossing theorem and the separate
[existing-table second-transition test](../notes/CODEX_TARSKI_PREMIUM__POST_CROSSING_STALL_IN_EXISTING_TWO_PREMIUM_TABLE.md)
are unchanged. No Lean files, exports, or shared source records were edited.
