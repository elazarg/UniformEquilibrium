# Two-active crossings at the same outside minimum: the sure-hazard threshold

Author: CODEX_TARSKI_PREMIUM.

Status: completed bounded ordinary-mathematics comparison, not independently
reviewed or Lean-checked. The one-sure/two-active branch admits an exact
same-annotation hazard reduction. It either produces the actual-punishment
sure-root alternative, or forces a strict, explicitly priced outsider
joining/suppression switch. Under the negative certificate the latter is
necessary. The genuinely mixed nondegenerate pair has no such free hazard
at the same annotation. This does NOT exclude all two-active crossings,
produce an actual terminal equilibrium, or identify a new UE class.

## 1. Source and the operation being tested

Use an arbitrary four-player table with zero Never reward and
|r_i(S)|≤M, own singletons s_i=r_i({i}), and the padded box K=[−B,B]^4,
B>M. The punishment coordinate P_i is the infimum, over independent
opponent behavioral strategies, of player i's complete behavioral cap.
Assume punishment normality P_i≤s_i. No punishment infimum is assumed
attained, and P is not assumed jointly realizable.

Assume the universal robust root potential H,δ and the absence of a
sure-root Nash profile at P from the literal polynomial characterization.
Here a root is the four independent Quit probabilities q; Q_i and C_i
are its immediate Quit and Continue endpoint payoffs; F is its prescribed
root payoff; and a=1−∏(1−q_i). Every player's two endpoints are retained.
The robust drift applies to all eligible roots and annotations in K, not
to arbitrary roots regardless of Nash inequalities.

Take the SAME global outside minimum constructed in
[the global outside-minimum note](../notes/CODEX_TARSKI_PREMIUM__GLOBAL_OUTSIDE_MINIMUM_AND_NASH_COMPONENT_RETURN_COST.md):

    C⁺={v∈K : v_i>s_i for every i},
    A=K\C⁺,
    z∈argmin_A H,                 H(z)<min_L H,

where L is the lower boundary of the closed singleton box. In particular
z is strictly outside the closed singleton box. EVERY exact Nash root at
z exists in the full four-player finite game and satisfies

    a>0,        F_i(q,z)>s_i+δa for every i.              (1)

There are at least two active players and at most one sure player. The
source note proves these statements from the same H; no terminal cap
minimum or multiplier is used here.

The chosen operation varies the probabilities of an exactly two-active
root, keeping both outsiders quiet, the raw table fixed, and the annotation
equal to z. It is not the older two-pinned-face operation: z_i need not
equal s_i, even for an active player.

## 2. Complete two-active equations

Let the active pair be i,j, with x=q_i>0 and y=q_j>0, and let k,l be its
two outsiders. Write

    a_i=r_i({i,j})−s_i,
    J_i=r_i({i,j})−r_i({j}),

and interchange i,j for a_j,J_j. Active optimality and (1) imply

    F_i=Q_i=s_i+y a_i>s_i,
    F_j=Q_j=s_j+x a_j>s_j,
    a_i>0, a_j>0.                                        (2)

The active endpoint differences are exactly

    G_i=(1−y)(s_i−z_i)+y J_i,
    G_j=(1−x)(s_j−z_j)+x J_j.                           (3)

For EACH outsider k (and separately for l), put

    A_k=r_k({i,k})−r_k({i}),
    B_k=r_k({i,j,k})−r_k({i,j}).

Its full root inequality, before specializing to a sure owner, is

    Q_k=(1−x)(1−y)s_k
          +x(1−y)r_k({i,k})+(1−x)y r_k({j,k})
          +xy r_k({i,j,k}),
    C_k=(1−x)(1−y)z_k
          +x(1−y)r_k({i})+(1−x)y r_k({j})
          +xy r_k({i,j}),
    Q_k≤C_k.                                             (4)

The other outsider has the same literal formula with its own rewards.
No pointwise no-join condition on a terminal coalition is substituted for
the averaged condition (4).

## 3. Exact one-sure consumption-or-blocking theorem

Suppose x=1 and 0<y<1. The pair cannot have two sure members under H.
The following conclusions are forced by the negative certificate:

    J_j=0,
    J_i<0,
    z_i<P_i≤s_i.                                         (5)

Put h=s_i−P_i≥0 and C=−J_i>0. There is an outsider k∈{k,l} with

    A_k>0,              B_k<0,
    A_k C > h(−B_k).                                    (6)

More precisely, define

    t_* = max({0} ∪ {A_k/(A_k−B_k) : k outside, A_k>0}),
    t_P = h/(h+C).

Then

    0≤t_P<t_*≤y<1,                                     (7)

the SAME annotation z has an exact root (q_i,q_j,q_k,q_l)=(1,t,0,0)
for EVERY t∈[t_*,y], and a maximizing outsider in the definition of t_*
is indifferent at t_*. Its prescribed root payoff is nevertheless
strictly above its singleton by (1). The sure owner's payoff at that
endpoint satisfies

    t_* a_i>δ.                                          (8)

These are actual finite roots against one annotation, not a parameterized
sequence silently identified with Bellman successors.

### Proof, including the sure-root consumer

Since j mixes and i quits surely, (3) gives J_j=0. Every player's
unilateral endpoints EXCEPT i's are now independent of the continuation
annotation: the unchanged player i quits surely even when that player
deviates. For the sure owner at P the Quit-minus-Continue difference is

    G_i(P;y)=(1−y)(s_i−P_i)+y J_i.                       (9)

If (9) were nonnegative, the SAME root would be exact Nash against the
actual P and would have a sure quitter. This is precisely the forbidden
sure-root alternative; no joint attainment of P is needed. Thus (9)<0.
Normality gives J_i<0. Since G_i(z;y)≥0, subtraction gives z_i<P_i.
This proves (5). It also shows that lowering y improves the sure owner's
root inequality at z: it is affine with positive value s_i−z_i at zero
and negative slope J_i−(s_i−z_i).

For every t∈[0,y], player j remains indifferent, player i remains
optimal, and the complete outsider tests reduce exactly to

    (1−t)A_k+t B_k≤0                                    (10)

for both outsiders. If A_k≤0, both the zero endpoint and the supplied
y endpoint satisfy (10), so the whole interval does. If A_k>0,
feasibility at y<1 forces B_k<0, and (10) holds exactly when
t≥A_k/(A_k−B_k). The whole feasible interval is therefore [t_*,y].
It is nonempty and includes its endpoints, without a limiting selection.

At ANY t in this interval, all the other players' exact tests remain
independent of the annotation. The sure owner's exact test at P is

    h−t(h+C)≥0  iff  t≤t_P.                             (11)

Consequently, if t_*≤t_P, choosing the literal feasible endpoint t_*
produces an exact sure-root Nash profile at P. Under its exclusion we
must have t_*>t_P. In particular t_*>0, so a maximizing outsider has
A_k>0 and B_k<0. Cross multiplication by the positive denominators in
(7) gives precisely (6). At t_* its test (10) is equality.

Finally, each of these roots is exact at the original z and has a=1.
Applying the SAME global source conclusion (1), including at the closed
endpoint t_*, gives every strict floor margin and (8). This is where the
global outside minimum adds information beyond an arbitrary one-sure
finite root. The proof uses the ordinary sure-root alternative separately
from this H-minimality comparison. ∎

## 4. Why the genuinely mixed case is a different remaining operation

If 0<x,y<1 and J_i J_j≠0, (3) determines the two hazards uniquely at
the fixed annotation:

    z_i−s_i = [y/(1−y)] J_i,
    z_j−s_j = [x/(1−x)] J_j.                            (12)

In particular the sign of the active annotation gap equals the sign of
the corresponding membership gap J. This is not the sign of the cross
singleton payoff minus s. The finite root can therefore be a
matching-pennies pair with one active annotation below its singleton and
the other above. There is no same-annotation pair-hazard interval in this
nondegenerate case. Altering either hazard breaks an active equality
before any conclusion about the outsiders is available.

Even when both active annotation gaps are positive, z can remain outside
because an OUTSIDER coordinate is below its singleton. The earlier
two-pinned argument cannot be imported in either case. If one J vanishes,
the corresponding mixed equality instead pins its own annotation to s;
that degenerate family needs its own endpoint analysis and is not covered
by the division in (12).

The existing two-premium HILBERT table illustrates the nondegenerate
matching-pennies branch at the level of exact root equations: J_0=−1,
J_1=2, z=(0,2,3,1), and the entire root set is the crossing pair
(1/2,1/2,0,0). That table has UE and no universal H. It is used only to
check that a claim excluding the branch from (2)–(4) alone would be false;
it is NOT a counterexample to the global source under study. No new
calibration table is constructed here.

## 5. Source comparison, limits of the result, and next question

The source declarations are
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
and exact finite Nash existence in `Quitting/Root/NashExistence.lean`.
The same-H outside minimization is the ordinary result linked in §1;
it is not a Lean-checked global minimum assertion.

The prior
[two-pinned test](../notes/CODEX_TARSKI_PREMIUM__TWO_PINNED_FACE_FINITE_ROOT_EXIT_TEST.md)
uses two zero active annotation gaps and strict negative cross-singletons,
which are absent here. The
[pair-base audit](../notes/CODEX_CEDAR__FIN4_PAIR_BASE_COMPOSITE_SOURCE_AUDIT.md)
instead starts with TWO sure players, solves the outside players, and
tracks terminal semantic caps. Its agency and support pattern differ
from a two-active root with at most one sure player. The easy pure
coalition cases and the literal matching-pennies calibration above are in
[HILBERT's two-premium note](../notes/CODEX_HILBERT__TWO_PREMIUM_CORE_STATIONARY_AND_ROOT_CHOICE_BOUNDARY.md).

The new comparison is deliberately limited: a concrete operation at the
same source either consumes the exact sure-root alternative or exposes
the outsider threshold (6). It does not eliminate that threshold. A
binding outsider at t_* is not automatically an independently selected
three-active root, and the interval t↦q(t) is not a chronological word.

For the full two-active branch, the remaining genuinely new input needed
is therefore not another pair payoff formula: it is a way to recruit a
threshold outsider, or to change the annotation in the rigid mixed case,
while paying that change under the SAME universal H. Neither an isolated
root calculation nor the stopped connected-component return supplies
this. No claim that globality is unnecessary or that this branch refutes
UE is made.
