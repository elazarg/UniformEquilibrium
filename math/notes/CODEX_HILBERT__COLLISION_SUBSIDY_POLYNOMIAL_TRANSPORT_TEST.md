# Collision-subsidy transport of a global polynomial certificate

Owner: CODEX_HILBERT. Ordinary mathematical bounded test, not independently
reviewed or Lean-checked. The exact all-edge transport estimate is proved;
its proposed continuation-to-a-sure-root use adds no global contradiction.
It consumes the fixed tolerance before the elementary target can be forced.
No general homotopy invariance or new equilibrium producer is claimed.

## 1. Why the fixed-period ansatz was stopped

The preceding two-/three-phase root idea had no coverage proof from the
canonical hard singleton data. The active root equalities and passive
collision comparisons are additional constraints, not outputs of those
matrix hypotheses. The arbitrary-active-increment construction in Section 6
of `CODEX_STRENGTHEN__FIN4_CAPACITY_POTENTIAL_STATIC_TOPOLOGY_SEPARATION.md`
shows exactly why a fixed binding-cap endpoint field can vary independently
of the passive singleton matrix. Its Section 7 also distinguishes a Boolean
improvement cycle from a temporal Nash--Bellman cycle.

The exact positive-size test in
`CODEX_HILBERT__POSITIVE_SIZE_COLLISION_CYCLE_GLOBAL_TEST.md` does produce a
charged cycle, but its table has a pure equilibrium. Merely presenting its
linear cycle inequalities as a new source hypothesis would not provide the
missing coverage theorem. That ansatz is stopped, not refined by further
hand-designed rewards.

## 2. A different global deformation question

Fix any canonical four-player table r, with zero Never and own singletons
s=(1,0,0,0). All root choices are independent. For t≥0 define

    r_i^t(S)=r_i(S)+t·1_{i∈S, |S|≥2}.                 (1)

This rewards a player for joining a collision. All singleton vectors,
including every off-diagonal singleton entry, are unchanged. Canonical
punishment normality therefore still holds, but the exact punishment
values and sure-root condition are not asserted to be invariant.

Let ℛ_ε^r(B) be the complete floor-free relation on the fixed box
[−B,B]⁴: ordinary root regret ≤εa and Bellman residual ≤εa in every
coordinate, where a is root absorption. Suppose H has unit charge drift
on all ℛ_δ^r(B) edges. The candidate mechanism was to move (1) to a
table with a direct all-Quit consumer while retaining that global H.

## 3. Exact all-edge transport and its tolerance cost

For one player let α_i be opponents' all-Continue probability, β_i=1−α_i,
and q_i its own Quit probability. At the same root and continuation,

    Q_i^t=Q_i+tβ_i,       C_i^t=C_i,
    F_i^t=F_i+tq_iβ_i.                                 (2)

These identities retain all collision coalitions, not only pairs. Put
Δ_i=Q_i−C_i. Ordinary regret is

    e_i=max{(1−q_i)Δ_i, −q_iΔ_i}.

The right side is Lipschitz as a function of Δ_i with constant
max(q_i,1−q_i)≤1. Therefore

    |e_i^t−e_i|≤tβ_i≤ta,
    |F_i^t−F_i|≤tq_iβ_i≤ta.                           (3)

For every ε≥0, the same actual root and abstract endpoints consequently
give the relation inclusions

    ℛ_ε^{r^t}(B) ⊆ ℛ_(ε+t)^r(B),
    ℛ_ε^r(B) ⊆ ℛ_(ε+t)^{r^t}(B).                     (4)

The box is unchanged; the inclusions do not infer a new reward bound or
new endpoints. In particular, for 0≤t<δ, the original polynomial H is
still a unit-drift certificate on ℛ_(δ−t)^{r^t}(B).

These statements are global over every product root and every pair of
eligible endpoints. They do not require an equilibrium selector, a selected
path component, or extrema of H. They also do not establish preservation
of positive tolerance after an arbitrarily long reward deformation.

## 4. The all-Quit target yields only the old pure-root test

Let I be the grand coalition and set

    t_* = max_i [r_i(I\{i})−r_i(I)]_+.

At t≥t_*, the all-Quit root is Nash: quitting pays r_i(I)+t while
continuing pays r_i(I\{i}). Every player's opponents contain sure
quitters, so continuation values are irrelevant. This is a direct pure
terminal equilibrium, hence also a sure-root consumer. Repeating its root
is a positive-charge self-loop at its reward vector.

However an original global certificate at tolerance δ already forces

    δ<t_*.                                             (5)

Indeed at the original all-Quit root the ordinary regret is at most t_*;
the endpoint v=w=r(I) gives exact Bellman matching and absorption one.
If t_*≤δ, this is already an ℛ_δ^r(B) self-loop, contradicting H's
unit drift. Its reward vector lies in the original reward box.

Thus (4) can preserve positive tolerance only for t<δ<t_*, before the
elementary all-Quit target is reached. The attempted global contradiction
has reduced exactly to the existing full-coalition Nash-regret test, not
to an additional constraint of a positive global minimum.

Subdividing the deformation does not help: applying (4) successively loses
the sum of the increments, still t. Multiplying H preserves its drift but
does not enlarge the edge relation on which it was verified. Selecting new
polynomials with renewed tolerances would require a new substantive
existence theorem; it does not follow from (4). No impossibility theorem
for every more sophisticated deformation is inferred here.

## 5. Source scope and the surviving question

The endpoint and mixed-regret identities used in (2)–(3) are the ordinary
root definitions in `UniformEquilibrium/Quitting/Root/NashDefect.lean` and
the current absorption-weighted packet interfaces. The narrow root and
weighted-packet lookup found no additional theorem transporting an all-edge
polynomial through an arbitrary collision-reward change. The active/passive
independence no-go cited above concerns a fixed local cap; it is not being
misused to deny global polynomial compatibility.

**Outcome:** neither the fixed-period reward design nor this fixed-margin
collision-subsidy homotopy supplies a new global producer. The exact
unproved requirement for continuing the latter is a way to renew a positive
all-edge tolerance using raw game structure before the current margin is
exhausted. Assuming that renewal would beg the question. This deformation
is stopped rather than promoted to a new interface or a conjecture
counterexample.
