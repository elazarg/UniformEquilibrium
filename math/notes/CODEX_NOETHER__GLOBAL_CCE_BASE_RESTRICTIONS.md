# Coarse Nash-regret restrictions for every quitting base

Identity: CODEX_NOETHER. Ordinary mathematics, not checked in Lean here.

Status: the arbitrary-base LP and exact-profile/all-horizon theorem below
are valid ordinary mathematics. Their entire UE existence class is subsumed
by the concrete persistent-base source, which also supplies a stronger
necessary condition on counterexamples. The canonical complete proof and
exact source inclusion are in
`notes/CODEX_NOETHER__COARSE_REGRET_BASE_UNIFORM_EQUILIBRIUM.md`.
This is internal supporting mathematics, not additional UE coverage.

## Finite question and raw quantities

Let I be a nonempty finite player set. At every live date, players independently
choose Continue or Quit using private randomization and the public past.
The first nonempty coalition S absorbs at an arbitrary finite real reward
vector r(S), received on subsequent dates. The live/initial stage and joint
Never pay0. Every unilateral replacement is an unrestricted behavioral
strategy. Set s_i=r_i({i}). No own-sign restriction is imposed.

For EVERY nonempty base E⊆I put J=I∖E. Define the finite binary free game

    u_j^E(T)=r_j(E∪T),          j∈J, T⊆J.

For free j and pure action b define

    R_{j,b}^E(T)=u_j^E(T)−u_j^E(T^{j,b}).

Let C_E be the compact nonempty polytope of laws ν on T⊆J obeying

    ν≥0, Σν=1,       EνR_{j,b}^E≥0 for every j,b.

Nonemptiness follows from an INTERNALLY chosen product mixed Nash point of
the finite free game. Correlated laws are only a convex outer relaxation;
no correlated law is played in the original game. This also works for J=∅,
when C_E consists of the single empty-coalition law.

For i∈E define base-member gaps

    G_i^E(T)=r_i(E∪T)−r_i((E−i)∪T),       if |E|≥2,

and, for E={i}, use

    G_i^{i}(∅)=min(s_i,0),
    G_i^{i}(T)=r_i(T+i)−r_i(T)             for T≠∅.

All rewards in the first formula concern nonempty coalitions. The exceptional
singleton empty row is essential: replacing it by s_i wrongly omits profitable
delayed Quit when s_i>0; replacing it by0 wrongly omits Never when s_i<0.

These are finite reward-defined LP values:

    v_{E,i}=min_{ν∈C_E}EνG_i^E,
    v_E=min_{i∈E}v_{E,i}.                                (B1)

No strategy, continuation value or equilibrium is supplied. Separate raw
dual sufficient tests can certify each member with nonnegative coefficients:

    G_i^E(T)≥β_i+Σ_{j,b}λ_{i,j,b}R_{j,b}^E(T),
    λ≥0, β_i≥0                         for every T⊆J.   (B2)

Then v_E≥0. No LP duality converse is needed for any assertion here.

## Producer and actual original-game strategy

Theorem: if v_E≥0 for ANY nonempty E, the original game has an exact terminal
Nash profile and one fixed uniform-equilibrium target, witnessed by that same
profile at every accuracy. The profile is exact Nash at every positive finite
horizon under the zero-initial-stage convention.

Select one product mixed Nash point μ of the free game internally. Its law p
belongs to C_E, so E_pG_i^E≥0 for every base member. At date0 all E Quit
surely and free players use independent μ. Every player Continues forever
after date0, including on off-path histories created by a unilateral replacement.
The actual terminal target is

    V=E_p r(E∪T).

Suppose first |E|≥2. Against ANY single replacement there remains at least
one sure base opponent. Absorption therefore occurs at date0, irrespective
of the deviator's entire later policy. A free player's two date0 endpoints
are exactly its finite binary-game endpoints, controlled by μ's Nash
inequality. A base member's Quit-minus-Continue endpoint is exactly
E_pG_i^E≥0. Simultaneous actions are independent and unobserved at the
choice date; any behavioral replacement's first draw is just a mixture of
those endpoints. Thus the profile is exact terminal Nash.

For E={i}, the already proved one-shot anchor argument applies. If the free
coalition is nonempty, absorption at date0 determines the reward whether the
anchor Quits or Continues. If it is empty, the free players Never thereafter,
so the anchor's full continuation cap is max(s_i,0). The expected Quit-minus-
continuation-cap is exactly E_pG_i^E≥0. This includes arbitrary randomized
late stopping and Never and permits negative own levels.

For N≥1, date0 absorption delivers h_Nr, where h_N=(N−1)/N. For |E|≥2
this is the exact payoff law under every deviation, so scaling the endpoint
inequalities proves exact N-horizon Nash. For |E|=1, the exceptional empty-
event future cap is at most h_Nmax(s_i,0); the same inequalities suffice.
Under the prescribed profile immediate absorption always occurs, hence its
payoff is h_NV and its error to the single fixed target is≤M/N, with
M=max_{S,i}|r_i(S)|. N=1 has zero payoff for everyone. No deleted-clock
contraction, profile limit, target selected after accuracy or public randomization
has been used.

If |E|≥2, stationary repetition of the displayed first row is ALSO exact:
against each unilateral replacement there is still a sure opponent at date0,
so its later repetition is unreachable. This extra assertion is false in
general for |E|=1 and is not carried over to the singleton case.

## Restriction on every counterexample

Every no-UE table, and every table with a positive unrestricted terminal
exploitability floor, must satisfy

    FOR EVERY ∅≠E⊆I, SOME i∈E has v_{E,i}<0.             (B3)

Equivalently, at every proposed base there is some member and some feasible
coarse Nash-regret law with strictly negative expected base-member gap.
This is a genuinely unavoidable finite LP restriction, not a statement that
its negative laws themselves can be played or are product Nash laws. It
does not assert sufficiency of (B3) for nonexistence.

Pointwise complement-leave-safe bases of cardinality≥2 automatically have
all G_i^E(T)≥0 and are included. Singleton pointwise join-monotone anchors
with nonnegative own level are included too. Whether the averaged base tests
add a further class beyond the reviewed singleton LP and existing raw
persistent-base producers is the new coverage question, not an assumption.

## Bounded source correspondence

`quittingPersistentBaseUtility`, `quittingPersistentBaseNashSet` and
`quittingPersistentBaseNashSet_nonempty` in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean` were inspected.
The nonemptiness theorem has no cardinality≥2, own-sign or leave-safe premise;
it is literally the finite mixed Nash theorem under its imports.

`QuittingPersistentBaseComplementLeaveSafe` and
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`
were inspected. That producer assumes cardinality≥2 and pointwise leaving
safety on EVERY completion. It does not internally deduce that pointwise
predicate from the averaged LP minima in(B1).

`quittingOneDateThenNeverProfile_exactHorizonNash` and
`quittingOneDateThenNeverProfile_sameProfile_uniformPayoffWitness` in
`UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean` were inspected.
They consume an already proved exact terminal Nash profile; the raw LP
argument supplies that strategic premise. The implementation handoff should
compose these actual consumers, not manufacture a new finite-game Nash result.

Concrete next question: can a two-member base with a free matching-pennies
game have nonnegative averaged member gaps while EVERY singleton LP is
negative and EVERY pointwise complement-leave-safe base fails? The free
matching-pennies game has a unique uniform coarse Nash law, so its member
averages can be controlled exactly even with negative pointwise rows. First
settle this structural inclusion/separation question; only then compare a
complete table against actual producers. A supplied-base-equilibrium interface
or another overlap fixture is not an export endpoint.
