# Choosing the proper clock's owner: a bounded selection test

Identity: CODEX_HILBERT. Ordinary mathematics, not Lean-checked or exported.
Status: the fixed-positive-pivot B-envelope all-selector failure has passed
a bounded independent check. Allowing the constrained owner to be chosen
among the four players survives all current fixtures. The explicit rule
below has been tested, but no raw-table bound for an arbitrary hard-residual
table and no all-owner obstruction have been proved.

## 1. Exact question and one actual rule

Take any Fin4 quitting table with own singletons (1,0,0,0), arbitrary other
bounded terminal rewards, and Never zero. For each owner j and 0<δ<1 let
its permitted marginal laws be

    B^j_δ={μ_j: Pr(T_j≥t)≤(1−δ)^t for every t≥0}.

All other players retain unrestricted behavioral strategies. These are four
separate games, not a correlated choice of owner during play. After choosing
one game, its equilibrium is an ordinary product of independent laws.

For each fixed δ use the following actual selection rule:

    choose (j,σ) minimizing Eσ[T_j] over all four
    B^j_δ-restricted equilibrium sets.

Each equilibrium set is nonempty and compact by the finite-head continuity
argument in `CODEX_HILBERT__ONE_PIVOT_FORCED_CLOCK_REGULARIZATION.md`.
The proof is symmetric in the constrained owner: its uniform proper tail
screens all prescribed payoffs, including every follower deviation. Mean
is continuous on each B^j_δ by its uniformly summable geometric tail bound.
A minimum therefore exists over the finite union. This is not an assertion
that its value stays bounded as δ tends to zero, nor minimization of the
missing unrestricted debt itself.

## 2. The fixed-owner counterexample does not refute this rule

The full modified table and its checked fixed-owner result are in
`CODEX_FRECHET_CYCLE__GLOBAL_ENVELOPE_ALL_SELECTOR_COUNTEREXAMPLE.md`.
Its pivot reward is1 when pivot0 quits and2 otherwise. The other rewards
are the old cyclic followers and dummy. My bounded independent PASS is
recorded in the corresponding HILBERT feedback file at the frozen input
hash3074a5b11159a135796193513a0a1080e055cb8bd1bf9ce24bccab76a137d040.

When owner0 is constrained, every restricted equilibrium has its geometric
clock and the two slow stationary followers; its full loss tends to2/7.
But the SAME table has the full pure equilibrium: player1 Quit0, all other
players Never. Its payoff is (2,0,2,1). Player1's payoff against Never
opponents is always0; every nonowner obtains its global reward upper bound.
Thus it lies in B^1_δ for EVERY δ and has constrained-owner mean zero.

Moreover EVERY zero-mean minimizer of the four-domain rule is full Nash.
Indeed it has owner j Quit0 surely. If a finite response t≥1 had value
F_j(t)>F_j(0), the actual B^j_δ law

    [1−(1−δ)^t] Quit0 + (1−δ)^t Quit t

would strictly improve its restricted payoff. Thus every finite response
is capped by F_j(0). All own singleton rewards are nonnegative, so the
limit of finite responses is Never plus the nonnegative singleton times
deleted Never mass; hence their supremum also covers Never. The followers
were unrestricted already. This proves full Nash without choosing one
particular minimizer or assuming continuity of a moving full cap.

This does not add a UE class: it uses an actual full pure equilibrium already
present in the modified table. It does show exactly why changing the owner
is mathematically substantive, not a relabeling of the failed restriction.

## 3. Two further fixture tests and the exact-limit strength

On the original cyclic canonical table, its known period-three exact Nash
profile is feasible for owner0 and has mean3. Hence the four-domain rule
has selected mean at most3 for all sufficiently small δ. On the exact-
example table, the known pivot-only geometric Nash of hazard1/2 is feasible
and has mean1, giving the corresponding uniform upper bound1. RENY's
paired-block completion has a sure-pivot stationary Nash, so the zero-mean
argument of Section2 applies exactly at every δ there as well.

For either uniform-bound fixture, take any sequence δ_n↓0 and its selected
equilibria. Passing to a subsequence fixes the chosen owner j. Bounded mean
gives a proper limiting owner law and uniform tightness of that marginal.
The other marginal laws have a weakly convergent subsequence on ℕ∪{Never}.
Finite-head approximation, screened by the tight owner, proves continuity
of prescribed payoffs and every fixed follower response payoff. Their full
Nash inequalities therefore pass to the limit.

For a fixed finite owner response t, min(t,Geomδ_n) is feasible and differs
in payoff from Quit t by at most2M[1−(1−δ_n)^t], uniformly over the moving
opponents. Letting n tend to infinity gives the limiting comparison for
EVERY finite t. The owner's singleton is nonnegative, including when it is
zero, so finite responses also cover Never. The limit is an ACTUAL full
terminal Nash profile. It supplies the terminal-all-errors consumer directly;
no separate cap-continuity bridge for the sampled equilibria is needed.

This is deliberately a solved-fixture test. Its uniform mean bounds came
from already known exact equilibria. A universal bound of this kind would
produce exact terminal Nash, which is stronger than the question's need for
unrelated approximate profiles at successive errors. No claim that UE implies
uniform mean, or that unrestricted exact Nash nonexistence is known for a
canonical fixture, is made here.

## 4. A raw singleton-owner calculation and its existing scope

One concrete raw-table condition can be stated without selecting an unknown
equilibrium. Choose a nonpivot j, so s_j=0, and a number h∈(0,1]. Let only
j use the geometric hazard h and every other player choose Never. For i≠j,
put A_i=r_i({j}), C_i=r_i({i,j}), and s_i=r_i({i}). Its finite pure response
at t has value

    A_i+[ (1−h)s_i+h C_i−A_i ](1−h)^t.

Never gives A_i. Therefore this profile is full Nash exactly when

    A_i≥(1−h)s_i+h C_i for every i≠j.

The owner itself always gets0 and is indifferent among its complete laws.
If the inequalities hold, the profile belongs to B^j_δ whenever δ≤h.
For the modified fixture, choosing j=1 gives the inequalities2≥1,2≥h,
and1≥0, so every h∈(0,1] works.

This is the elementary one-owner stationary branch, not a new producer.
The named existing stationary single-owner/singleton-base source family,
including `QuittingInducedOwnerChamber` in
`Diagnostics/Quitting/InducedOwnerChambers.lean`, already covers the relevant
supplied exact-root comparisons. The fixed-pivot counterexample's singleton
matrix even has a homogeneous one-column witness. It supplies no adverse
evidence for the actual no-homogeneous-witness residual.

## 5. What remains unresolved

In the canonical class, every full terminal Nash has at least one proper
clock: the late-release inequality d₀≥Π_i Pr(T_i=Never) forces the product
to be zero. This elementary fact does not put that clock in any exponential
envelope or produce a good equilibrium in one of the four restricted games.
Finite owner choice and pointwise convergence of the four restricted caps
also do not control responses escaping with the equilibrium opponents.

The existing proper-watchdog definitions
`IsProperQuittingBehaviorStrategy` and
`IsQuittingProperStrategicallyApproximable` in
`Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`
separate proper approximation from a compact-game semantic producer. They
do not provide an exact-equilibrium selector across these four domains.

Thus the actual unresolved comparison is to derive, from raw hard-residual
reward data, a useful bound for some selected owner and equilibrium, or to
produce an exact counterexample defeating ALL four owner choices. Neither
has been obtained in this bounded pass. The rule succeeds on the three
earlier solved fixtures and the paired-block stationary completion; that is
method validation only, not frontier coverage or a new export target.
