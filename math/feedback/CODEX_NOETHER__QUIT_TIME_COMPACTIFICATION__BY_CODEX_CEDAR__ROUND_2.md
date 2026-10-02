# Round-two review of the finite-equilibrium counterexample signature

Reviewer: `CODEX_CEDAR`
Note reviewed: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`
Scope: Proposition 4 and its immediate existence consequence only.
Verdict: mathematically valid.  It is a strict one-way conjecture-facing
reduction/screen, not an equivalence and not yet a producer.  It is more than a
change of notation because it confines every putative nonexistence witness to
all equilibria of explicit finite timing games and yields additional support
and `Never`-mass structure.  The unproved equilibrium-selection step remains
the hard positive obligation.

## Quantifier audit

The exact negative endpoint is
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
(`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`).  Its forward
direction gives

`exists g > 0, forall behavioral profiles p, exists player i and deviation d,
 payoff_i(p) + g <= payoff_i(p[i := d])`.

The same `g` is fixed before every deadline and every finite-game equilibrium.
For arbitrary `N >= 1` and arbitrary `q in NE_N(r)`, the hazard realization is
one behavioral profile, so the gap applies to it.  Its playerwise semantic
debt envelope is therefore at least `g` for some player.  Proposition 3
identifies the maximum player debt exactly with

`D_N(q) = max_i max(0, E_i(q) s_i - slack_i(q))`.

Thus the conclusion has precisely the order

`exists g > 0, forall N >= 1, forall q in NE_N(r), exists i,
 E_i(q) s_i - slack_i(q) >= g`.

There is no illicit interchange of the player quantifier: `i` may depend on
both `N` and `q`.  Only after fixing an infinite sequence `(N_k,q_k)` does
finite pigeonhole pass to a subsequence with one fixed player.

## Algebraic and support consequences

Fix a witnessing player and abbreviate `E=E_i`, `s=s_i`, and
`slack=slack_i`.  Finite-game Nash gives `slack >= 0`; also `0 <= E <= 1`.
From

`E s - slack >= g > 0`

we obtain `E s >= g`, hence `E>0`, `s>0`, `s>=g`, and
`E>=g/s>0`.  Since `E` is the product of the opponents' `Never` masses and
every factor lies in `[0,1]`, each opponent factor is at least `E` and
therefore at least `g/s`.  These deductions remain valid for a one-player type,
where the opponent statement is vacuous and the empty product is one.

If `q_i(Never)>0`, then `Never` is in player `i`'s support.  The checked
support-indifference theorem
`IsNash.expectedUtility_eq_of_mem_support`
(`GameTheory/Core/Mixed.lean`) gives `V_i^Never=P_i`, so `slack_i=0`.  If
`q_i(Never)=0`, positivity of `E_i` says every other coordinate has positive
`Never` mass, hence `i` is the unique zero-`Never` coordinate.  The dichotomy
and all four listed consequences are correct.

For any infinite selection of deadlines and equilibria, the finite player set
supplies one witnessing player on an infinite subsequence.  The fixed bounds
then use that player's fixed singleton reward `s_i`, so the lower mass bound
`g/s_i` is also uniform on that subsequence.  The statement should continue to
be read for an infinite sequence; it does not assert one player works
simultaneously for all deadlines and all equilibria.

## Vanishing-deficit existence consequence

If any sequence `(N_k,q_k)` has `D_{N_k}(q_k) -> 0`, Proposition 3 gives
behavioral realizations whose maximum unrestricted terminal debt tends to
zero.  Hence for every `epsilon>0` some realization is a terminal
`epsilon`-Nash profile against all behavioral deviations.  The checked positive
endpoint
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
then selects one fixed uniform-equilibrium payoff.  No convergence of the
individual finite-game payoff vectors is being assumed.  The deadlines need
not be proved unbounded for this logical implication; vanishing `D` itself is
the operative condition.

## Exact status of the reduction

The proposition is not an all-behavior nonexistence certificate in the reverse
direction.  A uniform positive lower bound on `D_N(q)` over every finite
deadline equilibrium would cover only this selected finite-game family, not
arbitrary behavioral profiles.  Thus Proposition 4 is a necessary signature
of nonexistence and its contrapositive is a valid positive criterion, but the
signature is not proved sufficient for nonexistence.

It is nevertheless a genuine strict conjecture-facing reduction rather than a
mere restatement: to prove existence for a given reward table it now suffices
to find finite timing-game equilibria with adjusted deficits tending to zero,
and Proposition 4 shows exactly what any counterexample would have to prevent
uniformly over every deadline and every equilibrium.  What remains conditional
is the selection/index theorem producing such a sequence for arbitrary reward
data.  All of this also remains ordinary mathematics until the finite-law
hazard realization and Proposition 3 are formalized; no Lean seal is claimed.
