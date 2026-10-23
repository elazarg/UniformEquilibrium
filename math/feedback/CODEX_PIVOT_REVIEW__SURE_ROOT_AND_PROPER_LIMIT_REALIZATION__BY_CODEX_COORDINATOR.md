# Independent review of the incoming-root realization reduction

Reviewer: CODEX_COORDINATOR.

Verdict: PASS for the ordinary mathematical statements in Sections 2–7 of
[the realization note](../notes/CODEX_PIVOT_REVIEW__SURE_ROOT_AND_PROPER_LIMIT_REALIZATION.md),
reviewed at SHA-256
`4ef42382af1ad636333c8cc348c1349e873721d03f60b6e379867aa43f3cdebf`.
This is supporting research, not a Fin4 solution or a new Lean theorem.

## Scalar caps and sure roots

The scalar range argument uses two different topologies correctly.
Finite deadlines are continuous for compact weak convergence, and the
native own-zero hypothesis makes their supremum the complete cap. Lower
semicontinuity on the compact product of opponent-law spaces gives an
attained minimum. The maximum is the largest recipient reward, including
the zero own singleton, and is attained by a pure opponent coalition.
Independent componentwise mixtures connect those two profiles in total
variation. The same uniform coupling bound controls EVERY response, so
it controls the supremum and gives the intermediate scalar cap values.
There is no public correlation or assertion that the cap is weakly
continuous.

With exactly one sure owner k, the entire prefixed pair depends on its
tail only through B_k. Replacing the tail by the scalar-cap realizer
therefore preserves every output coordinate. With two sure owners, no
tail coordinate survives. The resulting prescribed profile absorbs
regardless of whether the substitute tail itself absorbs. This verifies
the unique-sure case that a bare two-sure argument would miss.

At a unique-sure-pivot minimum, replacing its tail cap by the scalar
minimum strictly lowers the output pivot cap unless the old tail cap
was already minimal. Observer caps and all prescribed values are fixed.
The crossing of the pivot's maximum to its Quit branch still gives a
strict decrease, since the original Continue branch exceeds Quit by m.

## Proper limits and infinite incoming words

I inspected
`quittingTerminalSemanticPair_partial_eq_of_proper_lawLimit` and
`quittingTerminalPayoff_update_finiteTime_le_of_lawLimit` in
`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`,
and
`quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`.
Their statements supply exact prescribed values, all nonexceptional
caps, and an upper bound on each finite response of the exceptional
owner. The note correctly adapts the minimum argument to C_p instead
of citing a total-debt-minimum theorem with a different hypothesis.

The unrolling proof also correctly separates payoff and cap convergence.
Vanishing JOINT survival identifies the actual prescribed vector. Every
finite response is bounded by the initial cap through the exact finite
prefix recursion; own-zero late deadlines then bound Never. This yields
only B_actual <= B_target directly. Observer zero debt supplies observer
cap equality, and the GLOBAL C_p minimum supplies pivot equality. I
initially proposed requiring all deleted-owner survivals to vanish;
that stronger condition is unnecessary after this minimum argument.

## The terminal minimum and strict tail-debt rise

At a positive minimum, a nonzero incoming root must have an active
observer. A sole-pivot root contradicts the positive pivot payoff and
global minimum. An active observer has Q_i=B_i(X)>0, while own-zero
rewards bound |Q_i| by M times the total opponent quitting probability.
Hence EVERY nonzero incoming root has activity at least mu/M, where
mu is the least observer cap. Compactness gives one positive activity
threshold over the whole positive minimum fiber.

Starting at any NONREALIZED minimum, nonzero incoming chains in the
minimum fiber have bounded length. Otherwise compactness gives an
infinite chain from that fixed point, with survival at most exp(-n delta),
and the preceding argument would realize it. A maximum-length chain
therefore ends at a minimum with no incoming edge to the same fiber.
That terminal point is nonrealized: realizing it and attaching the finite
prefix would realize the initial point. This argument allows actual and
nonactual minima elsewhere in the fiber to coexist.

All its nonzero incoming factorizations form a nonempty compact set:
automatic activity makes nonzeroness a closed constraint on this fiber.
The sure-root realization theorem excludes sure roots there. The exact
nonnegative debt identity forces each tail to lie in C_p. No tail can
have debt m; compactness makes their excess at least one fixed kappa>0.
The same compactness gives a positive lower bound on c. Consequently
R_p <= m(1-c)-kappa c is a genuine uniformly strict incoming deficit.

This is not yet a contradiction to the outgoing minimum inequality:
the incoming root is observer-Nash at B(Y), while the outgoing bound
uses B(X). No step in the reviewed proof transfers observer optimality
between those two cap annotations. Consuming that difference, or
excluding an actual global minimum, remains open.

No Lean or Lake command was run. The frozen canonical exit export was
not changed or supplemented by a second export.
