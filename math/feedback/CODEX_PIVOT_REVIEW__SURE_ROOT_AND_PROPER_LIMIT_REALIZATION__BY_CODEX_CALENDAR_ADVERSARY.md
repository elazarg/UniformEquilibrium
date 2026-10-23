# Review of source realization and the terminal minimum reduction

Reviewer: CODEX_CALENDAR_ADVERSARY.

Verdict: PASS for the ordinary mathematical claims in Sections 1--7 of
[the source note](../notes/CODEX_PIVOT_REVIEW__SURE_ROOT_AND_PROPER_LIMIT_REALIZATION.md),
at SHA256
`4ef42382af1ad636333c8cc348c1349e873721d03f60b6e379867aa43f3cdebf`.
This is not a Lean check, an export approval, a proof of universal actual
attainment, or a Fin4 closure.

The reviewer independently proposed the scalar-cap/sure-root mechanism in
Sections 2--3; CODEX_PIVOT_REVIEW then checked it and wrote the self-contained
proof. Thus this file is not a second independent discovery or independent
origin audit of that mechanism. The reviewer separately stress-tested the
proper-limit adaptation, arbitrary-tail unrolling, and compact terminal
selection, including the stronger per-source version now stated in Section 7.
The reviewer also proposed the automatic-activity refinement; the owner
and root coordinator independently checked that argument before insertion.

## 1. Scalar cap and sure-root checks

For own singleton zero, Never is the limit of finite deadline values. A
fixed deadline depends only on finitely many clopen finite atoms of the
opponent laws. Therefore the full scalar cap is lower semicontinuous on
their compact product and attains its minimum. The maximum is attained:
if its maximizing coalition contains the recipient, the recipient quits
with its prescribed opponents at zero; otherwise it chooses Never against
the coalition quitting at zero. The singleton case has value zero. The
componentwise mixtures between minimizing and maximizing opponent laws are
independent private mixtures and are Lipschitz in total variation, uniformly
over all recipient responses. They fill the whole scalar interval.

At a sure root, all prescribed payoffs ignore the continuation. With two
sure owners every cap also ignores it. With exactly one sure owner k,
H_i=0 for i different from k; the only remaining dependency is the scalar
B_k of the continuation. Matching that scalar reproduces the full pair and
the sure root ensures actual absorption. The continuation need not itself
be absorbing, and no maximizing recipient response need be attained.

The unique-sure-pivot refinement also passes. Positive pivot debt makes
its Continue cap branch strictly exceed Quit. Replacing the tail scalar
by its minimum leaves all prescribed payoffs and all observer caps fixed.
Unless the old scalar was already minimal, the pivot cap strictly falls,
even if the maximum switches branches. This contradicts global C_p
minimality. For a sure observer, lowering its continuation cap preserves
its existing sure-Quit cap exactly.

## 2. Proper weak-limit adaptation

The partial realization declaration supplies the exact payoff vector and
every cap except the proper limiting owner's cap. Each fixed finite
deadline for that exceptional owner remains bounded by its target cap;
own singleton zero extends the bound to Never. If the owner is an observer,
zero target debt supplies the reverse inequality. If it is the pivot,
the reconstructed profile absorbs and belongs to C_p, so global C_p
minimality supplies the reverse inequality. No total-debt minimum over the
whole carrier is substituted for the stated hypothesis.

## 3. Arbitrary-tail infinite unrolling

Section 7 correctly allows every later X_t to be an arbitrary point of K.
Only X_0 must be a global C_p minimum. The prescribed payoff tail is bounded
by M times the joint survival, so the literal root sequence absorbs and
has payoff U(X_0).

For precision, write H_i(t) for player i's deleted survival at root t.
The exact cap equations give, at each t,

    B_i(X_t)>=Q_i(q_t),
    B_i(X_t)>=P_i(q_t)+H_i(t) B_i(X_(t+1)).

Iterating these inequalities only up to a fixed deadline bounds that
deadline's exact payoff by B_i(X_0). No limit of products of H_i(t) is
taken. The actual Never payoff is a limit of finite deadline payoffs,
so the actual full cap is at most B_i(X_0). Zero observer debts and the
global pivot minimum then force equality in every coordinate.

This closes the proposed deleted-survival objection in precisely the
stated minimum setting. For a general nonminimum carrier pair the argument
would give only cap domination, and full realization would not follow.

## 4. Compact terminal selection and quantifiers

The automatic-activity refinement correctly applies to EVERY nonzero
incoming root. A sole nonzero pivot root contradicts either positive pivot
payoff (if sure) or global minimality and B_p>m (if nonsure). An active
observer therefore exists. Zero observer output debt forces its root regret
to vanish and its Quit value to equal its positive output cap. Since its
own singleton is zero, this Quit value has absolute value at most M times
the probability that some opponent quits, and hence at most M times the
sum of opponent hazards. This proves the claimed activity lower bound.

The compact fiber M_p must consist entirely of points with positive
observer caps and positive pivot payoff. This gives one strictly positive
activity threshold delta over the whole fiber. Nonzero incoming roots are
therefore exactly the incoming roots satisfying the closed activity bound
at least delta. The resulting relation is compact, including its root labels.
Each infinite chain starting at a nonrealized X_0 has joint survival at
most exp(-n delta), contradicting the preceding unrolling theorem.

Arbitrarily long finite chains starting at that same X_0 would yield an
infinite chain by compactness of the countable product and diagonal
selection. Thus there is a maximum finite length. Its endpoint X_* has
no outgoing edge in this incoming-factorization relation to another
minimum. It remains nonrealized: an actual absorbing realization of that
endpoint, preceded by the finite root word, would realize X_0.

All nonzero factorizations of X_* form a nonempty compact set. None
has a sure root, by Section 3. Therefore every tail lies in C_p. Equality
of its pivot debt with m would give a forbidden relation edge. The
continuous positive difference d_p(Y)-m has a strictly positive minimum
kappa on this compact set. This proves the universal tail-debt gap for
this selected X_*, and the exact debt identity gives the stated incoming
root-regret deficit. The outgoing inequality uses different continuation
caps; the note correctly does not identify them.

Realized and nonrealized minima may coexist elsewhere in M_p. The proof
does not need nonattainment of the minimum value on the entire fiber.

## 5. Source inspection and limits

The following exact source declarations were inspected during the bounded
audit:

- `quittingTerminalPayoff_update_compactStoppingLawProfile_finiteTime_tendsto`
  in `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
- `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
  in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`;
- `quittingTerminalSemanticPair_rootThenContinuation` and
  `continuous_quittingTerminalSemanticPrefix` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingPunishmentValue_eq_stationaryPunishmentValue` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`.

The source note corrected the location of
`exists_twoSureProductRootThenNever_realizing_semantics_of_strictSingletonMargin`
to `UniformEquilibrium/Diagnostics/Quitting/ProductRootLimitCapSandwich.lean`;
the cited zero-singleton product-base file contains its carrier wrappers.
No matching unique-sure-root realization or closed scalar-cap range theorem
was found in the narrow source search. This is not a claim about the entire
repository or literature.

The remaining task is substantive: exclude the produced terminal minimum
by a whole-law operation, or prove that some minimum is actually realized
and then consume that actual source. Neither finite support nor properness
of the pivot follows from the current theorem.
