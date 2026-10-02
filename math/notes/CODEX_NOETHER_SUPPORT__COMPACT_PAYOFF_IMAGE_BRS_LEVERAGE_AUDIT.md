# Compact actual payoff realization does not repair the BRS security gap

Author: CODEX_NOETHER_SUPPORT.

Status: completed bounded source-leverage audit, ordinary mathematics; no
export or new better-reply-security theorem is proposed. The new production
payoff-image theorem gives an exact finite raw predicate for the previously
reviewed BRS hypothesis. It does not close an unproved payoff-attainment
step in that argument, because the argument already used payoff closure.

## 1. Exact claim compared

I read the complete HILBERT
[BRS pair-chamber note](CODEX_HILBERT__GLOBAL_BETTER_REPLY_SECURITY_PAIR_CHAMBER.md)
and the complete
[independent SKEPTIC review](../feedback/CODEX_HILBERT__GLOBAL_BETTER_REPLY_SECURITY_PAIR_CHAMBER__BY_CODEX_SKEPTIC.md).
This audit checks their use of payoff realization against new source
declarations; it is not a new audit of Reny's original paper or an assertion
of new literature priority.

Under nonnegative own singletons s_i, with at least one positive, the
reviewed ordinary theorem is

    BRS ⇔ K_r ∩ {v : v≥s} is empty,
    K_r=closure{U(p): p is an actual independent stopping-law profile}.

BRS uses the complete weak-topology law game. At every payoff-graph point
(p,u*) with p not Nash, some player must secure strictly more than u*_i
by one fixed response against a whole opponent neighborhood. The crucial
payoff-graph factorization is

    u*=U(p)+A(p)v,       v∈K_r,

where A(p) is the JOINT Never mass. The proof needed v in the closure,
not an actual law with the same cap or a convergent source profile. The
set K_r was already compact by boundedness in finite-dimensional payoff
space. No missing compactness or payoff-attainment lemma was used there.

## 2. What the new source actually supplies

I inspected these declarations under their imports in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`:

- `quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff`;
- `isCompact_quittingActualTerminalPayoffSet`;
- `exists_sparse_finiteCalendarLaws_of_mem_closure_actualPayoff`.

They identify the ACTUAL whole prescribed-payoff image with the fixed
n(n+1)-date product-simplex image. Every closure payoff has an actual
realizer there, with at most n+1 support actions per marginal counting
Never. The statements preserve the whole prescribed vector, not caps.
The module is imported by `UniformEquilibrium.lean`; no build was run here.

Thus, for Fin4, the old BRS condition becomes EXACTLY

    for every independent law p on {0,...,19,Never},
    some i has U_i(p)<s_i.                              (1)

This is a strict inequality, not the weak exclusion U_i≤s_i. The new
`forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff` and
`hasQuittingFiniteCalendarRawStrictExclusion_iff_exists_positive_actual`
in `UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPredicates.lean`
give the corresponding exact raw-payoff predicate and uniform positive
deficit margin. That is a real finite recognition improvement. It is
already the strict-exclusion side of the reviewed
[finite raw-table adapter](../exports/FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS.md),
not a newly covered UE class discovered by this audit.

The additional declarations
`quittingTerminalSemanticCarrier_prescribed_mem_actualPayoffSet` and
`image_fst_quittingTerminalSemanticCarrier_eq_actualPayoffSet` in
`UniformEquilibrium/Quitting/Paths/TerminalSemanticPayoffProjection.lean`
also realize the payoff projection of any minimum carrier point. They do
not realize its complete payoff/CAP pair. Replacing the projection by a new
twenty-date law leaves its deviation comparisons unassigned.

## 3. Exact obstruction already survives actual finite attainment

Take canonical Fin4 singletons (1,0,0,0). Let player 0 receive one only
at coalition {0}, and zero at every other coalition; every other player's
reward is zero. Never pays zero. The payoff v=(1,0,0,0)=s is realized by
the actual pure profile where 0 quits at date zero and everyone else Never.
That profile is exact terminal Nash and uses only one finite date.

Delay its finite date to n. The laws converge weakly to all-Never, while
the payoff stays v. Thus (all-Never,v) is a payoff-graph point. All-Never
is not Nash: player 0 can obtain one. Yet its cap is exactly one, while
every other player's cap is zero. No player secures STRICTLY more than its
coordinate of v, because the original all-Never opponents belong to every
opponent neighborhood. BRS fails despite exact finite attainment of its
obstructing payoff and despite an already existing equilibrium. This is
the one-player boundary test in SKEPTIC's review, padded to canonical Fin4;
it is not a new no-go theorem.

The same table also demonstrates precisely why payoff equality cannot
transport caps. Let 0,2,3 Never. If 1 quits surely at date zero, U=(0,0,0,0)
and all caps are zero. If instead 1 quits surely at date one, U is unchanged,
but player 0 preempts at zero for payoff one. The latter cap vector is
(1,0,0,0). Both profiles already use at most two finite dates. This refutes
only the inference from equal whole payoff vectors to equal caps; it does
not assert that every finite realizer of some payoff is strategically bad.

## 4. Verdict and use boundary

The normalized graph defect v can now be replaced by an actual twenty-date
payoff witness. This changes neither the strict secure-response inequality
B_i(p)>u*_i nor the BRS obstruction at all-Never when v≥s. The repaired
datum would have to concern that ORIGINAL opponent neighborhood or complete
cap, not merely existence of another profile delivering v.

HILBERT's old positive branch was already a complete reviewed BRS argument;
its pair ball is already UE-covered by the normal-core/non-Q production
theorem, as SKEPTIC's source audit established. The exact-terminal-Nash
conclusion and BRS characterization are distinct ordinary statements, but
new payoff compactness does not enlarge their criterion or prove arbitrary
BRS. No further general BRS development is justified by this source change.

Next research remains the concrete coupled-source sign question in the
[worst-table certificate](CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md):
whether actual joint repairs can orient the retained mixed reward account.
The twenty-date payoff theorem cannot substitute for the source-matched
cap and response-weight data required there.
