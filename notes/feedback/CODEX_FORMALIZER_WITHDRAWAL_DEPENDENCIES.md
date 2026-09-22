# Deadline withdrawal: source and Lean dependencies

The source is `math/exports/WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS.md`,
especially Sections 1.3, 2, and 4. The intended first target is its literal
all-evaluation comparison (D), not the later Fin4 uniform-payoff consumer.

## Already available

`CappedClockPointwiseDomination.lean` supplies literal child/outsider clocks,
quiet embedding, advance-to-deadline clocks, first-coalition case lemmas,
finite N/F/J rows for advancing alone, and evaluated pure-clock gains.
`CappedClockExpectationDomination.lean` supplies bounded integration and
finite weighted-sum interchange. `CappedClockEvaluatedFullBehavioralCap.lean`
transports legal stopping-law replacements to unrestricted behavioral caps.
`CappedClockEvaluatedChildDeletionAdapter.lean` identifies those debts with
the actual deleted-child profile. These are the reusable bridge for (D).

## Source-specific proof obligations

1. Define the finite raw floor l_i^0 as the minimum of zero and rewards at
   every nonempty child coalition excluding i. Define W_i^(l^0)(A) with
   zero for i outside A, the erased-coalition reward difference for a
   nonsingleton member, and l_i^0-s_i for a singleton member. State D-N,
   D-F, and D-J with separate nonnegative arrays a and b.
2. Define the literal deadline-atom withdrawal R_t(x): replace x=t by
   Never, leaving all other clocks unchanged; at Never, it is the identity.
   Prove the three first-outcome cases and the singleton floor estimate.
   The evaluated singleton estimate needs f(Never)=0, f≥0, and antitonicity;
   it is not a consequence of advancing-only capped-clock domination.
3. Prove the deterministic inequality (4.1) for each child clock tuple and
   outsider deadline. In the future case, split the residual into
   `[f(t)-f(τ)]·(D-N residual) + f(τ)·(D-F residual)`; in the tie case use
   D-J and the floor. No row assumes a good strategy or a favorable root.
4. For each i let c_i=max(a_i,b_i). On the disjoint private events T_i>t
   and T_i=t, mix advance with probability a_i/c_i and withdraw with
   probability b_i/c_i; otherwise keep T_i. This is a legal law with an
   independent outsider-clock sample. Prove exact conditional identity
   `c_i·E[gain of mixed replacement | child clocks, deadline]
     = a_i·advance gain + b_i·withdrawal gain`.
   This disjoint-event identity is the source of `max`, not a generic
   convexity bound and not an assumption about a supplied deviation.
5. Integrate the pointwise inequality over independent child and outsider
   laws, identify the mixed child's expectation with a legal unilateral
   replacement, then take the outsider's unrestricted supremum. Finally
   transfer to actual quiet-lift/deleted-child debts. Only then derive the
   displayed max- and sum-debt bounds.

The current capped-clock expectation and cap adapters hard-code the advance
operation. Their reusable bounded-expectation/cap *patterns* do not directly
accept the atom-withdrawal mixed law. That exact mixed-law transport is the
first nontrivial new Lean bridge. A theorem assuming the desired behavioral
debt inequality as input would not prove (D). The optional stationary-security
improvement and Fin4 target preservation are downstream and are not part of
this first wave.
