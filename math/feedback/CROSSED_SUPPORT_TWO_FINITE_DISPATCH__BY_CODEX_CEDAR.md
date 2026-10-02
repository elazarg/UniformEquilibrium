# Export-gate review of `CROSSED_SUPPORT_TWO_FINITE_DISPATCH`

Reviewer: `CODEX_CEDAR`

## Verdict

**REVISE, then ACCEPT.  Do not demote.**

The mathematical packet is valid and strictly narrows the live support-two
obligation in
[`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md).
I found one inaccurate phrase about punishment attainment and one small
source/adapter presentation omission.  Both have bounded textual repairs; no
theorem or proof must change.

## Required repairs

1. In Exact statement, item 3 currently says that a feasible rate's root and
   “exact punishment continuation” are accepted by the compiler.  The exact
   punishment value need not be attained by one continuation.  The checked
   proof chooses, for every positive `epsilon`, a punishment row whose cap is
   within `epsilon` of `chi_y`.  Replace that phrase by, for example:

   > its exact scalar repair conditions are accepted by the checked
   > unrestricted-behavior compiler, which supplies an accuracy-dependent
   > punishment continuation at every positive tolerance.

   The later Definitions/Probability audit already describes this correctly.

2. In Conjecture-facing change or Adapter, explicitly name/link the question
   above and state that this packet is the accepted partial-answer kind:
   it removes the real-rate quantifier and replaces the unresolved crossed
   chamber by a strictly smaller finite semialgebraic residual.  The current
   prose proves this, but naming the maintained obligation makes gate item 4
   literal.  It is also useful to name
   `quittingGame_uniformPayoff_or_normalizedSingletonSourcePacket` as the
   upstream analytic-waist source if the packet intends to describe the full
   arbitrary-game entrance; otherwise say explicitly that the adapter begins
   at the support-two packet branch.

## Mathematical falsification checks

### Rate and equality faces

The owner condition is exactly

```text
max(O0,O1) <= (1-p)O0+pO1.
```

It forces `p=0` for negative endpoint difference and `p=1` for positive
difference.  On equality faces, Lemma 1 is necessary and sufficient: lower
bounds `u/(u-v)` and upper bounds `-u/(v-u)` have positive denominators, and
their pairwise compatibility is exactly `u_i v_j<=v_i u_j`.  The current
statement correctly handles one equality face with the other orientation's
forced endpoint, and the repaired `alpha=beta=0` case correctly applies
Lemma 1 to both orientations.

### Generic residual and updated screens

For `(a,b)`, the rate-one blocker endpoint is `-beta`; for `(b,a)` it is
`-alpha`.  Exhausting the four strict sign chambers yields exactly the three
implications (8).  There is no missing mixed-sign orientation.

The translation of the checked terminal-gap screen is correct:

```text
r_a(a)<=-g or r_a(c)+g<=r_c(c),
r_b(b)<=-g or r_b(d)+g<=r_d(d).
```

These are singleton preemption comparisons, not coalition toggles, and the
packet keeps them separate.  The nonprojective-principal screen excludes
`{a,b}`, `{a,d}`, and `{b,c}`.  Under the separately stated cardinality-two
hypothesis, the only remaining pairs are exactly `{a,c}`, `{b,d}`, and
`{c,d}`.  The packet does not claim that such a principal exists or has size
two.

### Sure sets and finite toggle cycle

The join-promotion proof is the exact sure-exit characterization.  If the
promoted coalition is not sure, one old member has a strict leave gain or one
remaining outsider has a strict join gain.  Under the terminal witness every
coalition, including the empty coalition, has an outgoing strict membership
toggle.  The 16-vertex coalition cube therefore gives a reachable simple
cycle; bipartiteness makes it even, and a two-cycle would require one payoff
comparison to be strict in both directions.  Hence the displayed possible
lengths `4,6,...,16` are correct.

The packet is careful about the two principal scope hazards: a singleton
preemption comparison changes one singleton coalition to another and is not
a membership toggle, and an arbitrary strict toggle cycle is not a Bellman or
behavioral compiler.

## Probability and unrestricted deviations

The repair root is independent product randomization with a sure blocker, so
the first row absorbs.  The new algebra only checks the three exact scalar
conditions.  Coverage of arbitrary history-dependent randomized unilateral
deviations comes from `quittingCollisionRepairWorks_iff` and its
accuracy-dependent punishment construction, not from an illicit one-shot
deviation argument.  The pure sure-set equivalence likewise has full
behavioral coverage.  No strategy or probability law is assigned to the
residual toggle cycle.

## Boundary and novelty audit

The positive/infeasible affine tests are exact.  In the packet-interface
family, the singleton mixture and target are zero, the punishment floors are
automatic from `chi_i<=max(r_i({i}),0)`, and the selected spectator defect is
identically one in each orientation for every rate.  For `0<g<=1`, both
preemption arms of (11) also hold.  All-Never is an exact equilibrium, so the
example is correctly used only to prove that packet/singleton data do not
determine nonsingleton collision conditions.

The checked sources characterize a **supplied** rate and give the singleton
screens; they do not eliminate the rate, derive the cross-product equality
test, produce the three-defect generic residual, or anchor it to a finite
strict-toggle cycle.  Those are genuine new finite reductions, and the
question explicitly accepts a strictly smaller polynomial/sign residual as
progress.  The downstream consumers are correctly named for the successful
collision and sure-set branches.  The residual itself has, and claims, no
consumer.

## Lean handoff

The proposed handoff is appropriately narrow and does not encode the desired
conclusion as a certificate field.  It should retain the explicit
cardinality-two hypothesis for the principal-pair enumeration, treat the two
equality faces separately, and return only graph/reward data from the final
toggle theorem.  After the two wording/source repairs above, I see no
remaining mathematical, novelty, adapter, consumer, probability, boundary,
or handoff objection to export.

## Bounded recheck after repairs

Both required repairs are now present.  Item 3 accurately states that the
scalar repair conditions feed an accuracy-dependent near-minmax punishment
continuation.  The conjecture-facing section now links the maintained
four-player packet question and identifies the result as its accepted
partial-answer type; Source correspondence names the analytic-waist split and
explicitly scopes this reduction to the support-two packet branch.

**Final verdict: ACCEPT.**  No mathematical, novelty, source, adapter,
consumer, probability, boundary-test, or Lean-handoff objection remains.
