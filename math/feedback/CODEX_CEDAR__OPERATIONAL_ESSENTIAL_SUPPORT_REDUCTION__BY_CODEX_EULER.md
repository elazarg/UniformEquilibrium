# Independent review of operational essential support reduction

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Object reviewed:**
`notes/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md`  
**Verdict:** **REVISE, then PASS.**  Propositions 1--3 as stated are valid,
but the claim that the `eta` loss in Proposition 2 is essential is false.
There is an exact finite-time witness with the full weak gain `gamma`, using
the checked stopping-law expectation identity rather than epsilon-extremality.
Consequently Proposition 3 also admits `gamma`, not merely `gamma/2`, in its
finite-time conclusion.  The sharp deletion passport described below is valid
ordinary mathematics but should remain an internal strengthening for now, not
a separate export packet.

## 1. Claim restatement

The note fixes a finite quitting table with
`HasTerminalExploitabilityGap r gamma`, deletes a block `B`, takes a terminal
`epsilon`-Nash profile `sigma` of the survivor table with `epsilon<gamma`, and
lifts it by prescribing literal Never to every deleted player.  It claims:

1. the ambient gap witness at the lift is a player `d in B`;
2. after an arbitrary loss `eta>0`, the witness can be taken to Quit at one
   finite deterministic time;
3. cardinal minimality produces such a survivor profile and outsider witness
   for every nonempty proper deletion block.

I checked the lift direction, arbitrary behavioral deviations, exact
stopping-law semantics, the `none` endpoint, the block cardinalities, and the
relationship to the checked quantitative deletion split.

## 2. Proposition 1: PASS

Apply the ambient gap to `Lift_B(sigma)`.  If the selected player survived the
deletion, then

```text
quittingTerminalPayoff_liftDeletedProfile
quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
```

transport respectively its prescribed payoff and the payoff of its arbitrary
ambient behavioral deviation to the survivor game.  The transported gain is
still at least `gamma`, contradicting the survivor `epsilon`-Nash inequality
because `epsilon<gamma`.  Therefore the selected player lies in `B`.

The direction in the note is correct.  Off-path actions cause no gap: the
checked deletion deviation reads the ambient strategy's hazard on the unique
live history, which is all terminal payoff uses.  The best-reply debt statement
then follows from the selected actual deviation.

### Existing-result boundary

The note is right not to advertise Proposition 1 as a new deletion theorem.
The checked split

```text
exists_mem_gap_le_blockDeletionExcessBound_or_survivorGap
exists_mem_gap_le_blockDeletionExcessBound
```

in
`UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`
already kills the survivor arm and selects a deleted owner once a row
absorption bound is supplied.  Moreover a vacuous uniform bound `A=1` is
always available, so the absorption field is not an existence obstacle here.
What Proposition 1 preserves beyond the checked finite inequality is the
literal ambient deviation supplied by `HasTerminalExploitabilityGap`, rather
than only the owner's table-valued excess certificate.  This is useful
provenance, but it is adapter-level packaging.

## 3. Proposition 2: stated theorem PASS, “loss essential” FAIL

The proof printed in the note is valid: applying
`exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub` with `eta>0`
gives gain at least `gamma-eta`, and `quitTime=none` is impossible because
`Function.update_liftDeletedProfile_never` makes that update the original
profile while `eta<gamma`.

The next sentence, however, is too strong:

> “The loss `eta` is essential for this argument.”

It is essential only if one insists on using the epsilon-extremality theorem
as the sole input.  It is not essential for the quitting-game statement.

### Exact full-gap extraction

Use instead

```text
quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
```

from
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`.  For the
selected deviation `tau`, let `mu` be its PMF on `Option Nat`, let `V(none)`
be the Never payoff, and let `V(some t)` be the deterministic time-`t` payoff.
The declaration says exactly

```text
payoff(tau) = E_mu[V].                                      (3.1)
```

Here `V(none)` is the prescribed payoff because `d in B`.  If every finite
time satisfied

```text
V(some t) < V(none)+gamma,
```

then `none` also has strict inequality since `gamma>0`.  Choose any atom in
the nonempty support of `mu`.  All support values are at most the displayed
threshold and the chosen positive-mass atom is strictly below it.  Splitting
off that atom makes the expectation strictly below `V(none)+gamma`,
contradicting (3.1) and the ambient gap.  Thus, for the **same selected deleted
player**, there is a finite `t` with

```text
U_r(Lift_B(sigma),d)+gamma
  <= U_r(update (Lift_B(sigma)) d (QuitExactlyAt t),d).      (3.2)
```

This is an ordinary argument over a countable PMF, not presently a named
one-line extraction declaration.  Its key expectation identity is checked.
The distinction matters: epsilon-extremality alone yields `gamma-eta`, while
the complete stopping-law expectation plus the fact that Never is the
baseline yields the exact weak constant `gamma`.

### Mandatory repair

Replace Proposition 2 by (3.2), or retain the weaker proposition but replace
“loss is essential” by the exact explanation above and add the stronger
corollary.  Add these inspected sources:

- `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`:
  `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`;
- `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`:
  `quittingBehaviorStoppingLaw`.

## 4. Reached row and full-gap finite passport

The exact finite witness has a further valid consequence, audited separately
in
`notes/CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md`.
It is worth recording here because it identifies the strongest result of the
proposal.

Let

```text
ell_d(J) = min({0} union {r_d(S) : empty != S subset J}),
P_d(J)   = max(0,r_d({d})-ell_d(J)),
C_d(J)   = max({0} union
               {r_d(S union {d})-r_d(S) : empty != S subset J}).
```

For the selected finite time, the exact checked transport

```text
quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
```

in `UniformEquilibrium/Quitting/Paths/OutsiderNeverGluing.lean` gives

```text
finite-time gain = w_t * Delta_t,
```

where `0<w_t<=1`.  Hence `Delta_t>=gamma`.  The checked coalition expansion

```text
quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticEndpointDefectPolarity.lean`
writes `Delta_t` as a finite convex average of

```text
r_d({d})-N_{t+1}
```

on the empty retained coalition and

```text
r_d(S union {d})-r_d(S)
```

on nonempty `S subset J`.  Thus a coalition with positive conditional mass has
an **unweighted** toggle at least `gamma`.  In the empty case
`N_{t+1}>=ell_d(J)`, because Never's terminal payoff is an average of `0` and
retained-coalition rewards.  Therefore

```text
max(P_d(J),C_d(J)) >= gamma.                                (4.1)
```

The positive row probability is `w_t m_t(S)>0`.  Neither that probability nor
the probability-weighted atom is asserted to be at least `gamma`.

## 5. Sharp all-behavior deletion bound

The strongest surviving quantitative statement is also valid.  At time `t`,
let `c_t` be the probability every retained player Continues and
`a_t=1-c_t`.  The local endpoint difference obeys

```text
Delta_t <= c_t P_d(J)+a_t C_d(J)
         = P_d(J)+a_t(C_d(J)-P_d(J)).                       (5.1)
```

If `0<=A` and `a_t<=A` for every time, set `Abar=min(1,A)`.  Multiplying by
the preceding survival `w_t<=1`, splitting according to the sign of `C-P`,
and then averaging all pure-time/Never values through the exact stopping law
gives

```text
BR_d(Lift_B(sigma))-U_d(Lift_B(sigma),d)
  <= P_d(J)+Abar*(C_d(J)-P_d(J))_+.                         (5.2)
```

It is enough more generally to bound the source-weighted mass `w_t a_t` by
`Abar`; the conditional row bound is a clean stronger hypothesis.  State
`0<=A` explicitly.  For `A=1`, (5.2) becomes `max(P,C)` and recovers (4.1).

The sign and coefficients in (5.1) are correct: the solo premium is weighted
by the empty-row probability `c_t`, rather than charged at full weight.  This
is a strict refinement of the checked

```text
quittingBlockDeletionExcessBound = P+A*C
```

and its all-behavior consumer
`quittingBestReplyValue_liftDeletedProfile_le_add_excessBound`.  A narrow
search found no existing declaration with the sharpened positive-part formula.

## 6. Proposition 3: PASS and strengthens

For `B.Nonempty` and `B != univ`, the survivor subtype is nonempty and has
cardinality strictly below `minimal.playerCount`.  The application of

```text
MinimalFinQuittingCounterexample.exists_uniformEquilibriumPayoff_of_card_lt
```

to the block-native deleted reward table is correctly typed.  The resulting
uniform payoff supplies a terminal `gamma/2`-Nash profile because `gamma/2>0`.
The printed application of the weaker Proposition 2 then proves (4.1) in the
note with gain `gamma/2`.

After the repair above, the same survivor profile instead has a finite-time
deleted-player gain at least the full `gamma`; no second approximation loss is
needed.  More generally, for every `0<epsilon<gamma`, every selected terminal
`epsilon`-Nash survivor profile admits both the ambient behavioral witness and
an exact finite deterministic witness of gain `gamma`.

The note correctly makes no cross-block compatibility claim.  Re-solving after
adjoining the selected outsider is finite set growth, not behavioral
chronology or preservation of payoff coordinates.

## 7. Export and novelty assessment

The following parts are already checked structure or direct packaging:

- survivor/deleted localization is the witnessed version of the existing
  block-deletion split;
- cardinal-minimal production of uniform payoffs on every smaller nonempty
  player type is checked;
- exact payoff and deviation naturality under the Never lift is checked.

The genuinely new ordinary-mathematics refinements are:

- exact finite pure-time extraction with no `eta` loss;
- the reached unweighted-toggle passport (4.1); and
- the sharp convex deletion cap (5.2), improving `P+A*C`.

These are mathematically useful and suitable for a Lean handoff.  I do **not**
recommend a separate export packet yet.  They select one profile-dependent
deleted owner and one local row, but provide no ambient equilibrium, compiler,
Bellman edge, return, common support kernel, or well-founded invariant decrease.
Under the current conference gate they are an internal strengthening of the
checked deletion interface.  They would become export-worthy if a named live
question accepts the sharp inequality itself, or if a downstream consumer
uses the improved `P+min(1,A)(C-P)_+` chamber to close a maintained branch.

## 8. Minor presentation repairs

- The requested-falsification list repeats item 4 verbatim; remove one copy.
- If the finite minima/maxima are added, either assume the retained set is
  nonempty or use the existing `insertMin 0`/`insertMax 0` definitions so the
  empty boundary is literal.
- Continue to distinguish a positive-probability row with a large unweighted
  toggle from a large probability-weighted terminal atom.

