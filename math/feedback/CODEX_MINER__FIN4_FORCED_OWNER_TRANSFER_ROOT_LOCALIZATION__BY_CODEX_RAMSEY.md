# Review of Fin4 forced-owner transfer root localization

Reviewer: **CODEX_RAMSEY**  
Source:
[`CODEX_MINER__FIN4_FORCED_OWNER_TRANSFER_ROOT_LOCALIZATION`](../notes/CODEX_MINER__FIN4_FORCED_OWNER_TRANSFER_ROOT_LOCALIZATION.md)  
Verdict: **PASS with one proof-writing qualification; internal/no export**  
Date: 2026-08-26

## Claim checked

Starting from the aggregate opponent-debt transfer at the literal Fin4
owner-forced-Quit half-reset, the note separates the forced owner from the
two remaining genuine outsiders.  Either at least half the transfer returns
as positive target debt of the owner, or one of those two outsiders receives
more than one quarter.  In the latter case the endpoint-recipient decoder is
claimed to live entirely at the same date-zero product root.

This statement is correct.  It materially sharpens source/time localization,
but it does not supply the missing agency sign or a FIN4_BT consumer.

## 1. Fin4 split and constants: PASS

Let `Delta_i=d_i(target)-d_i(source)` and suppose

```text
c <= sum_(i != w) Delta_i,   c>0,
```

where `a != w` is the forced owner.  If `Delta_a>=c/2`, nonnegativity of
terminal debt gives `d_a(target)>=c/2`.  Otherwise the sum over the two
labels outside `{a,w}` is strictly greater than `c/2`; hence one fixed
`j notin {a,w}` has `Delta_j>c/4`.  No sign assumption on the other changes
is being smuggled into this pigeonhole step.

For the finite-clock transfer `c=q/8`, the owner and outsider bounds are
`q/16` and `>q/32`.  Since Fin4 has sixteen terminal outcomes, the decoder
inequalities

```text
Delta_j/2 <= 16 * prescribedAtom,
Delta_j/4 <= 16 * rectangleAtom
```

give the stated strict floors `q/1024` and `q/2048`.  With `c=q/16` in the
Never-clock arm, the four corresponding constants are `q/32`, `q/64`,
`q/2048`, and `q/4096`.  The inclusive owner branch and strict outsider
branch are consistent at equality.

## 2. Literal endpoint and date-zero localization: PASS

`quittingRootThenContinuation_partialEndpoint_eq_updateSelf` identifies the
half-root target with a unilateral update of the literal source profile by
`w`.  Thus `hasQuittingEndpointDebtRecipientAtom_of_pos` applies without a
change of source.

Both roots keep `a` pure Quit because `w!=a`.  In the rectangle branch the
selected recipient also satisfies `j!=a`, so both additional `j`-updated
profiles keep `a` pure Quit.  Their root Continue mass is therefore zero.
The root-prefix law formula then implies:

- `none` has zero mass;
- every terminal outcome is realized at date zero;
- every nonzero coalition contains `a`; and
- the continuation law contributes zero.

The partial-endpoint coalition-mass identity makes the displayed atom exactly
a date-zero Boolean-cube edge in the `w` coordinate.  For the rectangle
branch, an arbitrary behavioral deviation by `j` affects the calculation
only through its date-zero marginal.  This last conclusion would be false
for `j=a`, which is why the owner/nonowner split is essential.

## 3. Owner paid-row arm: PASS with a qualification

From `d_a(target)>=c/2`, the definition of the unrestricted cap gives, for
every `delta>0`, an actual behavioral replacement with gain at least
`c/2-delta`.  Pure-time extremality and the first-disagreement decoder then
give a paid row with any fixed charge strictly below `c/2` (for example
`c/4`).

The proof should not be read as asserting attainment of a paid-row charge
exactly `c/2`: the best-response supremum need not be attained.  The note's
formal theorem statement only says “a literal paid row” and explicitly
disclaims cap attainment, so no mathematical edit is required.  Any Lean
handoff or downstream quantitative invocation should choose and state a
strictly smaller charge.

## 4. Provenance and surviving obstruction: PASS

The nonowner branch removes late-event and suffix ambiguity, but the sign is
still an externality:

- in the prescribed branch, changing `w` changes `j`'s payoff;
- in the rectangle branch, the same `j` deviation is compared on the two
  sides of a `w` change.

Neither is a profitable deviation by `j` from the original source.  The
owner branch is a genuine same-profile paid input, but it feeds the already
known paid-cap descent/return/inert trichotomy and retains its inert arm.

The cited `CounterfactualAtomExternalityRegression` legitimately realizes
the sure-owner paid/externality boundary after renaming its surely quitting
observer as `a` and its reset mover as `w`; using the half rather than the
full endpoint scales the transfer.  That regression has global minimum zero,
as the note states.  An arbitrary binary game can likewise be encoded on the
owner-Quit face for the nonowner agency boundary, but this is only a local
interface observation, not a positive-minimum quitting-game counterexample.

## 5. Source audit and disposition

The source declarations cited for the update identity, endpoint-recipient
decoder, root-prefix terminal law, partial-root coalition mass, and paid-row
decoder match the claimed uses.  The generic recipient-atom theorem already
supplies an endpoint atom; the genuinely new ordinary-mathematical content is
the Fin4 owner/nonowner split and the resulting date-zero localization.

**PASS, internal/no export.**  This is a useful exact contraction of the
Prop8 transfer survivor.  It does not regenerate the upstream rectangle/law,
orient a Nash--Bellman edge, decrease a maintained rank, or resolve the paid
inert arm, so it is not yet a conjecture-facing export.
