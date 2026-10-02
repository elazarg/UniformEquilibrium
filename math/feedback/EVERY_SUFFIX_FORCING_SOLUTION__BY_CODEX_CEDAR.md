# Mathematical audit of the exact Nash--Bellman spine proposal by `CODEX_CEDAR`

Reviewed artifact: [`EverySuffixForcingSolution.lean`](../../EverySuffixForcingSolution.lean).
This is a static ordinary-mathematics and provenance audit.  I did not compile
the file or verify any new Lean declaration.

## Verdict

The core construction is mathematically valid and is genuinely stronger than
the earlier `exactOfRoots` observation for the **non-survival** fields.  A
bounded exact Nash--Bellman spine gives diagonal candidate pairs, zero
candidate debt, zero prescribed defect, and zero direct-debt defect.  Generated
secants compare those diagonal candidates with the literal executable tail.
Thus every forcing, boundedness, nonnegativity, generated-secant, and initial
*candidate*-debt field is automatic.

The construction does not solve the full chronological certificate.  Joint
and every-player-deleted survival must hold for the **same exact
Nash--Bellman roots**.  This is not a detachable clock condition: changing or
concatenating roots generally destroys exact root Nash and Bellman recursion.
By the two-label characterization, the remaining obligation is exactly to
select a bounded exact Nash--Bellman spine with at least two distinct
nonsummable marginal Quit streams.

For conjecture-facing endpoint existence, even that conditional implication
is not new.  The already-known positive-clock branch of
`uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine`
directly makes `value 0` a uniform-equilibrium payoff under the same
divergent-opponent-clock hypothesis.  The submission's genuine novelty is the
chronological-data adapter and the resulting clarification of the isolated
non-survival fields, not a stronger endpoint producer.

There is no omitted actual-initial-debt or carrier hypothesis in the full
conditional theorem.  Candidate pairs in chronological data need not be
carrier points.  Once the same roots have the two survival fields, semantic
shadowing forces the actual root profile to equal the diagonal candidate at
date zero and hence to have zero actual debt.  Without survival, however, the
actual initial debt can be positive and is completely uncontrolled.

## 1. Exact algebra of the diagonal spine

Let `v_t` be bounded payoff vectors and `q_t` product roots satisfying

```text
v_t = successorPayoff(v_(t+1),q_t),
q_t is exact Nash against continuation v_(t+1).       (1.1)
```

Exact one-stage Nash says that for every player the prescribed mixed action
value is the maximum of the forced-Quit and forced-Continue values.  Therefore

```text
Prefix(q_t,(v_(t+1),v_(t+1)))=(v_t,v_t).              (1.2)
```

Annotating date `t` by prescribed value `v_t` and candidate debt zero makes
both candidate coordinates diagonal.  Equation (1.2) gives zero prescribed
defect and zero direct-debt defect at every date.  The initial candidate debt
is literally zero, and boundedness of `v_t` gives the prescribed bound.

The semantic pair stored by the chronological datum is still the actual pair
of the literal infinite root tail.  It need not equal `(v_t,v_t)`.  The
secant is selected between the actual successor pair and the diagonal
candidate successor.  Monotonicity of the cap prefix supplies a coefficient
between zero and player-deleted Continue mass and gives the required generated
identity.  This is exactly the bridge needed by the chronological compiler;
no assertion that `v_t` lies in the terminal semantic carrier is used.

Consequently, if the same `q_t` also have vanishing joint and every-player-
deleted survival on every suffix, these data inhabit the full certificate at
every positive accuracy.  The forcing expressions are identically zero, so
their every-suffix quantifiers and slack order are automatic.

## 2. Actual debt is a consequence only with clocks

The distinction between candidate and actual debt is binding.  Consider two
players, give every nonempty quitting coalition payoff `(1,1)`, take

```text
v_t=(1,1),
q_t=all Continue
```

at every date.  Continue and Quit both have one-stage value one against the
diagonal tail, so (1.1) holds.  The diagonal chronological data have zero
candidate debt and zero defects.  But the literal infinite all-Continue
profile receives the Never payoff zero, while either player can Quit and
obtain one.  Its actual date-zero debt is one.  Joint and deleted survival are
identically one, so the missing hypothesis is exactly visible.

Conversely, suppose the clocks vanish.  Proposition 3 of
[`CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md`](../notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md)
applies with zero seams: bounded Bellman annotations are rigid under vanishing
joint and deleted clocks.  Hence the actual terminal payoff and cap equal
`(v_0,v_0)`, and actual debt is zero.  Equivalently, applying the
chronological estimate at every positive accuracy to the same zero-error data
forces actual debt below every positive number.

Thus `actual-initial-debt <= eta` is neither a missing input nor an automatic
fact of the bare spine.  It is the conclusion produced by combining the exact
spine with persistent clocks.

## 3. Comparison with `exactOfRoots`

For arbitrary literal roots, `QuittingChronologicalDebtData.exactOfRoots`
uses the actual semantic pair of each reached suffix.  It therefore has exact
recursion and zero defects, but its candidate debt at date zero is the actual
terminal exploitability.  Small initial debt remains an assumption.

The Nash--Bellman construction makes a different choice: it uses diagonal
nonsemantic candidates with zero debt and nontrivial generated secants.  It
therefore removes the actual-initial-debt hypothesis from the input, at the
price of requiring the roots themselves to lie on one exact Nash--Bellman
spine.  This is a genuine mathematical addition, not a restatement of
`exactOfRoots`.

It also answers Warning 1 in
[`CLAUDE_ERDOS__EVERY_SUFFIX_FORCING_COLLAPSE.md`](../notes/CLAUDE_ERDOS__EVERY_SUFFIX_FORCING_COLLAPSE.md):
without survival, all non-survival fields—including zero initial candidate
debt—can indeed coexist with large actual debt.  The constant all-Continue
example above is an exact witness.  The earlier factor-four converse remains
correct for a **full** certificate because that converse uses the survival
fields.

## 4. Interaction with the persistent-clock packet

The formalized two-label reduction applies verbatim to the selected spine
roots: all joint and one-player-deleted suffix survivals vanish exactly when
at least two distinct players have nonsummable marginal Quit hazards.  This
turns the residual producer into the clean selection problem

> construct one bounded exact Nash--Bellman spine whose roots carry two
> persistent labelled marginal-hazard streams.

The atom-derived block concatenation in Cedar Proposition 6 does not supply
this automatically.  Those literal atom roots have exact reached-tail data
under `exactOfRoots`, but they are not shown to be exact root Nash against one
diagonal Bellman value sequence.  Conversely, an arbitrary exact spine may be
the all-Continue spine and carry no clock at all.  One cannot combine the two
results by replacing spine roots with clock-rich atom blocks: both equalities
in (1.1) would have to be reproved on the modified chronology.

The packet-boundary charge criterion provides an equivalent way to verify the
clock once a spine is selected, but it supplies no selection theorem.

## 5. Exact novelty and remaining gap

The genuinely new ordinary-mathematics content is:

1. exact Nash--Bellman data solve `EVERY_SUFFIX_FORCING`'s non-survival fields
   unconditionally, even the small initial candidate-debt field;
2. generated secants permit these diagonal candidates without pretending
   they are actual semantic carrier points; and
3. the full route reduces to a persistent-clock selection on the exact
   Nash--Bellman correspondence.

Item 3 is a reframing, not a new existence implication.  The direct
positive-clock consumer for exact Nash--Bellman spines already covers
unrestricted behavioral deviations and yields the uniform payoff under those
same clocks.  The certificate construction supplies a second proof route and
stronger bookkeeping, while leaving the known summable-clock exceptional
branch unchanged.

The following stronger readings are not established:

- that the supplied generic exact spine has either survival field;
- that a clock-rich exact spine exists in every finite quitting game;
- that atom/reset provenance is retained by the generic spine;
- that survival can be imposed after the spine is constructed; or
- that the uncompiled file is a checked or integrated Lean result.

Accordingly, “only persistent clocks remain” is accurate as a certificate
field statement, provided “on the same exact spine” is explicit.  It is not a
full solution of the source-matched producer.  If such a spine were produced,
the result would be stronger than a forcing estimate: its literal root profile
would already be an exact terminal Nash profile.
