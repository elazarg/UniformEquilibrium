# Review of hidden-reset value-of-information passport

Reviewer: `CODEX_ROOT`

Reviewed note:
`notes/CHATGPT_EXTERNAL__HIDDEN_RESET_VALUE_OF_INFORMATION_PASSPORT.md`

## Claim reviewed

The note interprets independent complete-stopping-law resets as one actual
behavioral profile with hidden private selectors.  It claims:

1. exact affine prescribed-payoff and convex cap identities;
2. a uniform `O(h^2 lambda)` Boolean-cube remainder for expected total debt;
3. a common approximately optimal pure quit time at the source and every
   positive-weight singleton face;
4. localization of a positive information gap to a one-bit pure-time witness
   switch and hence a paid first-disagreement row;
5. positive-debtor/atom-observer label alignment in the flat no-entry branch;
6. no chronological or paid-admissible-return conclusion.

## Verdict

**PASS for the claims above, with the stated scope.**  I found no unresolved
mathematical objection.  This is one substantive independent review of an
external contribution.  It is not a review of a full-conjecture result.

## Detailed check

### Probability, information, and agency

The selectors are independent private draws made at the level of complete
stopping laws.  The stopping-law mixture is behaviorally realizable, so the
hidden object is an ordinary behavioral profile, not a correlated public
device.  A unilateral deviator observes no selector.  For every fixed
deviation, payoff is multilinear in the opponents' selectors.  Taking the
supremum after averaging can only reduce the value relative to revealing the
selectors before choosing the deviation.  The own selector disappears after
the player's complete strategy is replaced.  These facts justify equations
(1)--(7) without enlarging the deviator's information or restricting its
behavioral power.

Approximate pure-time attainment is sufficient throughout; no best-response
attainment is assumed.

### Uniform cube estimate

For one inner reset edge of weight `lambda`, bounded rewards give

```text
|Delta U_i| <= 2 M lambda,
|Delta B_i| <= 2 M lambda.
```

The cap of the reset owner is unchanged because the cap replaces that
player's prescribed strategy.  Hence the owner-debt edge costs at most
`2 M lambda`, every other coordinate at most `4 M lambda`, and total debt at
most `(4N-2) M lambda` (`14 M lambda` for four players).

Writing each higher Boolean difference as a signed sum of
`2^(|T|-1)` such edges proves

```text
|partial_T D(empty)| <= 2^(|T|-1) (4N-2) M lambda.
```

The exact product-Bernoulli Möbius formula then gives the claimed uniform
`O(h^2 lambda)` remainder.  No differentiability or stable cap maximizer is
used.  This repairs the main gap in the original draft.

### Flat schedule and passport

The checked source-excess condition gives `delta_n -> 0`.  A schedule can be
chosen with `h_n -> 0` and `delta_n/h_n -> 0`.  Flat circulation kills the
limiting singleton linear term.  Global minimality applies to the hidden
mixture because it is an actual behavioral profile.  Therefore the sum of the
nonnegative information gaps is `o(h_n lambda_n)`.

The empty face has asymptotically unit probability and each mover with
positive circulation weight has singleton probability comparable to `h_n`.
Dividing the weighted regret bound consequently yields `o(lambda_n)` regret
on precisely those faces.  A `k`-face has only order `h_n^k` mass, so the note
correctly refuses to claim comparable control for doubletons or higher faces.

### Information-gap localization

The one-bit inequalities follow by testing the hidden cap with near-maximizers
from the two endpoints.  They produce an oriented pure-time preference
reversal.  The checked theorem
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` converts a
positive endpoint pure-time difference into a literal paid
first-disagreement row, including the `Never` case.

Revealing finitely many selector bits gives a telescoping sequence of expected
conditional caps.  A positive total gap therefore localizes to one opponent
bit and one fixed preceding-bit context.  The note correctly distinguishes
this witness rectangle from a two-reset cap square.  It also correctly warns
that a gap of order `h_n lambda_n` need not yield a fixed positive gain.

### Flat-no-entry label alignment

For a reset owner `a`, the negative diagonal tangent and zero column sum force
a positive off-diagonal recipient `o`.  Under no support entry, the checked
`mem_active_of_tangent_pos_of_noEntry` theorem makes `o` an active
positive-debt coordinate.  The outer selector changes its debt by a vanishing
amount under the one-edge Lipschitz estimate.  Thus the atom observer and a
positive debtor already agree at the label level in this branch.

The affine source/singleton/full-endpoint argument also gives the stated
alternative: either the common witness extends to the full endpoint, or a
full-endpoint regret bounded away from zero yields a fixed-positive paid row.

## Boundary and falsification checks

1. A two-witness, one-bit payoff table with opposite endpoint maximizers has a
   positive information gap while all squares in irrelevant reset coordinates
   vanish.  This falsifies the stronger information-gap-to-two-reset-square
   claim and supports the note's narrower rectangle conclusion.
2. Face weights of order `h^k` show that the weighted-regret argument cannot
   provide first-order control on arbitrary higher-dimensional faces.
3. The argument does not make the conditional selector context reachable
   from the original source, preserve a reach floor, or preserve labelled
   clocks.  It therefore cannot be promoted to conditioned reprojection or a
   chronological certificate.
4. A positive but vanishing information gap does not meet the maintained
   fixed-gain paid producer.  The note states this explicitly.

## Source audit

The review compared the argument with the following checked development:

- complete stopping-law behavioral realization and payoff affinity in
  `StoppingLaw/TerminalSemanticStoppingLawMixture.lean`;
- simultaneous reset profiles and existing unilateral passport alternatives
  in `TerminalSemanticSimultaneousResetMinimumDichotomy.lean`;
- `source_excess_over_scale_tendsto_zero` in
  `StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
- fixed-deviation reset-cube identities in
  `StoppingLaw/TerminalSemanticStoppingLawResetCube.lean`;
- witness-switch and common-passport regressions in
  `TerminalSemanticSimultaneousMixtureWitnessSwitchRegression.lean` and
  `TerminalSemanticCommonWitnessPassportRegression.lean`;
- the paid-row decoder in
  `TerminalSemanticPaidFirstDisagreement.lean`; and
- `mem_active_of_tangent_pos_of_noEntry` in
  `StoppingLaw/OffDiagonal/PositiveDebtTangentCycle.lean`.

The repository contains the component one-coordinate mixture facts and
related regressions, but the search found no existing theorem packaging the
product-selector information identity, uniform total-debt Möbius remainder,
singleton-star common passport, and flat-no-entry observer/debtor alignment.
The result is therefore not merely a restatement of one checked declaration.

No external-paper claim is used.

## Export-gate reassessment

The notebook has since been rewritten as a clean, self-contained packet with
exact statements, boundary tests, a source audit, and a Lean handoff.  Its
remaining obstacle is the importance/consumer gate.  Support-rank descent has
removed flat charged circulation as an independent live exit, while this
packet neither constructs the active paid payoff near-return nor consumes the
four-player full-support hard residual.  Under `exports/README.md`, it remains
internal until a named actual-data adapter composes one of its conclusions
into an indexed live obligation.  This is not a mathematical objection to the
reviewed results.
