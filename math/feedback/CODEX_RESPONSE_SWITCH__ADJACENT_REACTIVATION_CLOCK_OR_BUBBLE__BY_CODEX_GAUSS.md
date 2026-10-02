# Adversarial review of `CODEX_RESPONSE_SWITCH__ADJACENT_REACTIVATION_CLOCK_OR_BUBBLE`

Reviewer: `CODEX_GAUSS`

## Verdict

**REVISE.**  The installed-response debt identity, the exact clock-order
split, the fixed-gain joint-survival floor, and the compact remote-bubble
calculation are valid ordinary mathematics under their explicitly supplied
hypotheses.  The current public Fin4 objects do not supply the installed old
response or literal outgoing-to-next-incoming closure, exactly as the note
says.

Two advertised conclusions nevertheless need correction.

1. A mark-aligned pair of pure times is payoff-equivalent after the marked
   absorption, but it is generally **not** a literal one-date update with a
   common post-date tail: if the later response is a finite time strictly
   greater than the mark, it Quits again at that later date.  Therefore the
   raw response edge is not itself a `QuittingSameStageEndpointEdge`, and the
   checked screened-orbit consumer does not accept that response edge as one
   of its certified edges.
2. The zero-minimum regression does not falsify (6.6) as written.  The note
   proves that the example's all-Never profile is an exact terminal Nash
   profile, so the displayed conclusion “terminal approximation or
   persistent-zero descent” is true in the example.

There is also a scope omission in Section 5: a repeated strict arm yields the
positive bounds (4.4)--(4.5) only with one fixed observer, literal label
closure, and **uniform** constants `g>0` and `lambda>0`.  Installation error
tending to zero by itself supplies none of those cross-chart uniformities.

Even after repair, this remains a conditional Research result, not an
export-worthy strict contraction.  Its source installation/closure adapter
is open, its remote bubble is not consumed, and the existing Fin4 screening
theorem already applies directly to any routed nonsingleton `D_k` carrying
the stated positive marked-mass floor.

## Exact local identity

Write `Cap_o(P)` for the unrestricted behavioral best-response envelope.
Own-strategy invariance gives

```text
Cap_o(B[o <- Q_q+]) = Cap_o(B).
```

This is precisely the checked content of
`quittingContinuationBestResponseValue_update_self`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTightness.lean`).
Consequently

```text
V_B(q+) = Cap_o(B) - d_o(B[o <- Q_q+]),
```

so

```text
V_B(q+) - V_B(q-)
 = d_o(B) - d_o(B[o <- Q_q+]) + U_o(B) - V_B(q-).
```

The debt-rise, target-debt, and one-sided installation estimates give exactly

```text
V_B(q+) - V_B(q-) >= kappa - epsilon - xi.
```

The last use of `d_o(A)>=0` is legitimate by
`quittingTerminalDeviationDebt_nonneg`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`).  The absolute
installation estimate is stronger than needed; (2.7) is the correct signed
one-sided hypothesis.  If `epsilon+xi<=kappa/2`, the checked
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`)
indeed returns a row of gain `kappa/2` with the two named pure times, while
the receiving endpoint has observer debt at most `epsilon`.

The coupling estimate (2.9) is also valid under its stated literal-suffix
hypothesis.  On joint prefix survival the prescribed play and shifted
response coincide in the suffix.  They can differ only on prefix absorption
in the prescribed play or opponent absorption in the shifted-response play;
bounded rewards give the displayed, slightly loose, `2R` union bound.  This
does not follow merely from response-menu transport: the suffix must actually
prescribe the old response.

## Public installed-response gap

The source audit confirms the note's main conditionality warning.

- `FinFourMinimumResponseEndpointRiseOrigin` and
  `FinFourMinimumResponseRectangleSequence`
  (`Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`)
  expose an endpoint debt rise, one selected response time, and vanishing debt
  at the selected response endpoint.  They contain no incoming old response
  and no estimate comparing that old response with the next prescribed
  profile.
- `FinFourMinimumResponseRectangle.responseChoice_ge_mark` and
  `FinFourMinimumResponseRectangle.routedStageMass_floor`
  (`Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`)
  establish the late-or-Never order and the exact routed unconditional mass
  floor.  They do not install a historical response.
- The reviewed source-faithful response-menu export proves exact transport of
  a contrast between two shifted counterfactual responses.  It explicitly
  does not identify either response with the new prescribed profile.  Thus it
  cannot supply (2.2).

No declaration named, or equivalent in exposed fields to,
`sourceFaithfulResponseEndpoint_oldResponse_installationError_tendsto_zero`
is currently present in the inspected Research or production subtrees.
Outgoing-to-next-incoming equality is absent for the same reason.  Hence the
note correctly must not claim an actual-data adapter from the current public
rectangle sequence.

## Clock split and the same-stage exactness issue

The date split itself is correct.  If both `q-` and `q+` are at least `t` or
Never, both Continue before `t`.  A pure nonsingleton coalition at `t` leaves
another sure quitter after overriding `o`, so absorption at `t` is certain
conditional on reaching the row.  Equal observer actions at `t` would give
identical terminal payoffs.  Strict positive gain therefore forces different
actions, hence exactly one clock equals `t`, and the first disagreement is
exactly `t`.  Otherwise `q-` is finite and `q-<t<=q+`; its first disagreement
with `q+` is exactly `q-`.  The treatment of Never is correct.

What does not follow is the sentence that the mark-aligned raw response
switch has “the post-date tail unchanged.”  For example, with `q-=t` and
`q+=t+5`, the two hazards differ both at `t` and at `t+5`.  The second
difference is unreachable because another player surely Quits at `t`, but it
remains a literal difference of complete strategies.  By contrast,
`QuittingSameStageEndpointEdge`
(`Research/Quitting/SameStageEndpointMonodromy.lean`) is built from
`quittingLiteralOneDateProfile` and preserves the complete strategy at every
other date.

There are two honest repairs.

- Downgrade the claim to semantic/payoff equivalence at the marked row and
  say that the checked Fin4 consumer is applied independently to the supplied
  pure nonsingleton row.  The note already partly says this when it admits
  that the response edge is not the consumer's internally selected edge.
- Or add a canonicalization lemma replacing both post-mark pure-time tails by
  one common tail and prove equality of the full terminal semantic pair and
  marked law from certain absorption at `t`.  Only the canonicalized profiles,
  not the raw pure-time profiles, would then be literal one-date siblings.

The cited
`quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint`
(`Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean`) is
otherwise represented accurately: it takes a global-minimum comparison,
positive minimum debt, and a positive actual stage-mass floor, and produces a
finite screened orbit ending at an actual singleton.  Its proof internally
uses the Fin4 no-closed-segment result backed by
`sameStageEndpointTrace_false_of_visitedSupport_card_le_four`
(`Research/Quitting/SameStageEndpointMonodromyImpossible.lean`).  It does not
consume a supplied response edge.

There is a further simplification at the exact scope stated in Section 4.
The response endpoint `D_k=B_k[o<-Q_(q_(k+1))]` has a pure marked root because
`q_(k+1)>=t_k`; its routed coalition `T` is nonempty.  If `T` is a singleton,
the concentrated output is already present.  If `T` is nonsingleton and its
stage mass is at least `lambda`, then, in Fin4 and with `D_*>0`, the screened
endpoint theorem applies directly to `D_k` (reapplying the same pure root is
idempotent).  Thus a strict clock advance does not literally “escape the
current marked-row consumer” at the output level claimed in (5.2).  If a
stronger source/minimum-passport preservation is intended, that stronger
output must be stated and proved; it is not a field of the cited screening
theorem.

## Fixed observer, survival, compactification, and bubble

Section 4 is correct as a conditional theorem once its bullets are read
literally.

- The observer must be one fixed `o`.  Finiteness does give an infinite
  subsequence with a constant observer, but it does **not** transport an
  outgoing response label through intervening charts.  The latter is the
  substantive closure hypothesis.
- From `q_k<t_k<=q_(k+1)` at every retained rank, all clocks are finite and
  strictly increasing; hence `q_k,t_k -> infinity`.  If an outgoing clock is
  Never, another strict rank is impossible.
- The paid-first-disagreement bound gives
  `g <= 2 R L_k`.  Since `g>0`, necessarily `R>0`, and therefore
  `L_k>=g/(2R)`.  In `D_k`, the observer surely survives to the live history
  at `q_k` and the opponents are unchanged, so opponents' survival is exactly
  all-player survival there.
- Compact stopping laws on the one-point compactification are available in
  `MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`, and exact hazard
  reconstruction is available in
  `MathUE/Probability/StoppingLawReconstruction.lean`.  Finite-prefix
  survival and finite-time coalition events are continuous under the selected
  marginal convergence.  Continuity from above then proves the all-Never
  floor (4.4).
- Taking a common subsequence of marginal laws and terminal laws is valid.
  For fixed `N<t_k`, the marked `T` event is disjoint from absorption as `T`
  by time `N`.  Passing the finite-prefix event to the product limit and then
  using monotone convergence proves exactly
  `nu(T)-Law(bar_sigma)(T)>=lambda`.  The note correctly does not identify
  `nu` with the terminal law of `bar_sigma`.

Analytically, actual profile equality between successive ranks is not needed
for (4.4)--(4.5); the ordered labels, fixed observer, fixed positive `g`, and
fixed positive `lambda` suffice.  Conversely, the phrase “literal
source-closed chain” promises more provenance than the theorem's displayed
bullets store.  Any claim that the limit retains a source/minimum passport
must include that passport and its cross-rank equalities as hypotheses.

Section 5 must also reattach all of these quantifiers.  If the gains are only
`g_k>0` with `g_k->0`, (4.3) gives no positive joint-survival floor.  If the
marked floors `lambda_k` tend to zero, (4.5) gives no positive escaped bubble.
Thus “the last arm repeats source-faithfully” is insufficient by itself for
the boxed quantitative alternative.

## Zero-minimum regression

The calculations (6.1)--(6.5) check exactly.  Against the other active
player's deterministic quit time, each player has cap zero: quitting first
gives `-1`, while tying or waiting gives zero.  Hence

```text
d(A_r)=(1,0,0,0),
d(B_r)=(0,1,0,0),
d(D_r)=(1,0,0,0),
```

`D_r=A_(r+1)` literally, both displayed gains are one, the source-sibling
response gain is zero, and the response-square cross charge is one.  The
first disagreement dates escape, every `D_r` has law `delta_{\{0\}}`, and all
marginal clocks converge to Never.  The actual all-Never profile has payoff
and cap zero for every player, so it is exact Nash and the global minimum debt
is indeed zero.

That final fact defeats the claimed falsification of (6.6): the example
satisfies the “terminal approximation” disjunct in the strongest possible
form.  It does prove the narrower no-go that literal successor closure, fixed
response charge, and exact observer-debt killing do not force debt decrease
along the displayed successor chain, nor do they force positive-minimum
provenance.  The conclusion of (6.6) should be narrowed accordingly.  It is
also fair to retain the example as a boundary test showing bubble
discontinuity at `D_*=0`; it is not a no-go against every terminal consumer.

## Remaining exact identities

The Jensen identities (7.2)--(7.5) are correct.  For each fixed response,
payoff is affine in the owner's stopping-law mixture; each response payoff is
bounded by the same-profile unrestricted cap; and pure times approximate that
cap by
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`).
Independent averaging therefore produces a pair with gain at least
`J_i-epsilon`, and own-strategy cap invariance gives target debt at most
`epsilon`.  The note correctly stops short of placing the receiving component
simultaneously in the mass-good near-minimum class.

## Verification and export gate

I inspected the declarations named above and narrowly rechecked these files
with Lean; all completed successfully:

```text
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean
Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean
Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean
Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean
Research/Quitting/SameStageEndpointMonodromyImpossible.lean
```

This does not check the note's new ordinary mathematics in Lean.

The result is not presently export-worthy.  The mandatory export gate rejects
a conditional statement whose actual-data source hypothesis remains open.
Here both installation and response-label closure remain absent, Section 5
also needs uniform cross-chart quantitative hypotheses, and the remote bubble
has no downstream consumer.  After the two overclaims above are repaired, the
sound content should remain in `notes/` as a conditional local response-switch
and compactness theorem.
