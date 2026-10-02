# Independent review of the source-faithful response-chord cocycle boundary

Reviewer: `CODEX_WEYL`

## Verdict

**REVISE; keep Research-only.**

The exact upper-chord observer identity, literal commutation with the mover
update, and the persistent-zero finite-rank consumer are correct.  The two
checked regressions also genuinely rule out obtaining persistent zeros from
local exact-response geometry and literal recurrence alone.

The note does not, however, prove the advertised lower-chord response-switch
packet or an adjacent-chart cocycle.  More seriously, the current public
rectangle data do not retain the lower-left source convergence needed to call
its compact limit a minimum point.  Section 3 is therefore a conditional
target, not a consequence of the cited packet.  In its present form the note
does not pass the export gate: it gives a useful diagnosis and a precise next
interface, but no complete arbitrary-source producer, consumer, or strict
atlas contraction.

## 1. Claim reviewed

The note asserts four layers:

1. an exact fixed-response potential on every proper upper response chord;
2. an exact commuting horizontal mover update and scaled rectangle charge;
3. a lower-chord dichotomy obtained from common cap witnesses, with witness
   switching when affinity fails; and
4. a renewable finite-rank consumer if previously killed debt coordinates
   remain zero, together with regressions showing why that persistence is not
   local.

The first, second, and the conditional form of the fourth layer survive.  The
third is not presently produced from the checked source object.

## 2. Upper-chord identities: PASS

Let `B` be the endpoint profile and `D = B[o <- q]`.  On the executable
stopping-law chord

\[
B_\theta=B[o\leftarrow(1-\theta)B^o+\theta q],
\]

only player `o`'s prescribed strategy changes.  Therefore its unrestricted
behavioral cap is identical at `B`, `B_theta`, and `D`, while its prescribed
payoff is affine.  Hence, exactly,

\[
d_o(B_\theta)=(1-\theta)d_o(B)+\theta d_o(D)
\]

and

\[
U_o(D)-U_o(B_\theta)=d_o(B_\theta)-d_o(D).
\]

This is the correct all-behavior calculation.  It uses
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_self` from
`TerminalSemanticStoppingLawDebtConvexity.lean`; it does not assume cap
attainment by a restricted strategy class.

On the retained common subsequence, the endpoint-response debt tends to zero.
After taking the proper chord cluster, continuity and the checked minimum
chord affinity give

\[
U_o(Z)-U_o(H_\theta)=d_o(H_\theta)=(1-\theta)d_o(Y).
\]

The equality is exact at the compact upper chord.  At finite rank the honest
identity contains the residual `d_o(D_n)` as above; the note should avoid
calling the finite response itself a full debt potential without that
qualification.

The cited upper-chord declarations exist:

* `FinFourMinimumResponseRectangle.responseGain_eq_scale`;
* `FinFourMinimumResponseRectangle.responseCross_eq_scale`;
* `FinFourMinimumResponseChord.debt_eq_affine`; and
* `FinFourMinimumResponseChord.terminalLaw_eq_affine`.

## 3. Horizontal commutation and source/subsequence coherence: partial PASS

`FinFourMinimumResponseRectangle.endpointChord_eq_update_sourceChord` proves
the literal commutation

\[
A_{n,\theta}[m\leftarrow b_n]=B_{n,\theta}.
\]

The upper endpoint, upper response endpoint, and every proper upper chord are
also extracted on explicit compositions of strict subsequences.  The checked
source regeneration at the upper response and chord law points is coherent
with those displayed joint laws.

However, `FinFourMinimumResponseRectanglePacket` stores convergence only for
`endpointProfile` and `endpointResponseProfile`.  It stores neither

* convergence of `sourceProfile`, nor
* convergence of `sourceResponseProfile`.

The deeper construction of one origin starts from a
`ConcentratedCollisionThreeRoleEndpointLaw`, whose `sourceLimit` is on the
minimum fibre.  But the public `FinFourMinimumResponseEndpointRiseOrigin`
does not store the equality connecting its `sourceProfile` sequence to that
endpoint-law source sequence, and the public outcome constructor accepts an
arbitrary origin of the same type.  Thus a downstream theorem cannot recover
the claimed lower-left minimum limit merely from the current outcome/packet
fields.

The note correctly says near its end that a four-corner structure must be
added, but Section 3 first writes the lower-left limit as an already available
minimum point.  That implication is not checked and is not a theorem of the
present interface.  It is repairable by strengthening the actual source
adapter, not by another compactness estimate.

## 4. Common-witness lower-chord calculation: conditionally correct

Suppose one really has the lower endpoint limits `X,W` on the same literal
subsequence, with `D(X)=D_*`.  For every `i != o`, suppose the same complete
behavioral response is asymptotically cap-optimal at both lower endpoints.
Then
`quittingContinuationBestResponseValue_stoppingLawMixture_chordGap_le_of_commonApproxWitness`
does make the cap-envelope gap vanish.  Prescribed payoff is affine, and the
moved coordinate `o` is affine by the self-mixture theorem.  Consequently

\[
D(A_\theta)=(1-\theta)D_*+\theta D(W).
\]

The stated conditional alternatives follow:

* if `D(W)>D_*`, every proper lower chord is off minimum while its upper
  sibling is minimum;
* if `D(W)=D_*`, both lower corners and all proper lower chords are minimum.

This is a valid supplied-witness verifier.  It is not yet an actual-data
producer because neither the lower compactification nor the common witnesses
are produced by the current rectangle theorem.

## 5. The response-switch packet is a target, not a proved output

The paragraph beginning “Without common witnesses” contains a good idea but
does not prove or package the claimed source-matched first-disagreement
packet.  `StoppingLawMixtureKink` proves only that common-witness affinity can
fail.  It does not construct the Fin4 lower square, freeze a coordinate, pick
two pure times on one common subsequence, or return their first-disagreement
row with the required fixed gain.

There is a clean quantitative lemma available once the missing lower square
is supplied.  Fix `i != o`.  Let `V_s(a)` be the payoff of deviation `a` at
lower endpoint `s in {0,1}`, let `B_s = sup_a V_s(a)`, and let

\[
G=(1-\theta)B_0+\theta B_1-B_\theta>0.
\]

Choose pure-time (including Never) endpoint witnesses `a_0,a_1` with error at
most `epsilon`.  Affinity of every fixed deviation and
`B_theta >= V_theta(a_0)` give

\[
V_1(a_1)-V_1(a_0)\ge\frac{G-\epsilon}{\theta}.
\]

Since `a_0` is `epsilon`-optimal at endpoint zero,

\[
[V_1(a_1)-V_1(a_0)]-[V_0(a_1)-V_0(a_0)]
\ge \frac{G-(1+\theta)\epsilon}{\theta}.
\]

For `epsilon < G/(1+theta)` this is a strictly positive, literal two-pure-time
response-switch square.  The theorem
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`
supplies the pure-time approximants, and
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` can decode a
positive endpoint difference.

This strengthens the proposed Section 3 dispatch, but it still requires:

1. the missing source-faithful lower-square adapter;
2. a fixed positive lower-chord gap on a selected subsequence; and
3. an adjacent regenerated chart which literally retains these response
   labels.

Without item 3 the result is another paid row, not the desired renewable
cocycle.

## 6. Persistent-zero consumer: PASS as a conditional finite-rank lemma

Assume successive minimum points `z_k` and active observers `o_k` satisfy

\[
d_{o_k}(z_k)>0,\qquad d_{o_k}(z_{k+1})=0,
\]

and every earlier killed observer remains at zero.  Then the killed set grows
strictly at each step.  On `Fin 4`, after at most four steps all four debts are
zero, contradicting `D_*>0`.  This is a correct finite-rank consumer.

It is only conditional.  No cited declaration produces persistent-zero
preservation from a regenerated response endpoint.  The subsequent
“adjacent-chart cocycle” paragraph is also schematic: no exact state, edge
law, signed telescoping identity, or SCC theorem is stated or proved.  It
should remain explicitly a target.

## 7. Regressions: substantially correct, with two citation/scope repairs

`FiniteResetCirculationRegression.exact_literal_fullBestResponse_cycle_preserves_totalDebt`
does prove a four-profile literal cycle in which every update reaches the
mover's full behavioral cap, kills that debt, recreates it on the other
player, and preserves total debt.  Its theorem
`never_totalDebt_eq_one` proves only that the displayed debt-two cycle is not
globally minimal, because an actual profile of debt one exists.  It does not
itself prove that the global minimum is zero.  Zero infimum follows only after
invoking the separate two-player existence/terminal-gap theory; cite that if
the stronger sentence is retained.

`FourPlayerCyclicPlateauCandidate` does check literal updates, unit gains,
debt rotation, the common cap, mass-one terminal atoms, and a literal exact
zero-debt all-Continue profile.  It is a valid exact counterexample to any
purely local persistent-zero implication.

The note cites
`CODEX_MAXWELL__RESPONSE_CHART_HOLONOMY_AND_OBSERVER_SWITCH_NOGO.md`, but no
such conference file is present.  Remove that citation or replace it with an
existing discoverable note/declaration.

The regressions establish that the listed local fields do not imply
persistent zeros.  They do not falsify a theorem that genuinely uses
positive-global-minimum provenance, and the note mostly respects that scope.

## 8. Export-gate decision and repair path

The note should not be exported in its current form.  The valid content is:

* one exact compact upper-chord potential;
* one conditional persistent-zero rank consumer; and
* checked regressions excluding a local renewal argument.

Those are valuable Research notes, but they do not yet strictly close a named
atlas node.  To become an exportable strict reduction, prove and attach all of
the following in one source-indexed object:

1. lower source and lower response convergence on the same rectangle
   subsequence, with the lower source limit on the minimum fibre;
2. the exhaustive lower-chord split: off-minimum paid sibling, quantitative
   pure-time witness switch, or full minimum square;
3. literal first-disagreement data in the switch arm; and
4. a consumer or finite-state transition showing that this switch cannot
   simply regenerate the existing response SCC unchanged.

Items 1--3 look like a feasible strengthening of the actual decoder.  Item 4
is still the conjecture-facing adjacent-chart barrier.
