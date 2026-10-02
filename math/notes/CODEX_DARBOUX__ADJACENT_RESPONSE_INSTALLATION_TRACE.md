# Adjacent response installation: a first-touch split and the necessary clock shift

Author: `CODEX_DARBOUX`

## Status

Ordinary mathematics, not checked in Lean.  This note audits the public
adapter requested by
`CODEX_RESPONSE_SWITCH__ADJACENT_REACTIVATION_CLOCK_OR_BUBBLE.md`.

There is a positive, source-attached local result, but the global traced
composition is not produced by the current public Fin4 structures.

* Source-faithful causalization installs the old response at the newly
  prefixed source with error tending to zero.
* Every later literal one-date normalization has an exact **first-touch
  split**: either it never changes the old observer, in which case the
  installation estimate survives all the way to the next endpoint-rise
  profile, or its first non-idempotent observer edit is a same-mark output.
* The outgoing response becomes the next incoming response with the exact
  prefix shift.  Raw equality of the two `Option Nat` labels is false; the
  correct equality is relative-label equality, or absolute equality after
  applying `shift` by the next prefix length.

With a post-prefix trace certifying that every observer-touching edit is
either idempotent or one of finitely many same-stage classes with one uniform
positive gain floor, this gives the installed / mark-aligned split needed by
the clock-or-bubble theorem.  The current public types erase both the
historical response and the intervening edit list, and the intended producer
chain has not yet been proved to generate such a coherent trace.  This is a
substantive source-composition obligation, not merely a missing field.

This does not consume the remote-bubble output and does not prove Fin4 UE.

### Traced adjacent-installation theorem

The precise positive statement proved below is the following.  Suppose one is
given, on one common subsequence:

1. actual minimum response endpoints `E_n` which prescribe `Q_(q_n)` for one
   fixed observer `o` and whose `o`-debt tends to zero;
2. exact cap words `W_n` above those literal endpoints, with joint survival
   tending to one;
3. the actual finite post-prefix edit list, including the final
   endpoint-origin edit, producing the source of the next
   `FinFourMinimumResponseEndpointRiseOrigin`; and
4. for every edit in that list which changes `o`, either a proof that the edit
   is idempotent on `Q_(q_n)`, or its retained same-stage gain certificate
   above one common positive floor.

Then, after a further common subsequence if needed, exactly one of the
following is returned:

\[
\boxed{
\begin{array}{ll}
\textbf{mark:}&\text{an actual source-attached positive one-mark edit of }o;\\
\textbf{installed:}&
 |U_o(B_n[o\leftarrow Q_{\widehat q_n}])-U_o(B_n)|\le\xi_n,
 \quad\xi_n\to0,
\end{array}}                                           \tag{T}
\]

where `B_n` is the next endpoint-rise profile and
`hat q_n=shift_(|W_n|)(q_n)`.  In the installed arm, if the next decoded
observer is `o`, the current decoder's outgoing response and vanishing target
debt give the named old/new response switch (3.3).  If its response endpoint
is used as the following literal suffix, the exact transition law is
`incoming_next = shift_(next prefix length)(outgoing)`.

The theorem is a verifier of the supplied trace.  Section 7 explains why the
trace cannot be reconstructed from the older forgetful public records; a
producer must construct it from a non-forgetful composite chronology.

## 1. Exact question and bounded source audit

Fix one observer `o`.  A preceding minimum response rectangle has an actual
response endpoint

\[
 E_n=B_n[o\leftarrow Q_{q_n}],                         \tag{1.1}
\]

where `q_n : Option Nat` includes `Never`, the endpoint debt of `o` tends to
zero, and the joint semantic/law pairs of `E_n` converge to a positive-law
minimum point.  The source-faithful causalization packet uses these literal
`E_n` as its new suffix profiles.

The next producer prefixes `E_n` by an exact cap--Nash word `W_n`, performs a
finite sequence of literal one-date pure-root normalizations in the suffix,
and finally performs the positive endpoint update decoded by
`FinFourMinimumResponseEndpointRiseOrigin`.  The question is whether the old
response is approximately prescribed at that next endpoint-rise profile and
whether the newly decoded response is literally the response carried into
the following source.

The declarations inspected were:

* `FinFourMinimumResponseEndpointRiseOrigin`,
  `FinFourMinimumResponseRectangleSequence`, and
  `nonempty_minimumResponseEndpointRiseOrigin` in
  `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`;
* `FinFourMinimumResponseRectanglePacket`, `endpointResponseProfile`,
  `responseChoice_ge_mark`, `routedStageMass_floor`, `responseSource`, and
  `regeneratedAtLawPoint` in
  `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`;
* `FinFourThreeRoleMinimumTargetRegeneration` in
  `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`;
* `FinFourMinimumAtomChronology` and the owner-compression declarations in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
* the literal tail equalities in
  `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean` and
  `MinimumReturnForcedPair.lean`; and
* the reviewed ordinary-mathematics source-faithful causalization and menu
  transport packet in
  `exports/SOURCE_FAITHFUL_MINIMUM_ENDPOINT_CAUSALIZATION_AND_RESPONSE_MENU_TRANSPORT.md`.

The current `FinFourThreeRoleMinimumTargetRegeneration` itself deliberately
constructs an arbitrary causal chronology from the limiting law and does not
store the incoming endpoint profiles.  Thus the source-faithful wrapper from
the reviewed export, not the older forgetful regeneration record alone, is
essential below.

## 2. Prefix installation is a coupling theorem

Let `E` be an actual suffix profile whose prescribed strategy for `o` is the
pure-time plan `Q_q`.  Let `W` be a finite product-root word.  Put

\[
 P=W*E,
 \qquad \widehat q=\operatorname{shift}_{|W|}(q).        \tag{2.1}
\]

Write

\[
 c(W)=\Pr_W(\text{all players Continue}),\qquad
 c_{-o}(W)=\Pr_W(\text{all opponents of }o\text{ Continue}). \tag{2.2}
\]

If every reward has absolute value at most `R`, couple the prescribed play
of `P` with the deviation `P[o <- Q_hatq]` by using the same opponent actions
in `W`.  On the event on which the prescribed play jointly survives the
word, the deviating play also survives and both enter the same literal
suffix.  They can therefore differ only on prescribed absorption inside the
word, an event of probability `1-c(W)`.

Therefore

\[
 \boxed{
 |U_o(P[o\leftarrow Q_{\widehat q}])-U_o(P)|
 \le 2R(1-c(W)).}                                      \tag{2.3}
\]

The bound is deliberately coarse; its useful feature is that it is uniform
in the suffix and in the response date, including `Never`.

For the source-faithful minimum endpoint construction, exact cap-stack debt
scaling and `D_*>0` give

\[
 c(W_n)\longrightarrow1.                               \tag{2.4}
\]

Joint survival is at most opponent survival, so

\[
 c(W_n)\le c_{-o}(W_n)\le1,
 \qquad c_{-o}(W_n)\longrightarrow1.                   \tag{2.5}
\]

Thus the installation error in (2.3) tends to zero.  Notice the distinction
from response-menu transport: the latter exactly transports a difference of
two counterfactuals.  Equation (2.3) is the additional coupling which compares
one shifted counterfactual to the newly prefixed prescribed profile.

## 3. Suffix edits preserve installation until the first observer touch

The preceding coupling is stable under much more than pure-row
idempotence.

Let `F` be any finite transformation of complete profiles satisfying:

1. every edit of `F` occurs at a date at or after `|W|`;
2. `F` changes only players other than `o`; and
3. the same edits are applied to `P` and to `P[o <- Q_hatq]`.

Then the prefix survival events in (2.2) are unchanged, and on their common
survival event both transformed plays still enter the same suffix profile.
Consequently

\[
 \boxed{
 |U_o(FP[o\leftarrow Q_{\widehat q}])-U_o(FP)|
 \le 2R(1-c(W)).}                                      \tag{3.1}
\]

Here `FP[o <- Q_hatq]` means: apply the non-`o` edits of `F`, then replace
`o` by the shifted pure response.  The operations commute literally because
their player coordinates are distinct.

This covers the exact pure-root normalization, forced-pair construction,
and paid endpoint edit whenever their edited players are not `o`.  Reapplying
the same pure coalition at the retained mark is idempotent and can simply be
deleted from the edit list.

For the last step, the current public endpoint-origin record already gives an
exact two-way split.  Suppose the old response is installed at
`origin.sourceProfile n`.

* If `origin.mover != o` **and** `origin.mark n >= |W_n|`, then
  `endpointProfile_eq_update` and
  `liveRoot_eq_of_ne` show that the same non-`o` marked edit is applied to the
  prescribed source and the old-response counterfactual.  Hence (3.1) holds
  at `origin.endpointProfile n` with exactly the same error.
* If `origin.mover = o`, then `moverGain_floor` is a uniformly positive actual
  gain by `o`, and `endpointProfile_eq_literalPureRoot` together with
  `liveRoot_eq_of_ne` identifies it as a one-mark modification with the
  game-relevant live roots unchanged away from the mark.  This is the
  mark-aligned output.

Thus no extra analytic branch occurs inside
`FinFourMinimumResponseEndpointRiseOrigin`.  The missing trace is entirely
in the route from the preceding response endpoint to the *source* of that
origin.

Now allow a finite list of one-date edits and stop at the first
non-idempotent edit of player `o`.  There are exactly two alternatives.

### Preserved installation

No such edit occurs before the next endpoint-rise profile `B_n`.  Then (3.1)
gives

\[
 |U_o(B_n[o\leftarrow Q_{\widehat q_n}])-U_o(B_n)|
 \le\xi_n,
 \qquad \xi_n\to0.                                    \tag{3.2}
\]

If `o` is the observer in the next
`FinFourMinimumResponseRectangleSequence`, its decoded response `q_n^+`
has response-endpoint debt `epsilon_n -> 0`.  The installed-response identity
from the response-switch note then gives the named seam

\[
 U_o(B_n[o\leftarrow Q_{q_n^+}])
 -U_o(B_n[o\leftarrow Q_{\widehat q_n}])
 \ge \kappa-\epsilon_n-\xi_n,                         \tag{3.3}
\]

where `kappa` is the fixed endpoint debt-rise floor.  This is the desired
old-label/new-label response switch, not an anonymous paid row.

### Mark-aligned observer modification

The first non-idempotent `o`-edit occurs at the retained marked date.  The
profile immediately before the edit and the profile immediately after it
have identical pre-mark history and identical post-mark live-root tail, and
their `o` strategies differ at that one Boolean endpoint.  If the trace
records the edit's existing positive gain certificate, this is exactly a
source-attached same-stage modification and enters the checked Fin4 screened
endpoint consumer.  It should be returned directly; attempting to continue
the response-installation proof across it would throw away stronger data.

In the intended producer chain every genuine observer touch has one of the
following explanations.

* Purifying a positive terminal row is idempotent on `o`: because `o` already
  uses a pure time, positive mass of coalition `C` at the selected date says
  that `o`'s pure action there is exactly membership in `C`.
* Owner compression at a singleton owned by `o` is idempotent when the
  supplied suffix already prescribes a pure time for `o`: positive singleton
  mass at the selected date forces that date to be the pure stopping date.
* If `o` is the forced outsider at the singleton row, the hard terminal-gap
  inequality is the positive same-stage join certificate.
* If `o` is selected by pure nonsingleton screening or as the paid endpoint
  mover, that selection already carries a positive same-stage endpoint-gain
  certificate.

Thus a trace of the constructors makes the two alternatives above exhaustive.
The currently public flattened packets retain their endpoints and tails but
do not retain this complete constructor trace.

The status of the ingredients is deliberately separated:

| fact | available from current public fields? |
|---|---|
| last origin edit is `mover != o` or a paid mark edit | yes: `endpointProfile_eq_update`, `liveRoot_eq_of_ne`, `moverGain_floor` |
| old response is literally the regenerated suffix strategy | only in the source-faithful wrapper; not in the old regeneration record |
| pureification is idempotent on `o` | follows from the supplied pure response and positive selected-row mass, but those facts are not co-packaged publicly |
| forced-outsider / screening observer touch is paid | yes in its local constructor, but the flattened next origin does not retain which constructor touched `o` |
| raw outgoing clock equals next incoming clock | no; false without the shift in (5.2) |

## 4. A zero-debt payer exclusion, when the source limit is retained

There is a useful way to eliminate an apparent extra branch.  Suppose actual
profiles `A_n` converge semantically to a minimum point `z`,

\[
 d_o(z)=0,                                             \tag{4.1}
\]

and a same-stage update of one fixed player `p` has whole-profile gain at
least `g>0` at every `A_n`.  Since changing `p`'s own prescribed strategy
does not change its unrestricted cap,

\[
 d_p(A_n)\ge g.                                        \tag{4.2}
\]

If `p=o`, continuity of semantic debt and (4.1) contradict (4.2).  Hence

\[
 \boxed{p\ne o}                                       \tag{4.3}

\]

Equivalently, if the producer stores only a conditional root-defect floor
`delta>0` but also stores a live/stage-mass floor `lambda>0`, the literal
global gain is at least `lambda*delta`, and the same conclusion follows.

This is exactly the promised use of positive-minimum provenance: a fixed
positive payer at a retained minimum source cannot be one of the coordinates
already certified to have zero debt there.  It proves automatic preservation
through the last paid endpoint edit whenever the source convergence and the
old zero are carried on the same subsequence.

The qualifier is essential.  The current
`FinFourMinimumResponseEndpointRiseOrigin` stores convergence of its
`endpointProfile`, not convergence of its `sourceProfile` to a named old-zero
minimum point.  Therefore (4.3) cannot be invoked from that record alone.

## 5. The outgoing label closes only after an exact clock shift

Let the newly decoded response be the suffix-relative pure time `q_n^+`, and
let its actual response endpoint be

\[
 D_n=B_n[o\leftarrow Q_{q_n^+}].                       \tag{5.1}

\]

Source-faithful regeneration uses the literal `D_n` as the next suffix.  If
the next cap word has length `L_n`, the response literally prescribed after
the new prefix is

\[
 \boxed{q_{n,\mathrm{in}}^{\mathrm{next}}
   =\operatorname{shift}_{L_n}(q_n^+).}                \tag{5.2}

\]

For finite `q`, `shift_L(q)=L+q`; `Never` is fixed by `shift`.  Equation
(5.2) is definitional once the source-faithful chronology and its root word
are retained.  It remains true through every later edit which does not touch
`o`; the first edit which does touch `o` is precisely the mark-aligned arm of
Section 3.

Raw equality

\[
 q_{n,\mathrm{in}}^{\mathrm{next}}=q_n^+              \tag{5.3}

is false whenever `L_n>0` and `q_n^+` is finite.  Even one literal
all-Continue prefix shifts `QuitAt q` to `QuitAt(q+1)`.  It preserves payoff,
cap, debt, and terminal law, but not the calendar label.  The iterated
clock-or-bubble packet must therefore store either:

* a suffix-relative response label together with a prefix offset; or
* an absolute label and the transition equality (5.2).

With this correction, outgoing-to-next-incoming closure is exact.  Without
it, the requested literal `Option Nat` equality is not merely absent from the
API; it is mathematically wrong.

## 6. Fixed-observer recurrence

Consider a finite or infinite chain of minimum response endpoints.  At each
step the selected observer is killed at its response endpoint.  Carry every
installed response through the next source-faithful chronology using (5.2).
For any previously killed observer `o`, one of the following happens before
its next selected occurrence:

1. an intervening edit first touches `o`, giving the mark-aligned arm;
2. no edit touches `o`, so (3.2) installs its named response at the next
   profile where its debt is tested; or
3. the public object forgets the relevant edit/shift trace, giving the typed
   obstruction below.

If all earlier zero debts were preserved, four successive Fin4 kills would
make all debts zero, contradicting `D_*>0`.  Hence a selected observer must
eventually repeat, or an earlier observer must be touched/reactivated.  Finite
pigeonhole then fixes one observer along any infinite recurrence.  In the
preserved arm (3.3) supplies the exact named response seam; in the touched arm
the same-stage consumer fires.  Iterating the clock-order split of the
response-switch note then yields either a concentrated singleton or its
quantitative remote-bubble/all-Never packet.

This paragraph is a consumer of a **source-closed traced chain**.  It is not
a claim that the present atlas already constructs such a chain.

## 7. Exact public-interface verdict

The current public structures are insufficient to state, let alone prove,
the adapter above.

`FinFourMinimumResponseEndpointRiseOrigin` stores only the current source and
endpoint profiles, current mover/observer, current mark, and the current
positive rise.  It contains no field for:

* the preceding response choice;
* the source-faithful chronology identifying the current suffix with the
  preceding response endpoints;
* the cap-word shift turning the preceding relative clock into the current
  absolute clock;
* the intervening same-date edit trace; or
* convergence of the current source profiles to the preceding old-zero
  minimum point.

Likewise, `FinFourThreeRoleMinimumTargetRegeneration` stores equality of the
new point and terminal but deliberately reselects its chronology.  Two
histories with different old response labels therefore have the same value
of these forgetful public structures.  No theorem whose input is only those
structures can return an outgoing-to-incoming label equality involving the
erased label.

The honest finite output is consequently

\[
\boxed{
\begin{array}{l}
\textsf{InstalledAtNextEndpoint}(o,q^-,q^+,\xi_n\to0)\\
\qquad\lor\ \textsf{PaidMarkAlignedObserverEdit}(o,t,\text{same tail})\\
\qquad\lor\ \textsf{MissingAdjacentResponseTrace}.
\end{array}}                                           \tag{7.1}
\]

The third constructor is not a new mathematical leaf.  It names the exact
data erased by the present adapter and should disappear once the source-
faithful chronology and constructor trace are packaged together.

A minimal Lean-facing wrapper would have the shape

```text
FinFourAdjacentResponseInstallationTrace where
  previousObserver : Fin 4
  previousResponse : Nat -> Option Nat
  previousResponseEndpoint : Nat -> BehaviorProfile
  nextChronology : FinFourMinimumAtomChronology nextSource
  suffixProfile_eq_previousEndpoint : ...
  prefixLength : Nat -> Nat
  incomingResponse_eq_shift : ...
  edits : Nat -> List SourceAttachedOneDateEdit
  edit_date_ge_prefixLength : ...
  paidGainFloor : Real
  paidGainFloor_pos : 0 < paidGainFloor
  editTraceOutcome :
    (all edits avoid previousObserver or are idempotent) or
    (first previousObserver edit is at the retained mark and has gain at
      least paidGainFloor)
  nextOrigin : FinFourMinimumResponseEndpointRiseOrigin nextSource
  nextOrigin_mark_ge_prefixLength : ...
  nextOrigin_sourceProfile_eq_apply_edits : ...
```

Its capstone should return the first two constructors of (7.1); the third is
only the verdict for the current forgetful API.

## 8. Nonclaims

This note does not:

* infer raw equality of response dates across a newly inserted prefix;
* infer source convergence from endpoint convergence in the current origin;
* treat literal response availability as response optimality;
* consume an uncertified observer edit;
* orient the remote bubble;
* prove that the current flattened Fin4 atlas retains the needed edit trace;
  or
* prove a uniform-equilibrium payoff.

## 9. Conclusion

The analytic installation estimate is available and survives every
source-faithful suffix edit until the first observer touch.  The observer
touch is not a mysterious cap leak: in the intended constructors it is
either idempotent or an already source-attached paid same-stage modification.
The outgoing response then closes to the next incoming label by the exact
prefix-shift identity (5.2), not by raw numeric equality.

Accordingly, the adjacent response-switch programme is blocked at a
dependent source-composition theorem.  The required result is not another
paid-row estimate: it must construct, rather than assume, one coherent
post-prefix edit trace with a uniform paid-touch floor from the
source-faithful endpoint chronology through the singleton/pure-row
normalizations into the next `FinFourMinimumResponseEndpointRiseOrigin`.
