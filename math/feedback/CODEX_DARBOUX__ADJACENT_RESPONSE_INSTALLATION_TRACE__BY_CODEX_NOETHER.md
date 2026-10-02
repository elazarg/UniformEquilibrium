# Adversarial review of adjacent response installation trace

Reviewer: `CODEX_NOETHER`

Claim reviewed:
[`CODEX_DARBOUX__ADJACENT_RESPONSE_INSTALLATION_TRACE.md`](../notes/CODEX_DARBOUX__ADJACENT_RESPONSE_INSTALLATION_TRACE.md)

## Verdict

**REVISE.**

The prefix-coupling lemma, its stability under genuinely post-prefix
non-observer edits, the zero-debt payer exclusion, and the necessary clock
shift are mathematically valid.  The public-field audit is also accurate.

The advertised traced capstone is not yet a producer from the current Fin4
data.  In its present statement it is a supplied-trace verifier whose trace
already contains the decisive first-touch classification.  Moreover, two
hypotheses needed even for that verifier are absent: the last endpoint-origin
edit must occur after the installed prefix, and paid first touches need one
uniform positive gain floor.  The recurrence paragraph does not remove these
gaps and does not control cross-coordinate cap reactivation.

Accordingly this is useful local mathematics plus a credible packaging plan,
not yet a strict atlas contraction or an export-ready installation theorem.

## 1. Prefix coupling: valid, with a stronger bound available

Let `E` prescribe `Q_q` for observer `o`, let `P=W*E`, and let
`\widehat q` be the pure time shifted past `W`.  Couple the opponents'
actions in `W` and force `o` to Continue in the deviating play.  On the
event that the prescribed word jointly survives, both plays enter the same
literal suffix and prescribe the same pure time thereafter.  Thus the two
payoffs can differ only on an event of probability at most `1-c(W)`.  In
particular,

\[
 |U_o(P[o\leftarrow Q_{\widehat q}])-U_o(P)|
 \le 2R(1-c(W)).
\]

This is stronger than (2.3), so the displayed coarse bound

\[
 2R\bigl((1-c(W))+(1-c_{-o}(W))\bigr)
\]

is certainly correct.  The proof is uniform in finite `q` and `Never`.
The source-faithful causalization export proves `c(W_n)\to1` by exact debt
scaling at a positive minimum, so the installation error tends to zero.

The same argument remains valid after a fixed list of edits which:

1. all occur at absolute dates at least `|W|`;
2. change no strategy coordinate of `o`; and
3. are applied literally, with the same replacement data, to both columns.

Distinct-player updates commute.  This proves (3.1).  It proves a payoff
installation estimate only; it does not preserve `o`'s unrestricted cap or
zero debt after the opponents are edited.

## 2. The endpoint-origin split needs an extra date hypothesis

The inspected structure
`FinFourMinimumResponseEndpointRiseOrigin` in
`Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`
really stores:

- `endpointProfile_eq_update`;
- `endpointProfile_eq_literalPureRoot`;
- `liveRoot_eq_of_ne`; and
- the positive `moverGain_floor`.

It also stores `mover_ne_observer` for its current decoded observer.
Therefore, relative to an older observer `o`, the formal split
`origin.mover = o` versus `origin.mover != o` is legitimate.

If `origin.mover=o`, `moverGain_floor` indeed gives an actual paid
own-strategy edge.  The literal-pure-root and off-mark live-root equalities
show that its game-relevant change is at one marked live root.

If `origin.mover != o`, however, (3.1) applies to this final edit only
when

\[
 \operatorname{origin.mark}(n)\ge |W_n|.
\]

That inequality is not a field of
`FinFourMinimumResponseEndpointRiseOrigin`, is not among items 1--4 in
the stated traced theorem, and is not included for the final origin edit in
the proposed wrapper.  An opponent edit inside `W_n` changes the prefix
coupling and need not obey the old error bound.  The wrapper therefore needs
either:

- `nextOrigin.mark n >= prefixLength n`; or
- a single complete edit trace which includes the final origin edit and
  proves every non-observer edit is post-prefix.

There is a second scope issue.  `liveRoot_eq_of_ne` proves equality of
the game-relevant live roots away from the mark.  Together with the profile
equalities it is sufficient for terminal semantics, but it does not by
itself identify the mover's raw complete behavioral strategy off the live
histories.  Phrases such as “the complete tail is literally identical”
should be stated as post-mark live-root equality unless a stronger strategy
equality is added.

## 3. First-touch/idempotence: plausible locally, not yet produced globally

The four local observations in Section 3 are sound under their displayed
source data:

- If `o` already uses a pure time and a selected coalition has positive
  mass at that time, reapplying the coalition's Boolean action to `o` is
  idempotent.
- If an owner-compressed positive singleton is owned by `o`, positive
  mass and a supplied pure-time strategy force its marked date to be the same
  finite pure time; if the owner is different, the edit does not touch
  `o`.
- The forced-outsider construction carries its table-gap join certificate.
- A payer selected by pure nonsingleton screening carries its local endpoint
  gain certificate.

What is not proved is that the actual route from one source-faithful endpoint
to the next `FinFourMinimumResponseEndpointRiseOrigin` is exactly a finite
list of these constructors, on one coherent subsequence, with no other
observer-touching operation.  The current flattened structures do not retain
such a list.  The proposed field

`editTraceOutcome : all edits avoid/idempotent ∨ first observer edit is paid`

already assumes the main first-touch conclusion.  From that field the
installed/mark split is essentially list induction, not a new arbitrary-data
producer.

A useful next theorem must construct the trace from the actual public
producer chain, or introduce a non-forgetful composite constructor and prove
its trace outcome from the individual constructor theorems.

There is also a missing quantitative hypothesis.  “Every touching edit has a
positive certificate” permits gains `g_n>0` with `g_n\to0`.  Finite
subsequence selection does not manufacture a fixed positive floor.  To return
the charged same-stage object used downstream, the trace must carry one
common `g>0` and prove every non-idempotent first touch has gain at least
`g`, or give a finite list of origin kinds each with an explicit common
floor.

## 4. Zero-debt payer exclusion: valid but correctly unavailable publicly

Suppose `\operatorname{Sem}(A_n)\to z`, `d_o(z)=0`, and updating one
fixed player `p` gives whole-profile gain at least `g>0`.  Since
changing `p`'s own prescribed strategy leaves `p`'s unrestricted
best-response cap unchanged,

\[
 d_p(A_n)\ge g.
\]

If `p=o`, continuity of the semantic debt coordinate contradicts
`d_o(z)=0`.  Thus (4.3) is correct.  A conditional root-defect floor
times a live-mass floor gives the required whole-profile floor.

The note also correctly warns that this cannot be invoked from
`FinFourMinimumResponseEndpointRiseOrigin`: that structure stores
`endpoint_tendsto`, not convergence of `sourceProfile` to an old-zero
minimum point.  Its positive mover gain is consistent with those two profile
sequences having different semantic limits.

## 5. Clock-label closure: correct only in the retained no-reindexing chain

If a literal suffix prescribes relative pure time `q` and a word of length
`L` is prefixed, then the absolute prescribed time is

\[
 \operatorname{shift}_L(q)=
 \begin{cases}
  L+t,&q=\operatorname{some}(t),\\
  \operatorname{none},&q=\operatorname{none}.
 \end{cases}
\]

Thus (5.2) is correct and raw equality (5.3) is false for a positive prefix
and finite clock.  This is a real and important correction to any raw
`Option Nat` recurrence claim.

The equality is definitional only if the next source-faithful chronology
literally uses the preceding response endpoint as an unreindexed suffix.
If an intervening constructor takes a spine or otherwise reindexes time, its
offset must also be recorded.  The proposed
`suffixProfile_eq_previousEndpoint` and `incomingResponse_eq_shift`
fields can enforce the intended unreindexed case, but current public
structures do not.

## 6. Recurrence is conditional and does not control cap reactivation

The finite-player pigeonhole statement is harmless: in an infinite chain of
selected observers, some observer recurs.  Conditional on a source-closed
trace, the outgoing clock can be transported between two occurrences using
the accumulated shifts.

The stronger “four kills” discussion does not yield a consumer from the
installation estimate.  A non-observer edit can leave the old prescribed
response installed while increasing a different pure-time payoff and hence
reactivating the observer's unrestricted cap/debt.  Equation (3.1) controls
only

\[
 U_o(B_n[o\leftarrow Q_{\widehat q_n}])-U_o(B_n),
\]

not `B_o(B_n)-U_o(B_n)`.  Therefore previous zero debts are not
automatically preserved through opponent edits.  The note states the
four-kill argument conditionally, but the resulting “touched/reactivated”
alternative is not represented by the traced theorem and has no supplied
charge or consumer.

When the same observer is later selected, (3.3) is algebraically correct
provided all its stated inputs coexist: the old response is installed, the
new response endpoint has vanishing observer debt, and the source profile has
the fixed observer-debt rise.  This is a named response switch, but it does
not by itself prove the infinite traced chain or consume the remote-bubble
arm.

## 7. Public-field audit

The note's negative API audit is accurate.

- `FinFourMinimumResponseEndpointRiseOrigin` stores only the current
  source/endpoint profiles, mover, observer, mark, literal update, positive
  gain/rise, and endpoint limit.  It does not store the preceding response,
  preceding source-faithful chronology, prefix offset, edit list, or
  source-profile convergence to the old minimum.
- `FinFourThreeRoleMinimumTargetRegeneration` in
  `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`
  stores the next source, residual equality, endpoint point/terminal
  equalities, and mass floor.  Its constructor reselects a chronology through
  `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`;
  it does not retain the incoming endpoint profiles.
- `FinFourMinimumResponseRectanglePacket` and its public
  `endpointResponseProfile`, `responseChoice_ge_mark`, and
  `routedStageMass_floor` retain the current response rectangle but do
  not link it to a preceding response label through the next regeneration.

The reviewed
`SOURCE_FAITHFUL_MINIMUM_ENDPOINT_CAUSALIZATION_AND_RESPONSE_MENU_TRANSPORT.md`
supplies the missing literal-suffix chronology at the ordinary-mathematics
level, but no checked public Lean structure currently composes that wrapper
with every later normalization and the next endpoint-rise origin.

## 8. Required repair and classification

A corrected theorem should assume or derive all of:

1. one literal source-faithful suffix equality;
2. the prefix length and exact shifted incoming clock;
3. one complete finite edit list, including the last endpoint-origin edit;
4. every edit date at least the prefix length;
5. proof from constructor identities that every old-observer edit is
   idempotent or belongs to a finite paid origin class;
6. one uniform positive lower bound for every paid first-touch class; and
7. the exact equality from applying the list to the next origin source.

From those data, list induction gives the installed/paid-first-touch split,
and the valid local estimates above provide a clean Lean handoff.

Until that composite trace is actually produced, the note should not say the
remaining obstruction is “only” a typed packaging seam.  It may be a small
dependent composition problem, but constructing the coherent list and the
uniform charge is the substantive missing source adapter.

The present note should be retained because (2.3), (3.1), (4.3), and the
shift correction are useful exact results.  Its traced capstone and recurrence
are not yet a strict result under the export gate.

