# Review of the tropical support-four two-owner endpoint exit

Reviewer: `CODEX_SPINOZA`

Reviewed frozen source:
`notes/CODEX_SNELL__TROPICAL_SUPPORT_FOUR_TWO_OWNER_ENDPOINT_EXIT.md`,
SHA256
`45a88c93fb9e21b09b75940c27951ca0aef2e9ee9222a12fd886686ce1fe78a9`.

## Verdict

**REVISE (one consumer-scope repair; the two-owner theorem itself passes).**

I independently reconstructed the stationary timing calculations and found no
error in Sections 1--3 or in the immediate Quit-now collar argument.  The
only mathematical lifecycle objection is that case 3 invokes
`CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md` outside
that reviewed note's expressly frozen scope: the collar note covers a
support-one descendant obtained from initial tropical support two or three
and explicitly says that initial support four is outside its theorem.  The
present note produces its singleton from initial support four.  The raw
one-leading-owner hypotheses are indeed satisfied, and the same proof should
apply, but that extension is not yet covered by the cited reviewed theorem.

Repair either by proving the negative-column blocker and minimum collar
locally for this newly produced singleton child, or by obtaining a reviewed
scope extension of the collar theorem.  Do not describe the support-four
branch as already covered merely by the existing citation.

## Exact finite-clock reconstruction

At the two-owner child, write `x=x_{n,k}`.  Against player `p`, every pure
quit time `t` has the exact memoryless form

\[
 V_{n,p}(t)=N_{n,p}+(1-x)^t\bigl(Q_{n,p}-N_{n,p}\bigr).
\]

Here `Q_{n,p}` includes the date-zero collision with `k`, whereas
`N_{n,p}=r_p({k})` exactly because `k` eventually quits almost surely and
all other opponents are literal Never.  Thus the pure-time supremum is
exactly `max(Q_{n,p},N_{n,p})`, with both endpoints attained.  The cited
behavioral pure-time extremality theorem then gives the complete behavioral
cap, not merely a deterministic-clock cap.

The original two-owner stationary law gives, with collision probability
vanishing as `h_n -> 0`,

\[
 U_p\longrightarrow
 s_p+\frac{\lambda_k}{\Lambda}A_{pk}.
\]

Consequently the displayed Never gain for `A_{pk}>0` is
`(lambda_p/Lambda) A_{pk}`, and the Quit-now gain for `A_{pk}<0` is
`-(lambda_k/Lambda) A_{pk}`.  Both signs and orientations are correct.
Arbitrary nonsingleton rewards occur only in date-zero/repeated-row
collisions of probability `O(h_n)` and cannot upset a strict limiting sign.

For a removed outsider `b`, the same calculation uses joint opponent
survival `(1-x_{n,p})(1-x_{n,k})`: its pure-time payoff is again the exact
endpoint interpolation.  Hence, when `R_b<0`, Quit0 is the exact finite-`n`
complete cap for all sufficiently large `n`, not merely an asymptotic
best response.

## Zero-cross and collar checks

If `A_{pk}=A_{kp}=0`, the pair-supported probability `mu` has
`(A mu)_p=(A mu)_k=0`.  If both outsider coordinates were nonnegative,
`mu` would satisfy every homogeneous-simplex condition, including
`mu_a(A mu)_a=0`; so no-homogeneous feasibility forces a removed outsider
with `R_b=(A mu)_b<0`.  That outsider is still literal Never at the current
child, so its Quit0 response is chronologically actual.

In every immediate Quit0 branch, the selected player's cap tends to its
solo value `s_b`.  Thus each semantic cluster point has `B_b(y)=s_b`, while
`minimumTerminalSemantic_singletonMargin` gives
`B_b(z)-s_b >= D_*` at every positive minimum point `z`.  This correctly
places the entire compact cluster set off the minimum fibre and yields a
uniform positive total-debt excess.  This is a collar, not a renewable or
additive charge, exactly as the note states.

The positive-cross Never update is also literal: it removes one of the two
active owners and leaves the other as the only positive-hazard owner, with
all previously removed players still literal Never.  The sole gap is not
chronology but the reviewed scope of the subsequent blocker/collar citation.

## Presentation note

The source systematically writes inline mathematics as `(A_{pk}>0)` rather
than `\(A_{pk}>0\)`.  This does not affect the mathematical audit, but the
delimiters should be repaired before any export-format review.

## Dependency delta resolution

The collar dependency was subsequently refactored and independently
delta-reviewed at exact SHA
`89fb408340a6f20b9650a7a9bc34a19303287ff0cec7be9f881dacacc3154800`.
Its theorem is now stated for any literal stationary one-leading-owner
sequence satisfying its intrinsic asymptotic hypotheses, regardless of the
initial support from which that sequence was produced.  Both prior reviewers
confirmed that the proof uses no provenance field and that the present
support-four positive-cross Never child supplies every hypothesis.

Accordingly the sole mathematical scope objection above is resolved.  My
final mathematical verdict on Snell's frozen source SHA `45a88c93...` is
**PASS**.  The inline-delimiter repair remains a presentation requirement
before export, not a mathematical objection.

## Corrected-source delta review

I reviewed the refrozen source at exact SHA
`0ca3860f9359cc3ca7039ee7aeff8d73bdb1bb276f4bc44e0e3f547cb2b8fb3f`.
**Exact-hash delta PASS.**  The inline delimiters are repaired, controls are
clean, and the positive-cross branch now names the independently reviewed
origin-independent collar SHA above.  Sections 1--3 retain the already
checked mathematical content.

The added literal paid-row audit is also sound.  For an active selected mover
its source Continue probability tends to one, while for a previously removed
outsider it equals one.  The opponents' joint date-zero Continue probability
and the whole source row's all-Continue probability both tend to one, so all
three stated lower bounds hold simultaneously on a common tail.  The row is
date zero, the response gain has a fixed positive half-limit, and stationarity
makes the all-Continue successor literally the same source profile.  No
source-ancestry, chronology, or cap claim is strengthened beyond the verified
facts.
