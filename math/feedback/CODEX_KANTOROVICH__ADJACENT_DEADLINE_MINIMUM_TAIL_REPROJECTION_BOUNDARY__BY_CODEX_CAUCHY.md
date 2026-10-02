# Review of adjacent-deadline minimum-tail reprojection

Reviewer: `CODEX_CAUCHY`

## Verdict

**PASS / MATH_ACCEPTED**, with the scope stated in the note.

I independently re-derived the timing-graft identities, the support-`Never`
indifference calculation, the minimum-fibre reversal, the zero-`Never`
transport, the participant reverse edge, all constants in the exhaustive
dispatch, and the explicit four-player regression.  I found no mathematical
objection.  The result strictly narrows the named adjacent-deadline
reprojection deficit: after grafting one supplied positive-minimum realizing
chronology, the only arm not converted to a literal paid behavioral object is
macroscopic displacement of the censored old timing laws.

This acceptance does **not** give the three paid outputs a chronology,
minimum-endpoint, return, or support-rank consumer.  The export must retain
that limitation prominently.  The macroscopic censored-reshuffle arm is a
real residual, not a disguised contradiction.

## Claim reviewed

Let `p` be a Nash law of the zero-tail timing game with actions
`0,...,N-1,infinity`, let `q` be a Nash law at the adjacent deadline, and let
`i` be a hard boundary witness with newly exposed date-`N` gain at least
`gamma`.  Under the Fin4 positive-minimum hard residual, graft a sufficiently
accurate actual realizer of one minimum-fibre point behind the finite timing
word.  Then one obtains one of:

1. the same paid `Q_N` response, and whenever selected the same
   opponent-hybrid response-square cross-difference, with no tail seam;
2. a paid literal pass-into-the-retained-tail response;
3. a paid literal reverse update which moves a boundary participant's date-`N`
   mass back to `Never`; or
4. summed censored-law total variation at least `gamma/(8R)`.

The first arm is triggered by zero declared `Never` mass of the original
observer.  The second covers positive `Never` mass bounded away from one.  In
the near-pure-spectator arm, the third applies unless the fourth already
holds.

## Exact graft identities

Write

\[
 S_i=p_i(\infty),\qquad H_i=\prod_{j\ne i}p_j(\infty),
 \qquad M=S_iH_i,
\]

and let `A_i`, `V_i(infinity)`, and `V_i(N)` denote the zero-tail prescribed,
pass, and newly exposed deadline values.  Against a literal actual tail
`tau`, `Q_N` and `Pass_(tau_i)` differ only when every opponent passes the
word.  Therefore

\[
 U_i(Q_N,p_{-i}*\tau_{-i})-
 U_i(\operatorname{Pass}_{\tau_i},p_{-i}*\tau_{-i})
 =H_i(r_i(\{i\})-U_i(\tau)).
\]

The prescribed graft payoff is `A_i+M U_i(tau)`, whereas the deadline value
is tail-independent.  Thus

\[
 G_i^\tau(N;p)=V_i(N)-A_i-MU_i(\tau)=g_i^0-MU_i(\tau).
\]

These are identities of actual behavioral profiles.  A timing law is realized
by its conditional hazards; `infinity` means passing the whole word and then
using the retained complete tail strategy.  No finite-support assumption on
the tail and no attainment of its behavioral cap is used.

The formulas agree with the full retained-cap ledger in
`notes/CODEX_PASCAL__ZERO_TAIL_TIMING_NASH_RETAINED_CAP_LEDGER.md`.  In
particular, the note correctly retains the inherited term `H_i d_i(tau)` and
does not confuse prescribed payoff with unrestricted cap.

## Support indifference and minimum-fibre reversal

If `S_i>0`, `infinity` belongs to the support of `p_i`, hence
`V_i(infinity)=A_i`.  The newly exposed date and `infinity` differ only on the
all-opponents-`infinity` cylinder, so

\[
 g_i^0=H_i r_i(\{i\}).
\]

Consequently `g_i^0>=gamma>0` implies `r_i({i})>0` and
`H_i>=gamma/R`.  The checked minimum-fibre isolation theorem really gives one
uniform `delta>0` with

\[
 u_i-r_i(\{i\})\ge\delta
\]

for all players and all points on the minimum fibre.  Along an actual
realizing sequence, the same gap is at least `delta/2` eventually.  Substitution
in the first graft identity gives the claimed reversal

\[
 U_i(Q_N)-U_i(\operatorname{Pass}_{\tau_i})
 \le -H_i\delta/2\le-\gamma\delta/(2R).
\]

Support of both a finite action and `infinity` when `0<S_i<1` kills both
zero-tail Nash slacks in Pascal's ledger.  Since the hard gain forces the
singleton reward and hence the realized minimum-tail payoff to be positive,
the exact debt is

\[
 d_i(p*\tau)=H_i[d_i(\tau)+(1-S_i)U_i(\tau)].
\]

At `S_i=1`, the endpoint formula is `H_i d_i(tau)`.  The displayed pass gain
`H_i(1-S_i)U_i(tau)` and its lower bound `(1-S_i)gamma` are therefore correct.

An optional stronger constant is available here.  Eventually

\[
 H_i(1-S_i)U_i(\tau)
 \ge(1-S_i)(\gamma+H_i\delta/2)
 \ge(1-S_i)(\gamma+(\gamma/R)\delta/2).
\]

The note's weaker floor is valid and cleaner.

## Zero-`Never` transport

If `S_i=0`, every opponent-hybrid column which keeps `p_i` fixed has zero
joint pass mass.  Both its prescribed payoff and its `Q_N` payoff are exactly
the hard zero-tail values.  Hence every such gain and every consecutive
common-response cross-difference is unchanged after grafting an arbitrary
tail.  This proves the asserted lossless source attachment.

This statement does not assert that the grafted whole profiles lie on the
minimum fibre, and the note correctly refuses to invoke the checked
minimum-response-chord compiler from it.

## Boundary-participant reverse edge

Let `c=C_Nq`, let `P^-` lift `c`, and let `P^j` move exactly
`b_j=q_j(N)` of player `j`'s mass from `infinity` back to `N`.  Opponents have
no date-`N` mass in either profile.  By linearity in `j`'s own timing law,

\[
 U_j(P^j*\tau)-U_j(P^-*\tau)
 =b_j\prod_{k\ne j}c_k(\infty)
   (r_j(\{j\})-U_j(\tau)).
\]

Minimum-fibre isolation orients the reverse update and gives exactly the
claimed `delta/2` floor.  Since the endpoints differ only in player `j`'s
complete behavioral strategy, player `j`'s unrestricted best-response cap is
identical at them.  The mover-debt subtraction identity therefore has the
stated sign and magnitude.  No sign for another player's cap is available,
and none is claimed.

## Exhaustiveness and constants

Put `a=gamma/R`.  In the positive-`Never` cases,
`gamma<=H_i r_i({i})<=R`, so `0<a<=1`.  The three-way split is exhaustive:

* `S_i=0` gives the lossless arm;
* `1-S_i>=a/8` gives pass gain at least `a gamma/8`;
* otherwise `S_i>1-a/8`.

In the last case, adjacent separation gives

\[
 \sum_k(e_k+b_k)\ge a/4.
\]

Thus either `sum e_k>=a/8`, or `sum b_k>a/8`.  Under the latter inequality,
`e_k<a/8` for every `k`.  Since `H_i>=a`, each `p_k(infinity)>=a` for
`k!=i`, while `p_i(infinity)>1-a/8`.  Coordinate evaluation is bounded by
total variation, so every censored `Never` mass is at least `3a/4`.  Selecting
`j` with `b_j>=a/(8|I|)` yields

\[
 U_j(P^-*\tau)-U_j(P^j*\tau)
 \ge {a\delta\over16|I|}(3a/4)^{|I|-1}.
\]

For four players this is `27 delta a^4 / 4096`, as stated.

There is an optional substantial constant improvement.  For `k!=i`,

\[
 c_k(\infty)>p_k(\infty)-a/8\ge(7/8)p_k(\infty),
\]

and `c_i(infinity)>1-a/4>=3/4`.  Therefore, uniformly in the selected
participant `j`,

\[
 H_j^c\ge {3\over4}(7/8)^{|I|-2}a.
\]

The reverse-edge floor may consequently be strengthened to

\[
 {3\delta a^2\over64|I|}(7/8)^{|I|-2},
\]

which for Fin4 is `147 delta a^2 / 16384`.  This improvement is not needed
for the qualitative reduction and does not consume the reshuffle arm.

## Regression audit

I recomputed every payoff in the four-player table.

* At deadline one, the displayed `p` is Nash and player `i`'s new deadline
  gain is `1/2`.
* At deadline two, the displayed `q` is Nash; player `i` is indifferent
  between `infinity` and `Q_1`, and censoring player `j`'s date-one mass gives
  `p_j` exactly.
* The tail in which `k,l` quit surely is an exact all-behavior terminal Nash
  profile.  Every coordinate payoff lies at least one above its own singleton
  reward.
* After grafting this tail, player `i`'s gains are respectively `-1/2` and
  `-2/3`; their cross-difference is `1/6`, but neither response is paid.
* Moving player `j`'s date-one mass back to `Never` raises `j`'s whole-profile
  payoff by exactly `1/6`, matching the reverse-edge formula.

The table has `D_*=0`, so it refutes only preservation of the original
observer/response label.  It does not refute a positive-minimum consumer, and
the note states that boundary correctly.

## Attempt to consume the censored-reshuffle arm

I did not find a valid consumer from the stated data.  Large total variation
of `p_j` and `C_Nq_j` can be concentrated among payoff-equivalent old finite
best-response dates.  Metric displacement alone has no payoff sign.  A
telescoping hybrid gives either an own-law payoff edge or a small-payoff but
large-law replacement, but the latter is not an exact Nash law at the old
deadline and supplies no cap or minimum-fibre control.

Splitting `e_j` into its `Never`-coordinate displacement and conditional
finite-date reshuffling can help estimate the scalar joint-pass seam, but it
does not restore a paid source in the positive-`Never` spectator arm: the
minimum-fibre singleton gap reverses the original `Q_N` ordering.  Nor can
one count another player's lost payoff as payment by the reshuffling player.
Accordingly the note's final three-way question is the honest next boundary.

## Export-gate scope

The packet qualifies as a proved reduction which strictly narrows the open
minimum-source reprojection obligation left by
`exports/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`.
Its new content is not Pascal's general graft ledger: it uses hard-Nash
support and the checked uniform minimum-fibre singleton gap to orient actual
source-attached responses, then gives an exhaustive quantitative role
reselection.

The export should preserve all of the following nonclaims:

* none of the grafted whole profiles is proved minimum-fibre;
* a paid behavioral edge is not an exact Nash--Bellman edge;
* mover-debt subtraction gives no control of other caps;
* macroscopic censored reshuffling is not consumed;
* the regression has zero global minimum; and
* no terminal approximants, uniform payoff, or positive-gap table are
  produced.

Likely Lean handoff dependencies are exactly the declarations named in the
note: finite-deadline timing realization, retained-tail payoff/cap transport,
and `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`.  The
capstone should return literal profiles and exact equalities, not only an
existential paid number.
