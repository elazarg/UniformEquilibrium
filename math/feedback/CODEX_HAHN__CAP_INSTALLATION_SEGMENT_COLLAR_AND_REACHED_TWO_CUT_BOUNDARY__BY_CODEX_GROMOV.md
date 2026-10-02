# Review of the cap-installation collar and two-cut boundary

Reviewer: `CODEX_GROMOV`

Reviewed artifact:
`notes/CODEX_HAHN__CAP_INSTALLATION_SEGMENT_COLLAR_AND_REACHED_TWO_CUT_BOUNDARY.md`,
SHA-256
`36bc91b4db9322f843489fb3cb4c372fa7b9e58795f1cb93cced5111c5431b9e`.

## Verdict

**REVISE.**  The whole-segment collar and the proper-segment fixed-root
expenditure are sound.  The literal stationary two-cut construction is also
sound, but the claim that its off-minimum alternative is already true omits
one quantitative choice: the theorem's exit threshold depends on the
*declared hazard floor*.  The note must choose that floor small enough in
terms of the existing off-minimum excess.  Two subsidiary wording repairs
are also needed.

## Parts that pass

Changing player `b`'s own stopping law keeps its opponents and therefore its
complete cap fixed.  Payoff affinity gives

\[
 d_b(X_n^t)=(1-t)d_b(\sigma_n).
\]

Every cluster of the whole moving segment has cap coordinate exactly the
singleton reward.  The global minimum singleton margin separates that
cluster from every global minimum by at least `D_*` in the same cap
coordinate.  Compactness and continuity of total debt then give the claimed
uniform positive debt collar.  This argument includes the endpoint and uses
no stationarity.

At the fixed proper parameter, the debt floor and cap pin have exactly the
hypotheses of the reviewed fixed-cap-pin theorem.  Its debt-drop and
absorption constants in (9)--(13) are correct.  The copied tail-cap response
at a positive-survival exact prefix is a feasible complete response with gain
at least `c_n g`; it need not attain the new prefix cap, and the note should
call it a transported response rather than an unqualified “cap response.”

For the structured tropical source, stationarity and the Quit0 endpoint are
genuine supplied hypotheses.  Conditional on survival of the private mixture
row, its Quit0 component is excluded and stationarity leaves the literal
suffix `sigma_n`.  Thus in `q_n :: sigma_n^{t_*}` the cuts `1<2`, reach
`c_n`, the one-row marginal-hazard floor, and exit identity (15) are all
literal.  No hidden stationary claim is being made in the abstract collar.

The ordinary-law total-variation lower bound in (19) also has the right
constant for the convention `TV = sup_A`: a payoff difference `gamma` for a
function in `[-M,M]` forces `TV >= gamma/(2M)`.

## Required quantitative repair in Section 3

The checked Fin4 two-cut theorem does not call every strictly off-minimum
exit its first alternative.  With declared hazard floor `h`, it requires

\[
 D(\operatorname{exit})\ge
 D_*+\frac{e^h-1}{2}D_*.
\]

The note only knows `D(sigma_n) >= D_* + delta`.  Declaring the available
floor `h=t_*` need not make `(e^{t_*}-1)D_*/2 <= delta`; `delta` may be
arbitrarily smaller.  Hence the sentence “its off-minimum-exit alternative
is already true” is not yet justified as written.

This has a short exact repair.  Keep the actual one-row lower bound `t_*`,
but declare in the packet any fixed

\[
 0<h_0\le t_*
 \quad\text{with}\quad
 \frac{e^{h_0}-1}{2}D_*\le\delta.
\]

For example choose

\[
 h_0=\min\{t_*,\tfrac12\log(1+2\delta/D_*)\}>0.
\]

Then the packet's hazard hypothesis follows from the stronger actual bound,
and (15)--(16) literally satisfy the first disjunct.  The mathematical
boundary claimed by the note survives after this repair.

## Other repairs

1. In Section 2, an attained tail cap does not necessarily “shift through”
   each later positive-survival prefix; dynamic programming permits a fresh
   Quit0 reset.  Replace this with “enters the existing reset/shift
   escaping-cap-clock construction.”  The asserted loss of the original pin
   and the nonrenewal conclusion remain valid.
2. Close the display delimiters after equations (12) and (16).

After these changes, the note gives a valid global collar and an honest
proof that the most immediate stationary two-cut instantiation exits through
the pre-existing off-minimum port rather than forcing the paid-splice arm.

## Delta review

Reviewed SHA-256:
`0c312909400abaf01c89851b9fc6017a3373657cd40582383d241c019279fa6f`.

**MATHEMATICS PASS; formatting repair still incomplete.**  The new choice

\[
 h_0=\min\{t_*,\tfrac12\log(1+2\delta/D_*)\}
\]

is strictly positive, is at most the actual row-hazard floor, and satisfies
the required exit threshold: `h_0 <= (1/2) log(1+2 delta/D_*)` implies
`exp(h_0) <= sqrt(1+2 delta/D_*) <= 1+2 delta/D_*`.  Thus (18), and hence
the claimed first arm of the checked two-cut theorem, now follows.  The
transported response and reset/shift language has also been repaired without
overclaiming prefix-cap attainment.

However, the two display delimiters requested in the first review are still
open: after `\tag{12}` and after `\tag{16}` the file has `}` rather than
`\]`.  This is typesetting only.  Once those two characters are repaired,
the packet is a full PASS with no further mathematical change required.
