# Remote bubbles carry a response-value reentry cocycle

Author: `CODEX_RESPONSE_SWITCH`

## Status

Ordinary mathematics, not checked in Lean.  Internal Research note; not an
export candidate.

The ordered response chronology does not by itself orient the remote
bubble/all-Never cap jump.  It does give a new exact alternative.  A fixed
positive response gain can recur indefinitely only if regeneration repeatedly
erases the value of the response just installed.  The erasure is an exact
same-label, cross-profile **reentry loss**, and its cumulative size is at least
the cumulative response gain up to one bounded endpoint error.

Consequently, any source adapter proving vanishing or summable reentry loss
immediately consumes the infinite ordered arm.  Current semantic/full-law
source equality does not prove that adapter.  A rational Fin4 regression based
on `CODEX_RIEMANN__REMOTE_BUBBLE_ALL_NEVER_JUMP_REGRESSION.md` has:

* one fixed observer and literally closed response labels;
* `q_k < t_k < q_(k+1)`;
* fixed response gain, zero target-observer debt, and a unit nonsingleton
  marked atom;
* all marginal clocks converging to Never while the full law is a unit
  finite bubble;
* identical complete terminal semantic pairs and outcome laws on both sides
  of every regeneration; but
* reentry loss exactly equal to the response gain and a strict failure of the
  desired cap-jump inequality.

Its global minimum is zero.  It therefore does not refute a theorem using a
genuine positive-minimum source.  It proves that such a theorem must use that
global provenance to control the reentry cocycle; ordered clocks, response
labels, unrestricted caps, semantic equality, and full-law equality still do
not do so.

## 1. Exact question and inspected material

Start with the quantitative remote-bubble output of
`CODEX_RESPONSE_SWITCH__ADJACENT_REACTIVATION_CLOCK_OR_BUBBLE.md`.  Thus one
has a fixed observer `o`, ordered pure times

\[
 q_k<t_k\le q_{k+1},                                    \tag{1.1}
\]

a fixed response gain `g>0`, response targets with `o`-debt tending to zero,
a fixed marked coalition with mass at least `lambda>0` at `t_k`, literal
outgoing-to-next-incoming response labels, and the mismatch between limiting
marginals and the limiting full terminal law.

The question is whether this extra chronology forces:

* the bubble social reward to be charged by the cap jump;
* terminal approximants or a charged return; or
* renewable finite-rank descent.

I used the exact debt/cap-jump identity and rational table in
`CODEX_RIEMANN__REMOTE_BUBBLE_ALL_NEVER_JUMP_REGRESSION.md`, together with the
source-faithful response-menu boundary in
`CODEX_LEIBNIZ__SOURCE_FAITHFUL_RESPONSE_CHORD_COCYCLE_BOUNDARY.md`.  Caps
throughout are unrestricted behavioral best-response envelopes.

## 2. The exact response-value cocycle

The following statement is game-independent apart from bounded payoffs.
Let `P_k` be actual profiles and let `q_k` be pure-time plans of one fixed
player `o`.  Define

\[
 x_k:=U_o(P_k[o\leftarrow Q_{q_k}]),
 \qquad
 y_k:=U_o(P_k[o\leftarrow Q_{q_{k+1}}]).                \tag{2.1}
\]

Assume the installed switch at every rank has gain

\[
 G_k:=y_k-x_k\ge g>0.                                  \tag{2.2}
\]

Literal label closure means that the response `q_(k+1)` in `y_k` is the same
complete pure-time strategy evaluated as the incoming response at
`P_(k+1)`.  If the successor chart prefixes or reindexes its suffix, this
requires the corresponding exact clock shift; raw equality of two relative
`Option Nat` labels is not enough.
Define its reentry loss by

\[
 \ell_k
 :=y_k-x_{k+1}
 =U_o(P_k[o\leftarrow Q_{q_{k+1}}])
  -U_o(P_{k+1}[o\leftarrow Q_{q_{k+1}}]).               \tag{2.3}
\]

Then, exactly,

\[
 x_{k+1}-x_k=G_k-\ell_k.                               \tag{2.4}
\]

Summing from `k=0` to `N-1` gives the response-value cocycle

\[
 \boxed{
 \sum_{k<N}\ell_k
 =\sum_{k<N}G_k-(x_N-x_0).}                             \tag{2.5}
\]

If every terminal reward has absolute value at most `R`, then
`|x_N-x_0|<=2R`.  Hence

\[
 \boxed{
 \sum_{k<N}\ell_k\ge Ng-2R.}                          \tag{2.6}
\]

In particular,

\[
 \limsup_{k\to\infty}\ell_k\ge g.                     \tag{2.7}
\]

Thus an infinite fixed-gain chain is impossible under any of the following
sufficient source-coherence conditions:

\[
 \ell_k\longrightarrow0,
 \qquad
 \sum_k(\ell_k)_+<\infty,
 \qquad\text{or more generally}\qquad
 \sum_{k<N}\ell_k=o(N).                                \tag{2.8}
\]

This is an actual consumer theorem: response-value-faithful regeneration
rules out the infinite ordered arm, without using compactification or a
cap-jump sign.

The conclusion is also sharp.  If the installed gain persists, regeneration
must return a positive average reentry loss.  This is stronger than another
paid row: `ell_k` compares the **same named pure response** on the actual
outgoing and successor environments.  But it is not yet a unilateral gain.
The two environments may differ in several players' strategies.  Turning a
positive `ell_k` into an executable first-disagreement chronology requires a
literal regeneration path between those environments, with its intermediate
profiles and marks retained.

If there is a literal path of uniformly bounded length `L` from `D_k` to the
response-overridden successor
`P_(k+1)[o <- Q_(q_(k+1))]`, changing one nonobserver strategy at a time and
keeping `o`'s prescribed response fixed throughout, telescoping (2.3) selects
one step at which the fixed-response payoff falls by at least `ell_k/L`.
This is a source-matched **fixed-response externality edge**.  It is not yet
a four-corner response square: no second prescribed-baseline column or sign
for its change has been supplied.  It still needs a consumer relating the
observer loss to the changed player's incentive, a charged return, or a
minimum-support transition.  No such sign follows merely from the payoff
drop.

## 3. Why the cocycle is not the bubble cap-jump inequality

Let the response target be

\[
 D_k=P_k[o\leftarrow Q_{q_{k+1}}].
\]

If `d_o(D_k)->0`, own-strategy cap invariance says that `y_k` approaches the
unrestricted `o`-cap against the opponents of `P_k`.  Equation (2.3), however,
compares that cap-attaining value with the same response against the **next
opponent profile**.  Neither terminal semantic convergence nor convergence of
the prescribed terminal law makes escaping pure-time response payoffs
continuous in this cross-profile direction.

Accordingly, (2.5) charges repeated response gains to reentry loss, not to

\[
 \Delta_B=\sum_i\bigl(b_i-B_i(\bar\sigma)\bigr),
\]

the total cap jump between the remote semantic limit and the actual marginal
limit.  Even perfect charging in coordinate `o` says nothing about the
escaped social rewards or cap jumps of the other coordinates.  The identity

\[
 D(\bar\sigma)-D_*=E_{\rm soc}-\Delta_B                \tag{3.1}
\]

at a minimum bubble therefore remains unoriented.

Positive global minimality gives only `D(bar_sigma)>=D_*`, which is the weak
sign `E_soc>=Delta_B`.  To reverse it, the source attachment must control the
reentry losses or supply a genuinely global deformation/rank argument.  The
ordered response labels themselves do not.

## 4. Rational ordered-clock regression

Use exactly the reward table from
`CODEX_RIEMANN__REMOTE_BUBBLE_ALL_NEVER_JUMP_REGRESSION.md`.  Put
`A={0,1}`.  For player `0`, set

\[
 r_0(S)=
 \begin{cases}
 -3,&S=\{0\},\\
 -4,&S=\{0,3\},\\
 -1,&0\in S\text{ and }S\ne\{0\},\{0,3\},\\
 -3,&S=\{3\},\\
 0,&\text{otherwise}.
 \end{cases}                                           \tag{4.1}
\]

For player `1`, symmetrically, set

\[
 r_1(S)=
 \begin{cases}
 -3,&S=\{1\},\\
 -4,&S=\{1,3\},\\
 -1,&1\in S\text{ and }S\ne\{1\},\{1,3\},\\
 -3,&S=\{3\},\\
 0,&\text{otherwise}.
 \end{cases}                                           \tag{4.2}
\]

Finally set

\[
 r_2(\{2\})=3,
 \qquad r_2(A)=5,
 \qquad r_2(A\cup\{2\})=6,                            \tag{4.3}
\]

with its other coordinates zero, and

\[
 r_3(S)=
 \begin{cases}
 3,&S=\{3\},\\
 6,&S=A,\\
 -1,&3\in S\text{ and }S\ne\{3\},\\
 0,&\text{otherwise}.
 \end{cases}                                           \tag{4.4}
\]

Fix observer `o=3`.  For `k>=0`, set

\[
 q_k=2k,
 \qquad t_k=2k+1,
 \qquad q_{k+1}=2k+2.                                  \tag{4.5}
\]

Let `P_k` prescribe players `0` and `1` to Quit at `t_k`, and players `2`
and `3` to play Never.  Let

\[
 D_k=P_k[3\leftarrow Q_{q_{k+1}}].                    \tag{4.6}
\]

The base pair quits before the prescribed response in `D_k`, so both `P_k`
and `D_k` terminate with coalition `A` at `t_k`.  In particular the fixed
nonsingleton marked mass is

\[
 \Pr_{D_k}(A\text{ at }t_k)=1.                         \tag{4.7}
\]

The incoming response quits one date before the base pair, while the outgoing
response quits one date after it.  Hence

\[
 U_3(P_k[3\leftarrow Q_{q_k}])=r_3(\{3\})=3,
 \qquad
 U_3(D_k)=r_3(A)=6.                                    \tag{4.8}
\]

Thus `G_k=3` at every rank, and

\[
 q_k<t_k<q_{k+1}.                                      \tag{4.9}
\]

The outgoing label `q_(k+1)=2k+2` is literally the incoming label at the next
rank.  Against the opponents in `P_k`, observer `3` obtains `3` by quitting
before `t_k`, `-1` by joining at `t_k`, and `6` by waiting beyond `t_k` or
Never.  Therefore its unrestricted behavioral cap is `6`, and

\[
 d_3(D_k)=0                                             \tag{4.10}
\]

exactly, not merely asymptotically.

At the next environment, the very same response `q_(k+1)` occurs before
`t_(k+1)=2k+3`, so

\[
 U_3(P_{k+1}[3\leftarrow Q_{q_{k+1}}])=3.
\]

Consequently

\[
 \boxed{\ell_k=6-3=3=G_k}                              \tag{4.11}
\]

at every regeneration.  The response gain is reset exactly by the reentry
loss.

### 4.1 Exact semantic/law equality does not stop the reset

All `P_k` and `D_k` have the same terminal payoff, the same unrestricted cap,
and the same full outcome law:

\[
 u=(-1,-1,5,6),
 \qquad b=(0,0,6,6),
 \qquad d=(1,1,1,0),
 \qquad \operatorname{Law}=\delta_A.                   \tag{4.12}
\]

Thus both sides of every regeneration are not merely close: their complete
terminal semantic/law points are exactly equal.  Nevertheless the value of
the escaping common response drops by three.  This is the precise
noncontinuity which semantic/law provenance does not record.

Every marginal stopping law in `D_k` converges weakly to Never, while the
full law remains `delta_A`.  The actual marginal-limit profile is all-Never.
The Riemann calculation gives

\[
 E_{\rm soc}=9,
 \qquad \Delta_B=6,
 \qquad D(\text{all-Never})-D(u,b)=6-3=3.              \tag{4.13}
\]

Therefore

\[
 \boxed{E_{\rm soc}>\Delta_B}                          \tag{4.14}
\]

despite the full ordered response chronology, fixed gain, exact zero target
debt, unit nonsingleton marked atom, unrestricted caps, and exact
semantic/full-law equality across regeneration.

### 4.2 Scope of the regression

The pure singleton `{2}` is an exact all-behavior terminal Nash profile for
this table, so

\[
 \boxed{D_*=0.}                                        \tag{4.15}
\]

The regression does not have positive-minimum/source attachment and does not
refute a theorem that genuinely uses it.  It also does not refute terminal
approximation, since an exact terminal Nash profile exists elsewhere.  It
does prove that every other field listed above, including exact equality of
the source semantic/law point, is insufficient to orient the bubble cap jump
or make the ordered response gains telescope without loss.

It also deliberately fails next-chart installation: the outgoing response
has value `6` at `P_k` and the identical incoming response has value `3` at
`P_(k+1)`.  This is not a hidden defect in the example; it is exactly the
reentry loss isolated by (2.3).  A theorem whose source attachment genuinely
proves vanishing installation/reentry error is consumed by (2.6) and is not
refuted here.

As recorded in the Riemann note, the positive-debt point (4.12) additionally
satisfies the numerical minimum-fibre singleton-margin equalities,
punishment normality, and unique all-Continue exact cap-root condition.  Those
local hard-residual signs do not control (4.11).

## 5. Exact remaining producer

The response labels now expose the missing datum sharply.  A successful
positive-minimum theorem must prove one of:

1. **response-value-faithful reentry:** `ell_k->0`, or a sublinear cumulative
   reentry loss, contradicting (2.6);
2. **executable reentry localization:** retain an actual bounded-length path
   from `D_k` to the response-overridden next incoming environment, localize
   a fixed part of `ell_k` to one fixed-response externality edge, then add
   the missing baseline column and consume the resulting square into
   charge/return or renewable support descent; or
3. **global bubble deformation:** use positive-minimum provenance to compare
   the remote bubble with the actual marginal limit and prove the missing
   debt ordering directly.

Merely retaining the same semantic pair, full law, response label, and marked
coalition does not imply item 1.  The regression has all four exactly and
still has `ell_k=g`.

The most economical source-facing interface is therefore not another paid
row.  It is a `ResponseReentrySeam` carrying:

* the actual outgoing target `D_k` and next incoming profile `P_(k+1)`;
* the identical pure response `q_(k+1)` on both;
* the exact response-value loss `ell_k`;
* a literal regeneration path with intermediate profiles and marks; and
* the incoming minimum/source passport.

The cocycle (2.5) guarantees a fixed positive average supply of these seams.
The remaining mathematical operation is to consume one without losing
unrestricted cap control.

## 6. Lean-facing boundary and nonclaims

The generic algebra could be packaged as:

```text
responseSwitch_reentryLoss_sum_eq
responseSwitch_not_infinite_of_reentryLoss_sublinear
```

The quitting-game adapter would require a dependent source object, not just
semantic equality:

```text
FinFourSourceFaithfulResponseReentrySeam
```

This note does not:

* construct that adapter from current public Fin4 data;
* turn reentry loss into a unilateral profitable deviation;
* orient the remote bubble cap jump under positive global minimum;
* produce terminal approximants, a charged return, or renewable rank; or
* prove or refute Fin4 uniform equilibrium.
