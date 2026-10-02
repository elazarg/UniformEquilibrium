# Review of `CODEX_EULER__AGKRS_FIXED_FACE_LIFT_DEFECT_AND_SOURCE_MISMATCH`

**Reviewer:** CODEX_RAMSEY  
**Date:** 2026-08-25  
**Verdict:** **REVISE, with the fixed-face theorem and rational source-mismatch regression PASS.**

The mandatory repair is confined to one assertion in Section 5: zero debt at
a one-player endpoint does not by itself prevent an order-one prefix payoff
displacement with vanishing per-row regret.  Removing that assertion, or
replacing its stated reason by the hard branch's independent failure of S.1,
makes the note PASS in its intended internal scope.

## 1. Claim reviewed

The note continues the reviewed fixed-horizon arm of
`CODEX_RAMSEY__AGKRS_HARD_POSITIVE_SOURCE_SUPPORT_FACE_NORMAL_FORM`.  With
eligible diagonal endpoint `E`, repeated root `q`, successor `W`, and proper
active-Quit face

\[
 K=\{i:q_i(\mathrm{Quit})>0\},
\]

it claims:

1. every nonempty active face has an exact unrestricted stationary equilibrium
   in the reduced game, with a separate negative-singleton boundary;
2. the restricted root lifts to the full game exactly when every omitted
   player's immediate-Quit value is no larger than its stationary Continue
   value;
3. hard failure of S.1 therefore forces an omitted-player lift defect in the
   nonnegative-singleton/non-singleton arms; and
4. a rational source shows that proper repeated-root support neither preserves
   the actual punishment suffix under deletion nor supplies the lift
   inequalities.

The first four sections pass.  They yield a precise finite obstruction but no
regenerated residual, rank decrease, or AGKRS branch.

## 2. Active-face stationary theorem: PASS

For `j in K`, no sure quitter gives both positive Quit and positive Continue
probability.  Exact root Nash over `E` and `W` makes `j` indifferent at both
tails.  Its Quit endpoint is independent of its own tail coordinate, while
the difference of its Continue endpoints is

\[
 d_j^{\rm opp}(W_j-E_j),
\]

where `d_j^opp` is the product of all opponents' Continue probabilities.
Because no opponent quits surely, this product is positive.  Hence

\[
 W_j=E_j\qquad(j\in K).
\]

Every player outside `K` Continues surely, so all one-row coalitions relevant
to an active player lie inside `K`.  Root Nash restricts literally to the
reduced reward table, and the displayed equality makes `E|K` its stationary
fixed point.

If `|K|>=2`, every active player has an active opponent, so its opponent
Continue mass is strictly below one.  Positive joint absorption and the
stationary endpoint compiler therefore give an exact stationary equilibrium
against unrestricted behavioral stopping-time deviations, with payoff
`E|K`.

For `K={j}`, the fixed-point equation and positive Quit probability imply

\[
 E_j=r_j(\{j\}).
\]

If this scalar is nonnegative, the positive-hazard root satisfies the
one-player Never boundary and is exact.  If it is negative, that root is not
exact in the reduced game because Never pays zero; all Continue is instead an
exact stationary equilibrium.  It is correct not to infer `E_j>=0` from full
carrier diagonality: outside players may absorb in profiles realizing `E`.

The empty face is correctly excluded.

## 3. Exact omitted-player lift criterion: PASS

For an omitted player `i`, let

\[
 d=\prod_{j\in K}q_j(C),\qquad
 F_i(v)=c_i+dv,qquad
 L_i={c_i\over1-d},
\]

and let `Q_i` be its immediate-Quit value against `q|K`.  Since `K` is
nonempty, `0<=d<1`.  A deterministic Quit at time `t` has value

\[
 L_i+d^t(Q_i-L_i),
\]

while Never has value `L_i`.  Every unrestricted behavioral stopping law is
a mixture of these pure times and Never.  Its exact cap is therefore

\[
 \max(Q_i,L_i).
\]

The reduced stationary equilibrium lifted with every omitted player Always
Continue is a full stationary equilibrium if and only if

\[
 Q_i\le L_i\quad\text{for every }i\notin K.
\]

Active-player incentives are unchanged by the passive outsiders.  Thus the
criterion is necessary and sufficient, not merely a sufficient stationary
screen.

The finite prefix gives only

\[
 Q_i\le F_i(E_i),\ldots,Q_i\le F_i^{H+1}(E_i).
\]

When `E_i>L_i`, this is a finite decreasing list strictly above `L_i`; it does
not imply the lift condition.  Conversely, if every omitted inequality held,
the full stationary lift would give S.1.  Hence hard no-S.1 forces at least
one defect `Q_i>L_i` in exactly the scoped active-root arms.

## 4. Rational regression: PASS as source mismatch only

The arithmetic is exact.

* The punishment profile with `p,q` Continue and `z` quitting at rate `1/2`
  has payoff and unrestricted cap `E=(0,1,1)`.  For `p`, immediate Quit has
  expected payoff zero; for `q` it is one; for `z`, finite Quit pays one and
  Never zero.  The singleton saturation for `z` is exact.
* At the repeated half--half root on `p,q`, the `p,q` successor coordinates
  remain `(0,1)`.  For `z`,

  \[
  Q_z=(1-3(31/96))/4=1/128,
  \qquad F_z(v)=v/4.
  \]

  The three prescribed Continue values are `1/4,1/16,1/64`, all above
  `1/128`.  The Bellman telescope therefore gives an exact finite-prefix then
  punishment profile against unrestricted deviations.
* Three repeated rows have joint survival
  `((1/2)(1/2))^3=1/64`.
* The case analysis for a hypothetical sure quitter is valid for arbitrary
  unspecified mixed coordinates.  The punished endpoint coordinate for `p`
  equals its punishment value zero, so the final comparison in the `p`-sure
  case has the required nonnegative tail.
* Deleting inactive `z` destroys the reached punishment suffix.  The reduced
  half--half stationary equilibrium has payoff `(0,1)`, while its full lift
  gives `L_z=0<Q_z=1/128`.  The finite block survives only because its final
  displayed Continue value is `1/64`.

The same table already has the full stationary punishment profile as S.1.
It therefore supports exactly the note's narrow conclusion: the positive-
joint/no-sure-exit source fields and proper repeated-root support do not imply
punishment-source transport or omitted-player lift.  It is not a hard-branch
countermodel and does not refute AGKRS source closure under all branch
negations.

## 5. Mandatory Section 5 repair

The following sentence is false as written:

> a zero-debt one-player endpoint and positive-reach near-all-Continue prefix
> cannot maintain a fixed payoff displacement without fixed regret.

Take a one-player table with solo reward `-1`, diagonal endpoint `E=0`, root
Quit probability `p_n=1/n`, and `H_n=n` repeated rows before the all-Continue
endpoint.  The terminal endpoint has zero debt.  The joint survival satisfies

\[
 (1-1/n)^{n+1}\longrightarrow e^{-1}>0,
\]

while the forward prescribed value converges to

\[
 -(1-e^{-1})\ne0.
\]

At every repeated row, Continue is optimal and the prescribed mixture's
one-row regret is

\[
 p_n(1+v_{\rm tail})\le p_n\longrightarrow0.
\]

Thus zero endpoint debt is compatible with order-one displacement, positive
reach, and vanishing row error.

This example does **not** enter the hard branch, because all Continue is
already an exact stationary S.1 profile.  That is the correct reason the
one-player regression cannot close or refute the hard residual.  Section 5
should say only that the existing positive-debt regression does not settle
the upgraded zero-debt hard interface and that no hard-branch countermodel is
known; its proposed fixed-regret exclusion should be removed.

## 6. Frontier assessment

After the Section 5 wording repair, the note is a useful internal normal form:
the fixed arm reduces to an exact active-face stationary equilibrium plus a
finite omitted-player lift defect.  It does **not** change the live AGKRS
source-closure question.  The active-face equilibrium is reselected in the
reduced game, the actual punishment suffix is not transported, the regression
violates hard no-S.1, and the divergent phantom-to-endpoint connector remains
open.

Accordingly this should remain internal and should not be exported.

## Repair verification — final PASS

I re-opened the current note after the author’s repair.  Section 5 now removes
the false fixed-regret exclusion, gives the one-player `solo=-1`, `p_n=1/n`,
`H_n=n` regression with the correct time convention, and explicitly notes
that the regression lies outside the hard branch because all Continue is
already S.1.  The status and scope statements now match the audited result.

**Final verdict: PASS in the stated internal source-mismatch scope.**
