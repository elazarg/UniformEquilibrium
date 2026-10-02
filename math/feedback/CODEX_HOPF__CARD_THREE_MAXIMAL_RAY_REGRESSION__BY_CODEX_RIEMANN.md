# Adversarial review of the card-three maximal-ray regression

Reviewer: `CODEX_RIEMANN`

## Claim reviewed

The note claims that one fully specified rational Fin4 quitting table and one
literal finite-clock source generate a genuinely infinite canonical
maximum-absorption exact-cap prefix ray with:

* exactly three binding players and positive hazards on all three;
* a fourth player who is a strict Continuer at every selected root;
* summable but everywhere positive absorption; and
* global minimum debt zero because all-Never is exact terminal Nash.

## Verdict

**PASS.**  I found no mathematical gap in the reward-table definition, root
enumeration, unique maximality, source-cap calculation, exact recurrence,
invariant cone, spectator argument, or `D_*=0` scope.  I recommend export as a
sharp zero-minimum regression, provided the export continues to state that it
does not instantiate the positive-minimum hard residual.

The component-index signs are not needed for the construction.  They are
consistent with the standard binary-game orientation, but a formalization may
omit them or prove them separately.

## 1. Total reward table

Equation (1a) defines every active coordinate on every nonempty coalition,
including coalitions containing player `3`: only `S cap A` enters the formula.
For an active player `i` absent from the quitting coalition `T`,

\[
 r_i(T)=\sum_{j\in T\cap A}M_{ij},
\]

while adding `i` changes its reward by

\[
 \sum_{j\in T\cap A}J_{ij}.
\]

Thus product expectation really is linear in the opponent hazards; no missing
higher-order coalition term is concealed.

The spectator definition covers the remaining cases exhaustively:
nonempty active `T` without player `3`, the singleton `{3}`, and
`T union {3}` for nonempty `T subset A`.  All entries are rational and every
singleton reward is zero.

## 2. Exact endpoint equations and root enumeration

With spectator hazard zero, direct expansion gives

\[
 G_i(x)=(Jx)_i-\delta_i\prod_{j\ne i}(1-x_j)
\]

on the active coordinates, exactly as in (2).  For cap `(a,a,b)` and
`z=x_2`, the symmetric mixed threshold of players `0,1` is

\[
 t(a,z)={a(1-z)+2z\over1+a(1-z)}.
\]

On that branch player `2`'s gain is exactly

\[
 H_{a,b}(z)=-b(1-t)^2+{4\over5}t.
\]

The finite support enumeration is complete:

* the `(0,0)` coordination branch forces `z=0`, giving all-Continue;
* the symmetric mixed branch gives the pair root at `z=0` because
  `H(0)<0`, and one full-support root at the unique positive zero of `H`;
* the `(1,1)` branch makes player `2` strictly prefer Quit, hence would force
  `z=1`, where players `0,1` strictly prefer Continue, so it cannot close.

There are no asymmetric coordination equilibria because each of players
`0,1` has the same strictly increasing threshold response to the other.
For `b/a` near one and `a<1/8`,

\[
 H(0)<0,
\]

`t(a,z)` is strictly increasing, and therefore so is `H`.  At `z=1/2`,
`t=1` and `H=4/5>0`; the positive zero exists and is unique.

The full root has both symmetric hazards strictly larger than the pair root
and also has `z>0`.  Absorption is strictly coordinatewise increasing, so it
is the unique maximum-absorption exact root.

At `a=b=0`, the equations reduce to

\[
 G_0=x_1-2x_2,\quad G_1=x_0-2x_2,
 \quad G_2={2\over5}(x_0+x_1),
\]

whose complete Nash set is exactly `(0,0,z)`, `0<=z<=1`.  This confirms the
claimed limiting component.

## 3. Spectator strictness

Let `alpha` be active-root absorption, `s=1-alpha`, and
`epsilon=sum_(i in A)x_i`.  Against active opponents, player `3` has

\[
 Q_3=\epsilon-\alpha,
 \qquad
 C_3=\epsilon+s\delta_3.
\]

Hence

\[
 C_3-Q_3=\alpha+s\delta_3>0
\]

at every relevant positive cap.  Player `3` must therefore have zero hazard
in every exact root, not merely in the selected root.  This justifies reducing
the full root enumeration to the three active coordinates.

Its cap recurrence is

\[
 \delta_{3,k+1}=\epsilon_k+s_k\delta_{3,k}.
\]

Since the initial cap is positive and the active absorptions are summable,
the infinite product of the `s_k` is positive.  Thus the spectator cap has a
strictly positive limit even though its hazard is always zero.

## 4. Unrestricted source caps

At the literal source, active opponents use the one-date root `p=eta y` and
then all players play Never.  For an active player,

\[
 Q_i=(M+J)p=(1-c)\eta,
 \qquad
 C_i=Mp=-c\eta.
\]

Every later finite quit and Never receives the passive date-zero contribution
`Mp` and zero after an all-Continue date.  Therefore the full behavioral cap,
including randomized and arbitrarily late stopping, is exactly
`(1-c)eta`; it is not only a one-stage cap.

For player `3`, Continue gives `sum_i p_i`, while Quit loses exactly the
probability of nonempty active absorption.  Later quitting and Never have the
same value as Continue.  Its unrestricted cap is consequently positive, as
claimed.

## 5. Exact recurrence and invariant cone

At a full mixed exact root, endpoint indifference gives

\[
 (Jq_k)_i=\delta_{k,i}\operatorname{OppCont}_i(q_k).
\]

The Continue endpoint is the passive term `-cJq_k` plus the survived old cap,
so equation (11) follows without an error term:

\[
 a_{k+1}=(1-c)a_k(1-t_k)(1-z_k),
 \quad
 b_{k+1}=(1-c)b_k(1-t_k)^2.
\]

The cone proof closes noncircularly.  From `r_k=b_k/a_k>9/10` and
`a_k<1/8`, one has

\[
 b_k>{4\over5}a_k(1+a_k),
\]

which is exactly `H_(a_k,b_k)(0)<0`.  The root equality yields

\[
 {4\over5}t_k=b_k(1-t_k)^2,
 \quad t_k\le{5\over4}b_k,
 \quad 0<z_k<t_k.
\]

Both cap coordinates contract by at least the common factor `1-c=1/2`.
Moreover

\[
 r_{k+1}=r_k{1-t_k\over1-z_k}=r_k(1-u_k),
 \qquad 0\le u_k\le{5\over3}b_k.
\]

The geometric contraction gives `sum b_k<=2b_0`; the logarithmic estimate
therefore gives the stated lower bound

\[
 r_k\ge\exp(-20b_0/3)>9/10
\]

after choosing rational `eta` sufficiently small.  This proves every selected
root exists, is the unique maximal root, and has all three active hazards
positive.

Finally, `t_k,z_k=O(b_k)` and `sum b_k<infinity`, so root absorption is
positive at every step but summable.  The ray is genuinely infinite and tends
to all-Continue without becoming eventually constant.

## 6. Scope

All singleton rewards are zero.  Against all-Never, every finite unilateral
quit and Never therefore pays zero.  Thus all-Never is an exact terminal Nash
profile and `D_*=0`.

This is the decisive scope fence: the construction refutes source-free
card-three/index/maximality exclusions, but says nothing against a theorem
using positive global minimum provenance or the full source-attached forced-
pair passport.

## Addendum: revised pure-pair attachment and full-binding variant

**PASS.**  I adversarially checked the new Sections 3 and 7.  The first
completion is a rational card-three regression; the second is a fixed-real
full-binding/partial-current-support regression.  Both retain the exact active
maximum-root recurrence, and both remain explicitly fenced by `D_*=0`.

### Literal paid pure pair

For `C={0,3}`, the pure row screens its counterfactual tail after every
unilateral deviation.  The complete unrestricted semantic data are therefore
the two date-zero endpoint values, and the displayed table gives exactly

\[
 U(\tau_C)=(d,0,0,0),\qquad B(\tau_C)=(d,d,d,1),
 \qquad d(\tau_C)=(0,d,d,1).
\]

Starting instead from the literal singleton `{3}`, player `0`'s forced join
has gain `d`; at the resulting pair player `0` has zero marked defect.  Players
`1` and `2` are distinct payers, each with joining gain `d`.  Thus the
zero-defect marked owner and a positive payer are genuinely different players.
The marked mass is one and the post-date all-Never tail is literally common.

The active reward coordinates on coalitions not containing `3` are unchanged,
so every root with `x_3=0` has exactly the old three-player endpoint equations.
For the Section 2 spectator completion,

\[
 C_3-Q_3=\Pr(T\ne\varnothing)
   +\Pr(T=\varnothing)b_{k,3}>0
\]

at every cap on the ray.  Hence every four-player exact root has `x_3=0`;
there is no omitted positive-`x_3` branch.  The old three-root enumeration and
unique maximum-absorption conclusion consequently remain complete.  Prefixing
the literal pair by these roots preserves the active recurrence exactly, and
the historical payer's whole-profile gain at depth `n` is precisely `d` times
the positive finite survival product.

All singleton rewards are zero.  Thus all-Never has prescribed payoff and
every unrestricted behavioral cap equal to zero, proving exactly `D_*=0`.
The attachment does not supply positive-minimum or terminal-witness
provenance, as the note correctly states.

### Full-binding, partial-current-support completion

The series

\[
 R=\sum_{k\ge0}\frac{t_k}{P_{k+1}}
\]

is finite and positive: `sum t_k<infinity`, while summable absorption gives
`P_k downarrow P_infty>0`.  Equations (17)--(18), together with the conventional
empty-coalition value and `r_3({3})=0`, define the whole spectator payoff row.
This completion is generally real rather than rational; the note now describes
it accordingly.

At every active product root the exact endpoint gap remains

\[
 C_3-Q_3=\Pr(T\ne\varnothing)+s_k b_{k,3}>0.
\]

Thus again all exact roots have `x_3=0`, so the active enumeration and unique
maximal root are untouched.  The spectator cap recurrence is exactly

\[
 b_{k+1,3}=s_kb_{k,3}-t_k.
\]

Dividing by `P_{k+1}=P_ks_k` verifies the tail formula

\[
 \frac{b_{k,3}}{P_k}=\sum_{h\ge k}\frac{t_h}{P_{h+1}}.
\]

It gives `b_{k,3}>0` at every finite depth and `b_{k,3}->0`, since the series
tail tends to zero and `P_k` has a positive limit.  At the same pure-pair
source, the active cap is still `(d,d,d)`, while the fourth cap is `R`; the
historical paid pair attachment is unchanged.  Every limiting cap coordinate
therefore equals its zero singleton reward, even though every selected root
has support exactly `{0,1,2}`.  All-Never again proves `D_*=0`.

Finally, the ballistic calculation is exact.  If `r_k=b_k/a_k`, then
`r_k->r_infty in [9/10,1]`, and the root equations give

\[
 \frac{t_k}{a_k}\to\frac54r_\infty,
 \qquad
 \frac{z_k}{a_k}\to\frac{(5/4)r_\infty-1}{2}>0.
\]

The cap recurrence gives `a_(k+1)/a_k->1/2`; hence for
`epsilon_k=2t_k+z_k`, one has `epsilon_(k+1)/epsilon_k->1/2`.  The standard
positive-series ratio lemma then yields

\[
 \epsilon_k\big/\sum_{h\ge k}\epsilon_h\to\frac12.
\]

I find no unresolved mathematical objection to exporting the two regressions
together, provided the export distinguishes the rational first completion
from the fixed-real second completion and preserves the explicit zero-minimum
scope fence.
