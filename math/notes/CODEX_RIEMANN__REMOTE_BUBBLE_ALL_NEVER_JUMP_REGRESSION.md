# Remote bubbles versus all-Never: the hard-residual signs do not orient the jump

## Status

Ordinary mathematics, not checked in Lean.  The exact jump calculation and
the regression below are complete.  The regression has global minimum zero,
so it is not a Fin4 counterexample and does not refute a theorem using the
full positive-global-minimum premise.  It shows that the currently available
minimum-fibre singleton-separation inequality, punishment normality, a paid
bubble row, and unique all-Continue cap inertness do not imply the missing
reward-moment/cap-jump inequality.

The example is the eventual-all-Continue boundary of the strict ray, not a
nontrivial summable maximal ray.  Its purpose is to fence the proposed local
sign argument.

## 1. Exact question and sources

Suppose actual profiles have all marginal stopping clocks converge weakly to
Never while their terminal laws retain a finite bubble `e`.  Can positive
minimum and hard-residual signs prove that the escaped aggregate reward moment
does not exceed the downward jump of the unrestricted cap envelopes?

I inspected:

* `exports/STRICT_RAY_TAIL_NORMALIZED_CAP_FLOW.md`, especially the remote
  pure-coalition debt and all-Never formulas;
* `minimumTerminalSemantic_singletonMargin` and its aggregate forms in
  `TerminalSemanticMinimumAggregateSurplusConsumer.lean`;
* the uniform singleton separation and punishment-normality statements
  summarized in `formalized/FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md`; and
* the reviewed local bubble fence
  `CODEX_RAMSEY__POSITIVE_SOCIAL_BUBBLE_CAUSAL_INERT_CONVERTER_NOGO.md`.

All caps below are unrestricted behavioral best-response values.

## 2. The jump is exactly an ordering of two actual debts

Let the compact marginal limit be literal all-Never.  Write

\[
 s_i=r_i(\{i\}),
 \qquad D_N=\sum_i(s_i)_+
\]

for the debt of the actual all-Never profile.  Let the semantic/law limit of
the original profiles be `(u,b)` with debt

\[
 L=\sum_i(b_i-u_i).
\]

If `e(S)` is the escaped finite terminal law, then

\[
 u_i=\sum_{S\ne\varnothing}e(S)r_i(S).
\]

Define the escaped social moment and the cap jump by

\[
 E_{\rm soc}:=
   \sum_{S\ne\varnothing}e(S)\sum_i r_i(S),
\qquad
 \Delta_B:=\sum_i\bigl(b_i-(s_i)_+\bigr).
\]

Direct algebra gives

\[
 \boxed{D_N-L=E_{\rm soc}-\Delta_B.}                     \tag{1}
\]

No semicontinuity claim is hidden here; `Delta_B` is the signed difference
between the supplied limiting cap and the actual all-Never cap.

Consequently

\[
 E_{\rm soc}\le\Delta_B
 \quad\Longleftrightarrow\quad
 L\ge D_N.                                                \tag{2}
\]

This is important: “the bubble cannot dominate the cap jump” is not a local
reward inequality in disguise.  It is exactly the global assertion that the
remote-bubble semantic debt is at least the debt of the actual all-Never
profile.

If the remote bubble itself is a global minimum, then minimality gives the
**opposite** weak ordering

\[
 D_N\ge L=D_*;
\]

hence `E_soc >= Delta_B`.  A non-domination theorem would therefore force
equality, while a strict non-domination theorem would contradict the global
minimum.  Positive minimum alone cannot provide that theorem because it does
not order two arbitrary actual/limit points above the same infimum.

## 3. Singleton separation points in the other direction

At a minimum semantic point, the checked coordinate margin is

\[
 D_*-d_i\le u_i-s_i.
\]

Summing over Fin4 gives

\[
 \boxed{3D_*\le E_{\rm soc}-\sum_i s_i.}                 \tag{3}
\]

Thus singleton separation lower-bounds the escaped social moment relative to
the signed solo sum.  It does not upper-bound it by the cap jump.

For a pure remote coalition `C` with limiting survival `alpha`, the reviewed
ray formula gives

\[
 L=\alpha H_C,
\qquad
 H_C=\sum_i
 \left(\max\{r_i(C\cup\{i\}),r_i(C\setminus\{i\})\}
             -r_i(C)\right).
\]

The singleton inequalities constrain the prescribed reward moment, whereas
`Delta_B` contains the global behavioral cap envelopes.  Punishment
normality constrains minimax punishment values; it supplies no upper bound on
these cap jumps.  The next example realizes this separation exactly.

## 4. Complete rational Fin4 regression

Let the players be `0,1,2,3` and put `A={0,1}`.  Define the complete reward
table as follows; every value not specified by these cases is zero.

For player 0:

\[
 r_0(S)=
 \begin{cases}
 -3,&S=\{0\},\\
 -4,&S=\{0,3\},\\
 -1,&0\in S\text{ and }S\ne\{0\},\{0,3\},\\
 -3,&S=\{3\},\\
 0,&\text{otherwise}.
 \end{cases}                                             \tag{4}
\]

For player 1, symmetrically:

\[
 r_1(S)=
 \begin{cases}
 -3,&S=\{1\},\\
 -4,&S=\{1,3\},\\
 -1,&1\in S\text{ and }S\ne\{1\},\{1,3\},\\
 -3,&S=\{3\},\\
 0,&\text{otherwise}.
 \end{cases}                                             \tag{5}
\]

For player 2:

\[
 r_2(\{2\})=3,
 \qquad r_2(A)=5,
 \qquad r_2(A\cup\{2\})=6,                              \tag{6}
\]

and all its other coordinates are zero.

For player 3:

\[
 r_3(S)=
 \begin{cases}
 3,&S=\{3\},\\
 6,&S=A,\\
 -1,&3\in S\text{ and }S\ne\{3\},\\
 0,&\text{otherwise}.
 \end{cases}                                             \tag{7}
\]

The special punishment values in (4)--(5) do not affect the bubble profile;
they make player 3 a literal punisher for players 0 and 1.

### 4.1 Bubble family and unrestricted caps

For `n>=1`, let players 0 and 1 Quit deterministically at date `n`, and let
players 2 and 3 play Never.  The terminal outcome is always `A`, so

\[
 u=(-1,-1,5,6).                                          \tag{8}
\]

Pure-time enumeration gives the full behavioral caps

\[
 b=(0,0,6,6).                                            \tag{9}
\]

Indeed, players 0 and 1 obtain their cap 0 by waiting beyond the other base
player's exit; player 2 obtains 6 by joining `A` at date `n`; and player 3
obtains 6 by Never.  Pure stopping times exhaust the behavioral cap in a
quitting game.

Therefore

\[
 d=(1,1,1,0),
 \qquad L=3.                                             \tag{10}
\]

Equivalently, the remote-coalition toggle defects are

\[
 h(A)=(1,1,1,0),\qquad H_A=3,
\]

so this is exactly the reviewed remote-bubble formula with common survival
`alpha=1`.

All four marginal stopping laws converge to Never, while every terminal law
is `delta_A`.  Hence `e(A)=1` and

\[
 E_{\rm soc}=R(A)=-1-1+5+6=9.                           \tag{11}
\]

The all-Never profile has

\[
 D_N=(-3)_++(-3)_++3+3=6,                               \tag{12}
\]

and

\[
 \Delta_B=(0-0)+(0-0)+(6-3)+(6-3)=6.                   \tag{13}
\]

Thus

\[
 \boxed{E_{\rm soc}-\Delta_B=3=D_N-L>0.}                \tag{14}
\]

The escaped reward moment strictly dominates the cap jump.

The paid row is literal and fully reached: player 2 gains one by changing
from Never (payoff 5) to Quit at date `n` (payoff 6).

### 4.2 The minimum-fibre signs hold numerically

The solo vector is

\[
 s=(-3,-3,3,3),
\]

and

\[
 u-s=(2,2,2,3)=L\mathbf 1-d.                            \tag{15}
\]

Thus every checked minimum singleton-margin inequality holds at equality for
this positive-debt semantic point.  This does not make the point a global
minimum; it proves that the inequalities themselves cannot distinguish it.

Punishment normality also holds.  Player 3 quitting at date zero gives both
players 0 and 1 at most their solo payoff `-3`, whether they Continue or Quit.
Player 3 similarly punishes player 2 to zero, which is at most `s_2=3`, and
player 2 punishes player 3 to zero, which is at most `s_3=3`.

### 4.3 Unique inert exact cap root

Against tail cap `b=(0,0,6,6)`, player 3 strictly prefers Continue at every
opponent action: with no opponent quitter it compares `3<6`, and with an
opponent quitter its Quit payoff is `-1` while its Continue payoff is either
`0` or `6`.

Once player 3 Continues, players 0 and 1 strictly prefer Continue at every
remaining opponent action: alone they compare `-3<0`, and with a nonempty
opponent coalition not containing 3 they compare `-1<0`.  Once players
0,1,3 Continue, player 2 compares `3<6`.  Therefore

\[
 \operatorname{Nash}(b)=\{\mathbf C\}.                  \tag{16}
\]

Every finite exact cap-prefix stack is consequently an all-Continue stack,
has zero charge, and merely translates the unit bubble and paid row outward.

### 4.4 Zero-minimum scope

The pure singleton `{2}` is an exact all-behavior terminal Nash profile:
player 2 weakly prefers its payoff 3 to exposing the zero tail, and every
outsider weakly prefers Continue to joining `{2}`.  Hence the global minimum
is zero.

The example therefore does not satisfy a positive terminal exploitability
witness, the positive global minimum, or the full hard residual.  It is also
the eventually constant all-Continue boundary rather than a nontrivial
summable ray.  It does show simultaneously that:

* strict singleton separation of the precise minimum-fibre size;
* punishment normality;
* a positive all-Never debt;
* a unit nonsingleton bubble with positive social surplus;
* a fully reached paid pure-time row; and
* selector-independent unique all-Continue cap inertness

do not force `E_soc <= Delta_B`.

## 5. Exact missing global inequality

For the bubble-vs-all-Never route, the missing statement is one of the
following equivalent comparisons:

\[
 \boxed{E_{\rm soc}\le\Delta_B}
 \quad\Longleftrightarrow\quad
 \boxed{L\ge D_N}.                                       \tag{17}
\]

To contradict a positive global minimum directly one needs the strict form.
The weak form, combined with minimality when `L=D_*`, only proves equality and
makes all-Never another attained minimum point of positive debt.

Current singleton separation supplies a lower bound on `E_soc`, and
punishment normality supplies no comparison between `b_i` and `(s_i)_+`.
Thus neither addresses (17).  A valid proof needs a genuinely global field,
for example:

* a cap-jump lower bound charged coalition-by-coalition against the same
  escaped law `e`;
* an executable deformation from the remote bubble point to all-Never whose
  total debt is known not to increase; or
* a source-matched chronology proving that every unit of escaped social
  reward creates at least the same unrestricted cap surcharge.

Absent such a field, the all-Never comparison is just a comparison of two
un-ordered semantic debts.  No local hard-residual sign can orient it.

## 6. Next question

Does the **nontrivial** strict maximal-ray recurrence impose an additional
cap-flow identity, beyond singleton separation and punishment normality,
which implies `L>=D_N`?  The regression proves that any such theorem must use
nonzero infinitely many exact roots (or their normalized occupation flow),
not merely their all-Continue limit, the remote bubble, or the endpoint cap.
