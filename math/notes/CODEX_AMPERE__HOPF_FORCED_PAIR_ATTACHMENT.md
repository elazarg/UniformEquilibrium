# Attaching the card-three HOPF ray to a literal paid pure pair

## Status

Ordinary mathematics, not checked in Lean and not independently reviewed.

The repaired card-three maximal-root regression can be attached to a literal
forced-pair row with:

* initial cap `(a,a,b,1)` in the HOPF invariant cone;
* one designated pair member with zero marked root defect;
* one designated outsider with an arbitrary fixed positive marked root defect;
* a fourth coordinate which has zero source debt, remains a strict Continuer
  at every selected maximal root, and has constant cap one; and
* the original three-active-coordinate maximal-root recurrence unchanged
  exactly.

Thus the literal pure pair, zero-defect owner, and fixed paid sibling are not
algebraically incompatible with the card-three ray.  The construction still
has `D_* = 0`, so it does not attach the positive-minimum or terminal-witness
provenance of the genuine forced-pair branch.

## 1. Active HOPF table

Let the players be `0,1,2,3` and put `A={0,1,2}`.  Fix

$$
J=
\begin{pmatrix}
0&1&-2\\
1&0&-2\\
2/5&2/5&0
\end{pmatrix},
\qquad
M=-\frac12J.
$$

For every nonempty coalition `S subset A` and active recipient `i in A`, use
the HOPF reward

$$
r_i(S)=
\sum_{j\in S\setminus\{i\}}M_{ij}
+\mathbf 1_{\{i\in S\}}
 \sum_{j\in S\setminus\{i\}}J_{ij}.
\tag{1}
$$

In particular, every active singleton reward is zero.  Against an active cap
excess `(a,a,b)`, and with player `3` Continuing, the active endpoint equations
are exactly those of `CODEX_HOPF__CARD_THREE_MAXIMAL_RAY_REGRESSION.md`.

Choose a positive rational `epsilon` sufficiently small for its invariant-cone
proof and set

$$
a=b=\varepsilon.
$$

Fix an arbitrary rational paid gap `kappa>0`; it need not shrink with
`epsilon`.

## 2. Completion on coalitions containing player 3

Let the desired forced pair be

$$
C=\{2,3\}.
$$

For the active reward coordinates on coalitions containing `3`, set every
unspecified value to zero and impose only

$$
\begin{array}{lll}
r_0(\{2,3\})=a-\kappa,
&\qquad&r_0(\{0,2,3\})=a,\\[1mm]
r_1(\{2,3\})=a,
&&r_1(\{1,2,3\})=a,\\[1mm]
r_2(\{3\})=b,
&&r_2(\{2,3\})=b.
\end{array}
\tag{2}
$$

Define player `3`'s coordinate by

$$
r_3(\{3\})=0,
\tag{3}
$$

$$
r_3(T)=1
\qquad(\varnothing\ne T\subseteq A),
\tag{4}
$$

and, for nonempty `T subset A`,

$$
r_3(T\cup\{3\})=
\begin{cases}
1,&T=\{2\},\\
0,&T\ne\{2\}.
\end{cases}
\tag{5}
$$

Equations (1)--(5) give a total rational four-player reward table.

## 3. Literal pure-pair source

Let `sigma_C` play the pure coalition `C={2,3}` at date zero and all-Never
after a hypothetical all-Continue outcome.  Since two players Quit surely,
the tail is never reached under any unilateral deviation.

The four unrestricted caps are therefore the two endpoint maxima:

$$
\begin{aligned}
B_0(\sigma_C)
 &=\max\{r_0(\{2,3\}),r_0(\{0,2,3\})\}=a,\\
B_1(\sigma_C)
 &=\max\{r_1(\{2,3\}),r_1(\{1,2,3\})\}=a,\\
B_2(\sigma_C)
 &=\max\{r_2(\{2,3\}),r_2(\{3\})\}=b,\\
B_3(\sigma_C)
 &=\max\{r_3(\{2,3\}),r_3(\{2\})\}=1.
\end{aligned}
\tag{6}
$$

Thus

$$
\boxed{B(\sigma_C)=(a,a,b,1).}
\tag{7}
$$

Take player `2` as the designated forced owner and player `0` as the paid
outsider.  Their root defects on the literal pair row are

$$
\boxed{\Delta_2(C)=0,\qquad \Delta_0(C)=\kappa.}
\tag{8}
$$

Player `1` also has zero defect.  By (4)--(5), player `3` is indifferent on
this particular pair row and likewise has zero defect.  Hence

$$
d(\sigma_C)=(\kappa,0,0,0).
\tag{9}
$$

This realizes the strongest local forced-pair pattern: a zero-defect forced
owner and a unique fixed positive payer at the required initial cap.

## 4. The active maximal-root recurrence is unchanged

Consider any prefix root with player `3`'s hazard zero.  Every current terminal
coalition then lies in `A`, so the active endpoint equations use only (1).
Therefore the complete HOPF enumeration and maximum-absorption selection apply
verbatim.  If the current active cap is `(a_k,a_k,b_k)`, the selected root is

$$
q_k=(t_k,t_k,z_k,0)
$$

and the next active cap is exactly

$$
\begin{aligned}
a_{k+1}&=\frac12a_k(1-t_k)(1-z_k),\\
b_{k+1}&=\frac12b_k(1-t_k)^2.
\end{aligned}
\tag{10}
$$

Starting from `a_0=b_0=epsilon`, the HOPF invariant cone

$$
0<a_k,b_k,\qquad 9/10<b_k/a_k\le1
\tag{11}
$$

and summable positive absorption follow unchanged.

## 5. Player 3 stays strict and its cap stays one

Let `S subset A` be the random active quitting coalition at one prefix root.
If player `3` Continues, its endpoint payoff is always one:

* if `S` is nonempty, equation (4) gives reward one;
* if `S` is empty, the continuation cap is one.

If player `3` Quits, equations (3) and (5) give payoff one only when
`S={2}`, and zero otherwise.  Thus

$$
Q_3-C_3=\Pr(S=\{2\})-1\le0.
\tag{12}
$$

At every HOPF root, `S` is not almost surely `{2}`, so the inequality is
strict.  Player `3` uniquely Continues and its next cap is exactly one.

It remains to exclude an additional exact root with positive player-`3`
hazard.  Equality in (12) forces

$$
x_0=x_1=0,\qquad x_2=1.
\tag{13}
$$

If `x_3<1`, player `2` strictly prefers Continue: its Quit-minus-Continue
difference is

$$
-(1-x_3)b_k<0.
\tag{14}
$$

If `x_3=1`, player `0` strictly prefers Quit by exactly `kappa`, using (2).
Hence (13) cannot be completed to a Nash root for any `x_3>0`.  The HOPF
active roots are the complete four-player Nash-root set, and their full active
root is still the unique maximum-absorption root.

## 6. Literal paid sibling survives every depth

Prefix `sigma_C` by the first `n` selected maximal roots.  Because each prefix
root is exact against the current cap, this is the canonical maximal-root ray
from the literal pair source.  Its survival product is positive at every
finite depth.  At the shifted pair row, player `2` still has conditional defect
zero and player `0` still has conditional defect `kappa`.  The actual whole-
profile gain from changing player `0` to Quit is

$$
\kappa\prod_{k<n}\prod_i(1-q_{k,i})>0.
\tag{15}
$$

Thus the ray retains a literal source pair and its paid historical sibling at
every finite depth, rather than merely sharing their labels.

## 7. Exact limitation

All singleton rewards remain zero.  Consequently all-Never is an exact
terminal Nash profile and

$$
D_*=0.
\tag{16}
$$

The construction therefore does not satisfy the positive-minimum source,
terminal exploitability witness, punishment-normality packet, or minimum-law
provenance of the genuine Fin4 forced-pair branch.  It proves only the sharp
local compatibility statement:

$$
\boxed{
\begin{array}{c}
\text{card-three maximal-root HOPF recurrence}\\
+\ \text{literal pure pair}\\
+\ \text{zero forced-owner defect}\\
+\ \text{fixed positive paid outsider}
\end{array}
\quad\text{is realizable.}}
$$

Accordingly, an exclusion of the card-three ray cannot use only the literal
pair, the local zero/positive defect pattern, or the paid sibling.  It must use
the genuinely global positive-minimum passport or another hard-residual field.

## Files inspected

* `notes/CODEX_HOPF__CARD_THREE_MAXIMAL_RAY_REGRESSION.md`
* `exports/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md`
* `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`
* `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`
* `Research/Quitting/FinFourProducerAtlas/StrictEndpointNormalizedReturn.lean`

## Next exact question

Can the same attachment be realized after imposing `D_*>0` and the terminal
witness?  Equivalently, does positive-minimum provenance impose an inequality
on rewards involving the omitted spectator which is absent from (1)--(16) and
incompatible with the strict-continuation completion (3)--(5)?
