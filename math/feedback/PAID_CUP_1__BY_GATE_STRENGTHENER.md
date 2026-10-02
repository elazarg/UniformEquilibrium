# Gate-strengthening review of `PAID_CUP_1.md`

## Verdict

The mathematical core of Sections 1--2 is correct.  It gives a useful new
classification of exact roots against the *prescribed payoff* of a terminal
semantic pair when all Continue is the unique root at its cap.  The equality
case can be sharpened substantially: it is not merely a solo-debtor root, but
an exact zero-premium solo gate whose owner is tight at the singleton reward.

The cross-law identity in Section 4 is also correct and admits a quantitative
finite-coalition dichotomy.  For Fin4, an owner debt at least `gamma` yields
either singleton pressure at least `gamma / 2`, or one weighted nonempty
coalition toggle at least `gamma / 14`.

These statements do **not** currently compose with the checked
singleton-base, induced-owner, paid-cap, or support-drop consumers.  In
particular, they do not produce an admissible temporal edge, a fixed-law
variation, or a renewable rank decrease.  My verdict is therefore:

* **PASS** as a Research theorem packet after the corrections below;
* **FAIL for export** until an actual-data adapter and terminal or renewable
  consumer are supplied.

## 1. Sharp active-zero-debt lifting theorem

Let `p = (u,b)` be a terminal semantic pair and write

\[
 d_i=b_i-u_i\geq 0.
\]

For a product root `x`, let `s_i(x)` be the probability that all opponents of
`i` Continue, and let

\[
 \Delta_i(v,x)=Q_i(x)-C_i(v,x).
\]

Then

\[
 \Delta_i(b,x)=\Delta_i(u,x)-s_i(x)d_i.                 \tag{1}
\]

Hence the following general finite-player statement is valid.

> **Active-zero-debt lifting.**  Suppose `d_i >= 0` for every player, `x` is
> an exact root Nash profile against `u`, and
> \[
> x_i(Q)>0\Longrightarrow d_i=0.
> \]
> Then `x` is an exact root Nash profile against `b`.

The same conclusion holds with a supplied epsilon in place of exactness: the
proof is playerwise, and raising only a pure-Continue player's continuation
value cannot increase the gain from changing its marginal.

The nonnegativity assumption is essential for an abstract pair.  It is
automatic for an actual terminal semantic pair and for every point in the
terminal-semantic carrier.

If all Continue is the unique exact root against `b`, it follows that every
non-all-Continue exact root against `u` activates a player with positive debt:

\[
 x\ne \mathbf C\quad\Longrightarrow\quad
 \exists i, d_i>0\text{ and }x_i(Q)>0.                 \tag{2}
\]

This is the main genuinely new observation in the packet.  It concerns the
ordinary root game at `u`; it is not a second maximal-root theorem at `b`.

## 2. Exact debt action and the sharp equality gate

For an exact root Nash profile against `u`, the checked debt-block identity
gives, coordinatewise,

\[
 d_i(T_xp)=\bigl(s_i(x)d_i(p)-\pi_i(u,x)\bigr)_+,       \tag{3}
\]

where `pi_i(u,x) >= 0` is the root exercise premium.  Therefore

\[
 d_i(T_xp)\leq s_i(x)d_i(p)\leq d_i(p).                \tag{4}
\]

Combine (2)--(4).  Under uniqueness of all Continue at `b`, every exact root
against `u` satisfies exactly one of the following inclusive alternatives:

1. `x` is all Continue;
2. total debt strictly falls: `D(T_x p) < D(p)`;
3. there is a unique debtor `i`, every opponent of `i` is pure Continue,
   `x_i(Q)>0`, and total debt is preserved.

The third arm has additional exact structure.  Equality of total debt forces

\[
 s_i(x)=1,\qquad \pi_i(u,x)=0,                          \tag{5}
\]

and positive Quit probability plus endpoint Nash gives

\[
 r_i(\{i\})=u_i.                                       \tag{6}
\]

For every opponent `j != i`, the root Continue inequality holds against the
solo mixture.  Thus the sharp name for arm 3 is an **exact singleton-tight,
zero-premium solo-debtor gate**.

The draft should not call every nontrivial solo-debtor root an equality case.
A solo root can still strictly decrease debt through positive exercise
premium.  Arm 3 is precisely the debt-preserving subcase.

Because the finite root game against `u` has an exact mixed Nash profile, this
also yields the root-correspondence theorem:

\[
\boxed{
 \text{prescribed-payoff exact root with strict debt descent}
 \ \lor\ 
 \text{exact solo-debtor equality gate}
 \ \lor\ 
 \text{all Continue is unique at both }u\text{ and }b.}
                                                               \tag{7}
\]

The uniqueness-at-`b` hypothesis must be explicit in the public statement.
For an abstract pair, coordinatewise nonnegative debt must also be explicit.
For an actual profile, the strict-debt arm is an actual profile obtained by
literal root prefixing; for an arbitrary carrier point it is only a carrier
descent, not yet an executable source transition.

## 3. Fin4 singleton-source / owner-repair adapter

The retained double-port data supply:

* at the original singleton source, the positive-debt support is exactly the
  singleton owner;
* at the repaired profile, the owner debt is zero and at least one free-player
  debt is positive;
* `b^S_o = u^R_o = b^R_o`.

Applying (7) separately to the two actual profiles sharpens the paired
unique-cap arm to

\[
\boxed{
\begin{array}{l}
\text{strict actual prescribed-payoff debt descent on one side, or}\\
\text{a source singleton-owner equality gate, or}\\
\text{a repaired unique-debtor singleton equality gate, or}\\
\text{all Continue is unique against both prescribed payoff vectors.}
\end{array}}                                                   \tag{8}
\]

This is stronger local information than
`sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique`,
but it does not subsume that theorem.  The maximal theorem selects roots at
the cap and regenerates paid/reset source data.  The present theorem selects
roots at the prescribed payoff; a strict prefix need not preserve the reset
law, the cap port, or any maximality certificate.

## 4. Cross-law identity and a sharp finite dichotomy

Let `F = I \ {o}`.  Let `c` be the probability that all free players Continue
at the repaired stationary root, let `nu_R` be the repaired terminal law on
nonempty `Q subset F`, and let `nu_S` be the original owner-joined law.  The
stored law transport is

\[
 \nu_S(\{o\})=c,
 \qquad
 \nu_S(Q\cup\{o\})=(1-c)\nu_R(Q).                      \tag{9}
\]

Using `u^R_o=b^S_o`, the owner's source debt is exactly

\[
 d_o^S
 =c\bigl(u_o^R-r_o(\{o\})\bigr)
  +\sum_{\varnothing\ne Q\subseteq F}
      \nu_S(Q\cup\{o\})
      \bigl(r_o(Q)-r_o(Q\cup\{o\})\bigr).             \tag{10}
\]

No sign assumption on the individual summands is needed for the following
one-sided statement.  For every `theta` with `0 < theta < 1`, either

\[
 c\bigl(u_o^R-r_o(\{o\})\bigr)\geq \theta d_o^S,        \tag{11}
\]

or there is a nonempty `Q subset F` such that

\[
 \nu_S(Q\cup\{o\})
 \bigl(r_o(Q)-r_o(Q\cup\{o\})\bigr)
 \geq \frac{(1-\theta)d_o^S}{2^{|F|}-1}.               \tag{12}
\]

Indeed, if (11) fails, the sum in (10) is strictly greater than
`(1-theta)d_o^S`; one of its `2^{|F|}-1` terms has at least the average.  The
selected term is automatically positive, so it provides both positive source
atom mass and a strict owner leave-toggle.

For Fin4, choose `theta=1/2`.  If `d_o^S >= gamma`, then either

\[
 c\bigl(u_o^R-r_o(\{o\})\bigr)\geq \gamma/2,           \tag{13}
\]

or some nonempty free coalition has weighted leave-toggle at least

\[
 \gamma/14.                                            \tag{14}
\]

The factor `1/14` is the sharp uniform pigeonhole constant obtainable from
(10) with the symmetric half split: there are seven nonempty free coalitions.
Other choices of `theta` trade singleton pressure against the toggle bound.

In the source solo equality gate, (6) says `r_o({o})=u_o^S`; hence
`u_o^R-r_o({o})=d_o^S`.  This simplifies the first term but still does not
turn it into a reached Nash--Bellman edge.

## 5. Consumer audit

I found no checked consumer that closes either gate.

* **Induced-owner / one-date-then-Never.**  Those results require the relevant
  zero-tail Quit-versus-Continue signs and outsider no-join inequalities.  The
  first arm (13) is instead positive owner floor-excess.  The required signs
  do not follow.
* **Support drop.**  A solo-debtor equality gate already has support rank one
  and preserves it.  A strict decrease of its real debt need not make the debt
  vanish and is not a well-founded natural-valued decrease.  On the repaired
  side, other coordinates can enter after a prefix unless a no-entry theorem
  is added.
* **Fixed-law reset.**  The reset theorem compares points on one fixed law.
  A non-all-Continue prefix changes that law by adding fresh root absorption;
  the source and repaired laws in (9) are also distinct.
* **Maximal paid-cap regeneration.**  Its selected roots are exact at `b`.
  The new roots are exact at `u`; the interesting positive-debt active player
  is precisely what prevents the lifting theorem from moving them to `b`.
* **Paid-chain / cross-law identity.**  The original source-to-repair update is
  already a genuine paid behavioral edge.  Equation (10) disintegrates its
  value across terminal coalitions, but a selected summand is not by itself an
  exact temporal or Nash--Bellman edge.

Thus the surviving mathematical seam is not root existence.  It is the
source-faithful consumption of a singleton-tight equality gate or of the
weighted toggle in (12).

## 6. Boundary tests

The following tests should accompany any formal statement.

1. **Active zero debt is necessary.**  In a one-player root game with
   `u=0`, `b=1`, and singleton reward `0`, pure Quit is exact at `u` but not at
   `b`.
2. **Debt nonnegativity is necessary.**  With `u=0`, `b=-1`, and singleton
   reward `-1/2`, pure Continue is exact at `u` but not at `b`.
3. **Cap uniqueness is necessary for (2).**  If all rewards and both vectors
   are zero, every root is exact at both vectors, including nontrivial roots
   activating no positive debt.
4. **The solo equality arm is real.**  Take a two-player semantic root game
   with `u=(0,0)`, `b=(1,0)`, player 1's singleton reward `0`, and player 2
   strictly preferring Continue against every root.  All Continue is unique at
   `b`, while player 1 may use a nontrivial solo mixture at `u`; its unique debt
   is preserved and the singleton constraint is tight.
5. **A solo root need not preserve debt.**  Raising the owner's singleton Quit
   payoff above `u_i` gives positive exercise premium and strict debt descent,
   even though no opponent quits.
6. **Equation (12) needs no termwise sign assumption.**  Negative toggle terms
   are harmless: if the total toggle sum exceeds the threshold, at least one
   term exceeds its average.  Conversely, an unweighted positive toggle does
   not imply positive source incidence, so the product in (12) must be kept.

These are semantic/root-game regressions, not positive-gap quitting-game
counterexamples.

## 7. Lean-facing handoff

Natural declarations are:

```text
isEpsilonQuittingRootNash_cap_of_prescribed_of_active_debt_eq_zero

isZeroQuittingRootNash_prescribed_eq_allContinue_or_debtSum_lt_or_soloGate_of_unique_cap

FinFourSingletonBaseResetRepairPaidCapDoublePort.
  prescribedRootDescent_or_soloGate_or_doublePrescribedUnique

QuittingSingletonBaseStationaryHandoff.
  source_owner_debt_eq_crossLawToggleSum

FinFourSingletonBaseResetRepairPaidChain.
  singletonPressure_or_weightedLeaveToggle
```

The first two belong near `TerminalSemanticPair.lean` or a small prescribed-
versus-cap root file.  The exact debt formula should reuse
`quittingTerminalSemanticDebt_prefix_eq_blockAct`; the equality case should
reuse the face lemmas behind
`quittingTerminalSemantic_minimum_stratum_alternative`, without assuming
global minimality.  The last two should expose the law identity separately
from the Fin4 `gamma/2`--`gamma/14` specialization.

## 8. Gate conditions

### PASS for a nonterminal Research packet

Require:

1. the exact lifting theorem with nonnegative-debt and active-zero hypotheses;
2. the corrected equality arm including unique debtor, opponents pure
   Continue, zero premium, and singleton tightness;
3. an actual-profile Fin4 adapter on both sides of the retained double port;
4. the exact cross-law identity and the weighted finite-coalition dichotomy;
5. explicit statements that strict real descent is not a renewable rank and
   that no displayed toggle is yet an admissible chronology edge.

### PASS for export

In addition, require at least one of:

* a checked terminal/UE consumer for every solo equality gate;
* a source-faithful admissible return from (10)--(12); or
* a renewable finite-rank transition whose no-entry and regeneration fields
  are proved for the actual prefixed profiles.

### Current verdict

Those export conditions are absent.  The note should not enter `exports/` in
its current form.
