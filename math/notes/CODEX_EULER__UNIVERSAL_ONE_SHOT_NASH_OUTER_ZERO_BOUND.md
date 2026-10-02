# Universal one-shot Nash obstruction to early quantile outer certificates

## Status

**Ordinary theorem proved; independent falsification requested.**  This is a
table-parametric actual-center construction, not a candidate-family
experiment.  For every normalized finite quitting table it gives a literal
one-date center of unrestricted semantic exploitability at most `2/3`.
Consequently the Fin4 quantile-clock lower problems satisfy

\[
 \max_r L_M(r)=0\qquad(1\le M\le36).                 \tag{0.1}
\]

In particular the first universally nontrivial level is not `M=25` but at
least `M=37`.  No claim is made about `L_37`.

The executable semialgebraic reduction is emitted by

```text
python3 experiments/fin4_quantile_center_prototype.py \
  dump-one-shot-universal --lambda-value 3/4
```

The command's table argument is only a concrete serialization test; the proof
below quantifies over every normalized table.

## 1. Exact statement

Let `I` be a nonempty finite player set.  Let every terminal reward lie in
`[-R,R]`, where `R>=0`.  Form the finite simultaneous game in which each
player chooses `Quit` or `Continue`.  A nonempty Quit coalition `S` receives
the quitting reward `r(S)`; the all-Continue action profile receives zero.

### Theorem 1.1 (one-shot Nash actual-center bound)

There is a mixed Nash equilibrium `p in [0,1]^I` of the simultaneous game.
Realize it as a quitting profile `sigma^p` in which player `i` quits at date
zero with probability `p_i` and otherwise Never quits.  Then this is a
literal actual finite-clock profile in `A_1`, and

\[
 0\le B_i(\sigma^p)-U_i(\sigma^p)\le {2R\over3}
 \qquad\text{for every }i.                            \tag{1.1}
\]

The cap `B_i` is against every unrestricted behavioral deviation, not merely
the two actions in the simultaneous game.

### Corollary 1.2 (normalized finite-player outer zero range)

Suppose now that the table is normalized, so `R=1`.  For the quantile
hierarchy with

\[
 K_m=2|I|m+1,\qquad \delta_m={|I|(|I|-1)\over m},     \tag{1.2}
\]

the diagonal midpoint of the center in Theorem 1.1 proves `L_M=0` whenever

\[
 M\le 3|I|(|I|-1).                                    \tag{1.3}
\]

For normalized rewards `R=1` and `I=Fin 4`, this gives `L_M=0` for every
`M<=36`.  Since every lower objective is nonnegative, the maximum over all
normalized Fin4 reward tables is also exactly zero through level 36.

## 2. Proof of Theorem 1.1

Fix a player `i`.  Under the opponents' product mixture, let `pi_i(S)` be the
probability that precisely the opponent coalition `S subseteq I\{i}` Quits.
Put

\[
 a_i=\pi_i(\varnothing)
     =\prod_{j\ne i}(1-p_j),\qquad
 s_i=r_i(\{i\}).                                      \tag{2.1}
\]

Write `Q_i` and `C_i` for the one-shot payoffs from pure Quit and pure
Continue:

\[
 \begin{aligned}
 Q_i&=\sum_{S\subseteq I\setminus\{i\}}
       \pi_i(S)r_i(S\cup\{i\}),\\
 C_i&=\sum_{\varnothing\ne S\subseteq I\setminus\{i\}}
       \pi_i(S)r_i(S).
 \end{aligned}                                       \tag{2.2}
\]

The empty term in `C_i` is zero.  Mixed-Nash optimality gives

\[
 U_i=p_iQ_i+(1-p_i)C_i=\max(Q_i,C_i).                 \tag{2.3}
\]

This equality includes `p_i=0` and `p_i=1`: at an endpoint the action used
with probability one is a best response.

Against the literal date-zero/Never profile, every deterministic quit date
has one of exactly three values:

- date zero has value `Q_i`;
- Never has value `C_i`; and
- every finite date at least one has the common after-support value

\[
 L_i=C_i+a_i s_i.                                     \tag{2.4}
\]

Indeed, a nonempty opponent coalition at date zero preempts the late quitter,
whereas on the all-opponents-Never event the late quitter receives its solo
reward.  Pure-time extremality therefore gives

\[
 B_i=\max(Q_i,C_i,L_i),\qquad
 d_i:=B_i-U_i=\max(0,L_i-U_i).                        \tag{2.5}
\]

If `s_i<=0`, then `L_i<=C_i<=U_i`, so `d_i=0`.  Suppose `s_i>0`.
First, comparison with Continue gives

\[
 d_i\le L_i-C_i=a_i s_i\le a_iR.                     \tag{2.6}
\]

Second, comparison with Quit cancels the entire empty-coalition solo term:

\[
 \begin{aligned}
 L_i-Q_i
 &=\sum_{\varnothing\ne S\subseteq I\setminus\{i\}}
   \pi_i(S)\bigl(r_i(S)-r_i(S\cup\{i\})\bigr)\\
 &\le 2R(1-a_i).
 \end{aligned}                                       \tag{2.7}
\]

Because `U_i>=Q_i`, equations (2.5) and (2.7) yield

\[
 d_i\le2R(1-a_i).                                     \tag{2.8}
\]

For every `a in [0,1]`,

\[
 \min(a,2(1-a))\le {2\over3};                        \tag{2.9}
\]

use the first term for `a<=2/3` and the second for `a>=2/3`.
Combining (2.6) and (2.8) proves (1.1).  Nash existence for the finite
two-action game supplies `p`.  This proof does not select a rational Nash
point; for rational rewards the point may be algebraic, which is sufficient
for literal actual-center and real-closed-field feasibility.

## 3. Proof of Corollary 1.2

The one-date profile embeds literally in every `A_(K_m)` by inserting
zero-mass dates before the exact Never atom.  For its semantic center `a`, set

\[
 z_{U_i}=z_{B_i}={a_{U_i}+a_{B_i}\over2}.             \tag{3.1}
\]

Then `F(z)=0`, and Theorem 1.1 gives

\[
 \|z-a\|_\infty={1\over2}\max_i(B_i-U_i)\le {R\over3}.
                                                               \tag{3.2}
\]

Under (1.3) with normalized `R=1`, the same embedded actual center lies within every radius
`delta_m` for `m<=M`.  Thus `z in R_M`, so nonnegativity of `F` gives
`L_M=0`.

For Fin4 and `R=1`, `delta_36=12/36=1/3`, proving (0.1).  At `M=37`, this
particular uniform estimate no longer fits: `12/37<1/3`.  That is only the
failure of this certificate, not evidence that `L_37>0`.

## 4. Exact semialgebraic reduction

The prototype's `dump-one-shot-universal` command emits the closed `A_1`
system with marginal variables `x_(i,0),x_(i,N)`, prescribed payoff, every
supported/after-support/Never deviation value, and unrestricted cap graph.
It adds the eight finite Nash inequalities

\[
 U_i\ge V_{i,0},\qquad U_i\ge V_{i,N},                \tag{4.1}
\]

and the exact midpoint equations `2z_U=U+B`, `z_B=z_U`.  Because `U` is the
prescribed mixture of the two action values, (4.1) is precisely the one-shot
mixed-Nash condition, including pure boundary equilibria.  Finite mixed Nash
existence proves this four-marginal semialgebraic system nonempty for every
table.  Equations (2.6)--(2.9) are the table-parametric certificate that its
midpoint obeys the level-36 distance constraints.

This replaces a direct `A_201` CAD attack at `M=25` by a four-probability
actual-center construction.  It produces a zero witness rather than an
approximate or closure point.

## 5. Checked declarations and scope

Inspected declarations:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` is the checked
  one-shot finite mixed-Nash producer at continuation zero.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
  upgrades the three pure-time values to the unrestricted behavioral cap.
- `quittingFiniteClockSemanticReachable_eq_range_fold` and
  `quittingFiniteClockSemanticReachable_isCompact` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` identify the
  literal actual finite-clock center and its compact finite-word model.
- `quantileClockSupport`, `quantileClockRadius`, and the Fin4 bracket in that
  file give the exact outer constants used in Corollary 1.2.

No external paper is used.  This theorem concerns the algorithmic outer
hierarchy.  It does not prove a uniform payoff, a positive terminal gap, a
zero-decision algorithm, or any claim about `M>=37`.

## 6. Boundary regressions and next question

- If every singleton payoff is nonpositive, then every `L_i<=C_i` and the
  selected one-shot center is already unrestricted exact.
- If one player quits surely, (2.6) and (2.8) remain valid; no division by its
  Continue probability occurs.
- With two or more sure quitters the all-opponents-Never probabilities vanish
  for the other sure quitter coordinates, and the same formulas apply.
- The scalar constant `2/3` is the sharp maximum of the two comparison bounds
  in (2.9).  This does not assert that some complete quitting table attains
  the bound simultaneously with all Nash equations.
- The proof is unchanged at zero-probability coalition cells and mixed-action
  ties.

The next bounded question is whether a second finite timing action yields a
strictly smaller **table-parametric** cap bound, or whether an exact normalized
table forces every finite timing Nash center to retain debt `2/3`.  A
candidate-family witness is not enough; the target is the universal level
`M=37`.
