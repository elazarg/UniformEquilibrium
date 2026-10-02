# Endogenous soft cyclic blocks: terminal Nash or isolated-owner escape

Author: `CODEX_SPINOZA`

## Status

The existence and debt estimates below are exact ordinary mathematics, not
checked in Lean.  They give an unconditional finite-dimensional producer for
every finite quitting table: at every period and every positive row error
there is a literal cyclic root word with exact Bellman return, strictly
interior product roots, and that row error.  Repeating the word is an actual
absorbing behavioral profile with one named payoff.

If the row error is little-o of every player-deleted absorption per period,
these profiles are terminal approximate Nash and a fixed payoff subsequence
is a uniform-equilibrium payoff.  Under a hypothetical positive global
terminal gap, the complementary output is a fixed player whose three
opponents have only \(O(H\varepsilon)\) absorption per period.  This is an
approximate isolated-owner cyclic packet, not a paid-port output.

What remains open is consumption of its two boundary regimes: a
singleton-dominant one-debtor limit, or a vanishing-total-hazard cyclic
tangent packet.  No claim is made that either regime is impossible.

## Question and probability mode

Let \(I=\operatorname{Fin}4\), and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I,
 \qquad |r_i(S)|\le M.
\]

Never pays zero.  Behavioral randomization is independent across players and
dates, conditional on the public event that play is still live.  A unilateral
deviation replaces one complete behavioral strategy and may Quit at any
finite date or Never.  All payoffs below are undiscounted terminal payoffs.

Can a finite-horizon construction choose its own continuation payoff, rather
than impose the false zero boundary, while retaining one payoff target and
complete terminal-deviation control?

## Sources inspected

The finite Nash--Bellman path type is in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanMinimizer.lean`, and
the exact cyclic objects and terminal compilers are in
`UniformEquilibrium/Quitting/Cycles/AdmissibleCycleTerminalEquilibrium.lean`.
The scalar companion contraction and its player-deleted survival factor are
in `CycleMismatchContraction.lean`.  The equality-one/isolation boundary is
in `CycleIsolatedCoordinate.lean`, especially
`isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one`.

Behavioral pure-time completeness is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`BehaviorPureTimeExtremality.lean`.  The fixed-target terminal limit theorem
is `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`TerminalUniformPayoffSelection.lean`.

The hard-zero-boundary obstruction is recorded in Section 10 of
`PAIRED_HULL_REVIEW__FULL_DEBT_ORTHOGONAL_PRODUCT_AND_PROJECTIVE_ATTACK.md`.
The passive-padding theorem in
`CODEX_SPINOZA__PERIODIC_COMPLEMENTARITY_AND_PASSIVE_PADDING_NO_GO.md`
excludes a universal exact bounded-period theorem.  The present result uses
approximate roots and allows the period to vary; it does not contradict that
no-go.

## 1. One-stage endpoints

Fix a continuation vector \(w\in[-M,M]^I\) and a product root
\(x\in[0,1]^I\), where \(x_i\) is player \(i\)'s Quit probability.  With the
other coordinates fixed, write

\[
 Q_i(x_{-i})
\]

for player \(i\)'s payoff from Quit, and

\[
 C_i(x_{-i},w)
\]

for its payoff from Continue, including \(w_i\) when every opponent
Continues.  The prescribed Bellman value is

\[
 F_i(x,w)=x_iQ_i(x_{-i})+(1-x_i)C_i(x_{-i},w).       \tag{1}
\]

All three expressions are continuous, and belong to \([-M,M]\).

For temperature \(\theta>0\), define the soft Quit response

\[
 L_i^\theta(x_{-i},w)
 =\frac{e^{Q_i(x_{-i})/\theta}}
 {e^{Q_i(x_{-i})/\theta}+e^{C_i(x_{-i},w)/\theta}}. \tag{2}
\]

It lies strictly between zero and one.  The elementary entropy bound gives,
when \(x_i=L_i^\theta(x_{-i},w)\),

\[
 \max\{Q_i,C_i\}-F_i(x,w)\le\theta\log2.             \tag{3}
\]

Thus (2) controls the ordinary two-action Nash defect; it is not a
regularized payoff used by the quitting game.

## 2. Unconditional soft cyclic producer

### Theorem 2.1 (endogenous-boundary soft cycle)

For every integer \(H\ge1\) and every \(\varepsilon>0\), there are product
roots

\[
 x_0,\ldots,x_{H-1}\in(0,1)^I
\]

and phase values

\[
 v_0,\ldots,v_{H-1}\in[-M,M]^I
\]

(indices read modulo (H)) such that

\[
 v_t=F(x_t,v_{t+1})                                      \tag{4}
\]

exactly, and every playerwise root Nash defect is at most
\(\varepsilon\):

\[
 \max\{Q_i((x_t)_{-i}),C_i((x_t)_{-i},v_{t+1})\}
       -(v_t)_i\le\varepsilon.                           \tag{5}
\]

Repeating (x_0,\ldots,x_{H-1}) forever gives an actual behavioral profile
(\sigma^{H,\varepsilon}).  It absorbs almost surely and its terminal payoff
from phase (t) is exactly (v_t).

#### Proof

Put \(\theta=\varepsilon/\log 2\).  On the compact convex set

\[
 \mathcal X=([0,1]^I)^H\times([-M,M]^I)^H
\]

define a continuous self-map by

\[
 x'_{t,i}=L_i^\theta((x_t)_{-i},v_{t+1}),
 \qquad
 v'_t=F(x_t,v_{t+1}).                                  \tag{6}
\]

The Bellman map preserves the reward box because every coordinate is a
convex combination of coalition rewards and the continuation coordinate.
Brouwer gives a fixed point.  Equations (4)--(5) follow from (3) and (6), and
(2) makes every root strictly interior.

Let

\[
 P=\prod_{t<H}\prod_{i\in I}(1-x_{t,i}).                 \tag{7}
\]

Strict interior gives \(P<1\).  One traversal of the word has Bellman form
\(a+Pv_0\), while (4) says \(v_0=a+Pv_0\).  Repetition has Never probability
\(\lim_NP^N=0\), and unrolling the same identity shows that its actual
terminal payoff is \(v_0\).  Phase shifts give every \(v_t\).  The product
roots are ordinary independent behavioral hazards. \(\square\)

This is a producer, not merely a verifier for supplied cyclic data.  Its
continuation boundary is selected endogenously as part of the Brouwer fixed
point.

## 3. Complete terminal-deviation estimate

For player \(i\), let

\[
 c_{t,i}=\prod_{j\ne i}(1-x_{t,j}),
 \qquad
 P_i=\prod_{t<H}c_{t,i},
 \qquad
 A_i^{-}=1-P_i.                                         \tag{8}
\]

Thus \(P_i\) is the probability that all opponents of \(i\) survive one
period; \(A_i^{-}\) is player-deleted, or opponent, absorption.  Strict
interiority gives \(A_i^{-}>0\).

### Theorem 3.1 (row error divided by opponent absorption)

For the actual periodic profile of Theorem 2.1, the unrestricted terminal
debt of every player satisfies

\[
 d_i(\sigma^{H,\varepsilon})
 \le {H\varepsilon\over A_i^{-}}.                       \tag{9}
\]

#### Proof

Let \(W_{t,i}\) be player \(i\)'s complete terminal cap from phase \(t\)
against the periodic opponents, and put

\[
 \delta_{t,i}=W_{t,i}-(v_t)_i\ge0.
\]

Pure-time extremality, or equivalently the scalar stopping Bellman equation,
gives

\[
 W_{t,i}=\max\{Q_i((x_t)_{-i}),
                    D_i((x_t)_{-i})+c_{t,i}W_{t+1,i}\}, \tag{10}
\]

where \(D_i+c_{t,i}(v_{t+1})_i\) is the prescribed Continue endpoint.
Using (5) in (10) yields

\[
 \delta_{t,i}\le\varepsilon+c_{t,i}\delta_{t+1,i}.     \tag{11}
\]

Iterate once around the period.  Every partial product of the \(c_{t,i}\)'s
is at most one, so

\[
 \delta_{0,i}\le H\varepsilon+P_i\delta_{0,i}.
\]

Since \(P_i<1\), rearrangement proves (9).  The same proof works from every
phase.  Equation (10) takes the supremum over arbitrary finite stopping times
and Never; no bounded-clock or stationary-deviation restriction is used.
\(\square\)

### Corollary 3.2 (direct fixed-payoff uniformization)

Let \(H_n\ge1\), \(\varepsilon_n>0\), and select the profiles above.  If

\[
 \max_i{H_n\varepsilon_n\over A_{n,i}^{-}}\longrightarrow0, \tag{12}
\]

then, after a subsequence,

\[
 v_{n,0}\longrightarrow v
\]

for one fixed \(v\in[-M,M]^I\), while the terminal exploitability tends to
zero.  Hence this particular limit \(v\) is a uniform-equilibrium payoff by
the checked theorem
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`.

The profile may depend on \(n\), but the limiting target \(v\) does not.  The
checked terminal-to-uniform theorem then supplies, for each accuracy, one
profile that works against every complete behavioral deviation on all
sufficiently long finite horizons.

## 4. Exact escape under a positive global gap

Assume hypothetically that every actual behavioral profile has maximum
terminal debt at least

\[
 \Gamma>0.                                               \tag{13}
\]

(A positive minimum of total debt \(D_*>0\) gives
\(\Gamma=D_*/4\).)  Choose any periods \(H_n\) and errors satisfying

\[
 H_n\varepsilon_n\longrightarrow0.                       \tag{14}
\]

### Theorem 4.1 (approximate isolated-owner escape)

After a subsequence there is one fixed player \(i\) such that

\[
 A_{n,i}^{-}\le {H_n\varepsilon_n\over\Gamma}
 \longrightarrow0.                                      \tag{15}
\]

Equivalently, the other three players jointly absorb during one period with
probability \(O(H_n\varepsilon_n)\).  In particular, for every \(j\ne i\),

\[
 1-\prod_{t<H_n}(1-x_{n,t,j})\le A_{n,i}^{-}\to0.       \tag{16}
\]

The same subsequence has one payoff target limit \(v_{n,0}\to v\).

#### Proof

At each actual periodic profile choose a player \(i_n\) with debt at least
\(\Gamma\).  Equation (9) gives (15) for \(i_n\).  Stabilize the label among
four players.  Since the opponent-survival product in (8) is no larger than
the full-period survival factor of any one opponent, (16) follows.  Compactness
of the payoff box gives the final assertion. \(\square\)

This is a full root word with literal successor values, not a horizontal
response profile.  It has exact Bellman equations, uniformly small row Nash
defects, a fixed debtor label, a fixed limiting payoff, and a quantitative
player-deleted survival defect.

### Corollary 4.2 (fixed-period exact isolated limit)

Fix \(H\) and let \(\varepsilon_n\downarrow0\).  Under (13), a subsequence of
the soft cycles converges phasewise to an exact cyclic Nash--Bellman block
\((x_t^*,v_t^*)_{t<H}\) such that one fixed player \(i\) satisfies

\[
 x_{t,j}^*=0\qquad(t<H,\ j\ne i).                       \tag{16a}
\]

Thus the limit is either all Continue at every phase or an isolated-\(i\)
cycle.  Its phase-zero value is a terminal-semantic carrier limit of the
actual absorbing soft profiles.

Indeed compactness gives a phasewise limit, (4) passes by continuity, and
the root defects in (5) vanish.  Equation (15) makes the product of all
opponent Continue probabilities tend to one.  Every factor lies in
\([0,1]\), so every opponent factor tends to one, proving (16a).

This does not by itself give a terminal Nash profile.  In the isolated
branch, player \(i\)'s deleted-survival product is one, exactly the exceptional
case of `CycleMismatchContraction.lean` and
`CycleIsolatedCoordinate.lean`; the Never mismatch can remain positive.

## 5. The two surviving boundary regimes

Let

\[
 A_{n,i}^{+}=1-\prod_{t<H_n}(1-x_{n,t,i})                 \tag{17}
\]

be the selected owner's own absorption probability per period.

### Proposition 5.1 (singleton-dominant arm)

If, after a further subsequence,

\[
 A_{n,i}^{+}\ge a>0,                                    \tag{18}
\]

then the terminal coalition law of the repeated profile converges to the
point mass on \(\{i\}\), and

\[
 v_{n,0}\longrightarrow r(\{i\}).                       \tag{19}
\]

Moreover every outsider \(j\ne i\) has terminal debt

\[
 d_j(\sigma^{H_n,\varepsilon_n})
 \le {H_n\varepsilon_n\over a}\longrightarrow0.         \tag{20}
\]

Thus the positive-gap witness becomes a one-debtor singleton semantic limit.

#### Proof

Within one period, every absorbing outcome other than singleton \(i\)
requires at least one opponent of \(i\) to Quit.  Its probability is at most
\(A_{n,i}^{-}\).  Total period absorption is at least
\(A_{n,i}^{+}\ge a\).  Repetition normalizes the one-period absorbing law by
this total absorption, so (15) gives convergence to singleton \(i\), proving
(19).

For \(j\ne i\), the opponents of \(j\) include \(i\), hence
\(A_{n,j}^{-}\ge A_{n,i}^{+}\ge a\).  Apply (9). \(\square\)

The owner's debt need not vanish.  When its opponents' period absorption
tends to zero, a deviation that waits through arbitrarily many periods is
divided by the small quantity in (15).  This is the exact conditional-
survival discontinuity retained by (9).

Although the terminal law tends to \(\delta_{\{i\}}\), the limiting cap
record need not be the cap of the literal pure-singleton profile: normalized
rare-opponent continuation can survive in the cap limit.  Hence this is a
carrier conclusion, not an actual singleton-source retraction.

Punishment normality alone does not turn the moving-period singleton arm
into a fixed collision deviation.  Here is a sharp boundary test.  Fix
distinct players \(i,j\), an integer \(H\ge2\), and \(\Gamma>0\).  Define
the reward table by

\[
 r_j(\{i,j\})=\Gamma
\]

and set every other reward coordinate equal to zero.  Every player is
punishment-normal: its solo payoff is zero, and opponents can hold its
unilateral terminal cap to zero by always Continuing.  In the \(H\)-periodic
profile, let only owner \(i\) Quit, with hazard \(1/H\) at each phase, and
repeat the word forever.  It absorbs almost surely at \(\{i\}\), while its
one-period owner absorption is

\[
 1-(1-1/H)^H\ge 1/2.                                  \tag{20a}
\]

Player \(j\)'s deviation to absolute time \(n\) is profitable only when it
ties \(i\) at that date, so its exact gain is

\[
 {\Gamma\over H}(1-1/H)^n\le {\Gamma\over H}.          \tag{20b}
\]

Never gains zero, and pure-time extremality gives the same upper bound for
every behavioral deviation.  Thus even a fixed collision premium and
macroscopic owner absorption can be diffused over a moving period.  This
table has the all-Never equilibrium and therefore is not a positive-gap
counterexample; it refutes only a direct inference from punishment normality
and a static premium.  The hard singleton arm still needs concentration,
bounded period, minimum-fibre anchoring, or a separate harmful-owner
consumer.

### Proposition 5.2 (vanishing-total-hazard arm)

If instead

\[
 A_{n,i}^{+}\longrightarrow0,                            \tag{21}
\]

then the joint absorption probability of one period tends to zero.  Since
all root Quit probabilities are strictly below one,

\[
 \sum_{t<H_n}\sum_{j\in I}x_{n,t,j}\longrightarrow0.     \tag{22}
\]

Thus the output is a vanishing-hazard cyclic Nash--Bellman packet with exact
return, row error \(\varepsilon_n\), and one fixed payoff target limit.  The
theorem does not assert that

\[
 H_n\varepsilon_n=o\!\left(
   \sum_{t,j}x_{n,t,j}\right),                            \tag{23}
\]

so the checked returned-block tangent consumer does not automatically apply.

#### Proof

The period joint survival is the product of the owner's survival and the
opponent-survival factor in (8).  Equations (15) and (21) make it tend to one.
For \(0\le q<1\), \(-\log(1-q)\ge q\).  Taking minus logarithms of the finite
joint survival product proves (22). \(\square\)

The exact residual is therefore not the paid-port waist:

\[
 \boxed{
 \text{one-debtor singleton normalization}
 \quad\text{or}\quad
 \text{vanishing-hazard exact-return soft cycles without (23).}}
 \tag{24}
\]

## 6. Moving-period Never regression

The player-deleted denominator in (9) cannot be replaced by total absorption,
even for exact Bellman cycles with a fixed payoff.

For every \(H\ge1\), take player \(0\) to Quit surely only at phase \(H-1\),
and let players \(1,2,3\) always Continue.  Give every player payoff \(-1\)
whenever that player belongs to the first quitting coalition and payoff zero
otherwise.  Put

\[
 v=(-1,0,0,0).
\]

Use \(v\) as the continuation after phase \(H-1\).  This is an exact cyclic
Nash--Bellman block: player \(0\) gets \(-1\) from every finite Quit time and
also \(-1\) by passing to the boundary, while an outsider gets zero by
Continue and \(-1\) by Quit.  The word has total absorption one and its
displayed payoff is the same fixed \(v\) for every \(H\).

Its actual infinite repetition absorbs at player \(0\)'s moving date and pays
\(v\).  Nevertheless player \(0\)'s unrestricted Never deviation pays zero,
so its terminal debt is one.  Here

\[
 A_0^{-}=0.
\]

Thus an exact endogenous boundary, exact row Nash, sure absorption, and one
fixed payoff do not imply terminal Nash when one coordinate is isolated.  The
example has global minimum zero (all Never is terminal Nash), so it is a
boundary test rather than a counterexample to the conjecture.

## Scope and next question

- The soft-cycle producer is unconditional for every finite quitting table;
  the positive-gap hypothesis is used only to force (15).
- The periodic profile is actual and absorbs almost surely.  The values are
  its undiscounted terminal payoffs, not discounted or artificial-boundary
  payoffs.
- The terminal cap estimate covers Never and arbitrarily late behavioral
  deviations.
- The result does not produce exact Nash roots, a terminal approximate Nash
  profile in the escape arms, or a bounded-period theorem.
- The singleton arm does not identify the owner's normalized rare-opponent
  payoff, and the diffuse arm lacks the relative-error estimate (23).

The precise next question is whether Fin4 punishment normality and the
positive minimum exclude the singleton-dominant limit (18), or force the
relative-error scale (23) in the vanishing-hazard arm.  Either conclusion
would feed a checked terminal or returned-block consumer without passing
through a paid port.
