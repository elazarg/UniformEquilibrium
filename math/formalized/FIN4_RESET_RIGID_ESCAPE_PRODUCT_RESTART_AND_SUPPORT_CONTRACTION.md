# The Fin4 reset-rigid escape branch has a one-way product restart and support contraction

Authors: SOCIAL_WEIGHT_REVIEW

Independent reviews:
[PAIRED_HULL_REVIEW of the product restart and phase rank](../feedback/SOCIAL_WEIGHT_REVIEW__ZERO_NEVER_SCREENED_FREE_NASH_TO_UNIQUE_DEBTOR__BY_PAIRED_HULL_REVIEW.md),
[PAIRED_HULL_REVIEW final composite review](../feedback/FIN4_RESET_RIGID_ESCAPE_PRODUCT_RESTART_AND_SUPPORT_CONTRACTION__BY_PAIRED_HULL_REVIEW.md),
[CODEX_DESCENDANT falsification review](../feedback/FIN4_RESET_RIGID_ESCAPE_PRODUCT_RESTART_AND_SUPPORT_CONTRACTION__BY_CODEX_DESCENDANT.md)

Dependency reviews:
[CODEX_RAMSEY on the positive-Never late release](../feedback/CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY__BY_CODEX_RAMSEY.md),
[CODEX_EULER on the positive-Never late release](../feedback/CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY__BY_CODEX_EULER.md),
[SOCIAL_WEIGHT_REVIEW on the moving-row pair contraction](../feedback/PAIRED_HULL_REVIEW__ORIENTED_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD_SECTION17__BY_SOCIAL_WEIGHT_REVIEW.md),
[PAIRED_HULL_REVIEW on the common-prefix unrestricted-cap lemma](../feedback/SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE__BY_PAIRED_HULL_REVIEW.md),
[CODEX_DESCENDANT on the common-prefix unrestricted-cap lemma](../feedback/SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE__BY_CODEX_DESCENDANT.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table with 

\[
 |r_i(S)|\le M
\]

for \(M>0\).  At every live date the four players independently randomize
between Continue and Quit.  Never has payoff zero.  Unilateral responses are
unrestricted behavioral strategies, including Never, unbounded pure stopping
times, and arbitrary randomized clocks.

For a behavioral profile \(\sigma\), write

\[
 U_i(\sigma),\qquad
 B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i}),
\]

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
 \qquad D(\sigma)=\sum_{i<4}d_i(\sigma).
\]

Let \(\mathcal C^{\rm law}\) be the joint closure of prescribed payoff,
unrestricted cap, and the complete terminal law on the fifteen nonempty
coalitions and Never.  Put

\[
 D_*:=\min_{z\in\mathcal C^{\rm law}}D(z.1).
\]

Assume a supplied Fin4 hard residual with no uniform-equilibrium payoff.  Let
\(\Gamma>0\) be its terminal exploitability gap.  In particular,
\(D_*>0\), every player is punishment-normal, and the residual supplies the
following table facts:

1. some owner \(a\) satisfies
   
   \[
   r_a(\{a\})\ge\Gamma;
   \tag{1}
   \]

2. for this owner there is \(b\ne a\) satisfying
   
   \[
   r_b(\{a,b\})-r_b(\{a\})\ge\Gamma;
   \tag{2}
   \]

3. every global minimum point \(z=(U,B,\mu)\) satisfies the singleton moat
   
   \[
   B_i-r_i(\{i\})\ge D_*
   \qquad (i<4);
   \tag{3}
   \]

4. every global minimum joint-law point has a positive finite coalition
   coordinate.

Suppose the reset-rigid/all-player-escape construction supplies an
`escapeOrigin` packet with:

* one complete FinFourMinimumAtomProducer at an original global minimum;
* four selected marginal stopping-law limits \(\mu_i\) on
  \(\overline{\mathbb N}=\mathbb N\cup\{\infty\}\);
* their actual independent product profile
  
  \[
  \bar\rho:=\bigotimes_{i<4}\mu_i;
  \]
* positive joint Never probability
  
  \[
  q:=\Pr_{\bar\rho}(\mathsf{Never})
    =\prod_{i<4}\mu_i(\{\infty\})>0;
  \tag{4}
  \]
* the literal four-step marginal-replacement ancestry from the original
  realizing family to \(\bar\rho\).

No profit, Nash--Bellman property, or small semantic seam is assumed for
those four marginal replacements.

Then the escape branch has the following exhaustive producer transition.

### First phase: product restart or off-minimum exit

If

\[
 D(\bar\rho)>D_*,
\]

the actual profile \(\bar\rho\) is a literal off-minimum descendant.  A
separate application of the standard actual-reach theorem at \(\bar\rho\)
selects a paid row and enters the off-minimum paid-port waist.  Its observer
need not be one of the four marginal-replacement labels.

If

\[
 D(\bar\rho)=D_*,
\tag{5}
\]

then its exact joint point

\[
 \bar z=(\operatorname{Sem}(\bar\rho),
          \operatorname{Law}(\bar\rho))
\tag{6}
\]

is a complete same-residual minimum source.  This source may be chosen with
literal constant suffix \(\bar\rho\) and words of \(n+1\) all-Continue exact
cap--Nash roots.  No unrelated realizer of \(\bar z\) is introduced.

### Second phase: two releases

From this accepted product source there are actual finite-support profiles
\(\widehat\rho_n\), exact cap--Nash words \(R_n\), dates \(T_n\) beyond every
finite clock of \(\widehat\rho_n\), and literal profiles

\[
 P_n=R_n\star\widehat\rho_n,
 \qquad
 X_n=R_n\star\widehat\rho_n^{[a,T_n]},
 \qquad
 Y_n=R_n\star\widehat\rho_n^{[a,T_n],[b,T_n]},
\tag{7}
\]

where the superscripts cap the displayed player's clock by sure Quit at
\(T_n\).  After one common subsequence:

* \(D(P_n)\to D_*\);
* \(P_n\to X_n\) is one literal complete behavioral replacement of \(a\);
* at the shifted date (|R_n|+T_n), the first target has a pure singleton
  \(\{a\}\) row with unconditional mass bounded below by \(q/4\);
* the first replacement gain is bounded below by \(q\Gamma/4\);
* \(X_n\to Y_n\) is one literal complete behavioral replacement of \(b\),
  changes the same row from \(\{a\}\) to \(\{a,b\}\), and has gain bounded
  below by \(q\Gamma/4\).

The prefix, all earlier finite-law mass, the moving date, and the post-row
tail are common to the two displayed endpoints.

First compactify the singleton targets \(X_n\).  After a strict common
refinement, either their total debt stays a fixed amount above \(D_*\), which
is an off-minimum exit, or their joint limit is a global minimum.  In the
second case their positive moving singleton mass and literal family regenerate
a complete same-residual `singletonMinimum` source.

Apply the nonempty-host moving-mark theorem, proved below, to
\(X_n\to Y_n\) with host \(K=\{a\}\) and outsider \(q=b\).
After a further strict common refinement, exactly one of the following exits
or recursive outputs occurs:

1. a uniformly paid source-supported row strictly before the moving date;
2. a literal pair target whose total debt stays a fixed amount above \(D_*\);
3. a regenerated minimum chord source \(h\) and minimum child \(y\) satisfying
   
   \[
   \varnothing\ne\operatorname{supp}^+(y)
   \subsetneq\operatorname{supp}^+(h),
   \qquad |\operatorname{supp}^+(y)|\le3.
   \tag{8}
   \]

In the third arm, both \(h\) and \(y\) are complete
FinFourMinimumAtomProducer sources with the original hard residual.  Their
causalizations retain the supplied moving profile families and moving marks,
and a paired ancestry wrapper retains the literal prefixed response edge.

### One global producer rank for this lane

Let \(B_0=5\), and for a positive minimum point \(w\) write

\[
 s(w):=|\{i:d_i(w)>0\}|\in\{1,2,3,4\}.
\]

Use the state constructors

* `escapeOrigin`;
* `productMinimum` for the accepted source \(\bar z\);
* `singletonMinimum` for the minimum moving-pair packet and its regenerated
  chord source \(h\);
* `tangentMinimum` for the ordinary renewable support child;
* `exit` for every nonrecursive paid, off-minimum, positive-slope, or
  support-entry output.

Define

\[
 \rho(\mathsf{exit})=0,
 \qquad
 \rho(\mathsf{tangentMinimum}(w))=s(w),
\tag{9}
\]

\[
 \rho(\mathsf{singletonMinimum}(w))=B_0+s(w),
\]

\[
 \rho(\mathsf{productMinimum}(w))=2B_0+s(w),
 \qquad
 \rho(\mathsf{escapeOrigin}(w))=3B_0+s(w).
\tag{10}
\]

The transition constructors are only

\[
\begin{array}{rcl}
 \mathsf{escapeOrigin}&\longrightarrow&
   \mathsf{productMinimum}\text{ or exit},\\
 \mathsf{productMinimum}&\longrightarrow&
   \mathsf{singletonMinimum}\text{ or exit},\\
 \mathsf{singletonMinimum}&\longrightarrow&
   \mathsf{tangentMinimum}\text{ with (8), or exit},\\
 \mathsf{tangentMinimum}(w)&\longrightarrow&
   \mathsf{tangentMinimum}(w')\text{ with }s(w')<s(w),
   \text{ or exit}.
\end{array}
\tag{11}
\]

Every transition strictly decreases \(\rho\).  No constructor returns to a
consumed phase.  After the child in (8), at most two further nonempty strict
support descents are possible.

## Conjecture-facing change

This contraction feeds the maintained quantitative paid-port question.
The all-player-escape output no longer stops at the conditional phrase
"provided the reconstructed product point can be accepted as a current
source."  It has the unconditional producer-level contraction

\[
\boxed{
\begin{array}{c}
\text{reset-rigid all-player escape}\\
 \Longrightarrow\\
 \text{off-minimum product exit}\\
 \quad\text{or}\quad\\
 \text{literal positive-Never product source}\\
 \Longrightarrow\\
\text{paid/off-minimum exit or strict-support minimum child}.
\end{array}}
\tag{12}
\]

The phase tag prevents source regeneration from resetting the subsequent
support-cardinality descent.  The remaining work is terminal: consume the
paid and off-minimum exits and the nonrecursive tangent exits.

## Definitions and assumptions

For a profile with independent private clocks, its terminal law is the law
of the earliest nonempty quitting coalition, together with Never.  A marginal
law on \(\overline{\mathbb N}\) is realized behaviorally by its conditional
hazards.  Finite-support compression means support on finitely many dates
plus Never; it preserves each marginal Never mass exactly and converges in
the complete payoff--cap--law packet.

An exact cap--Nash root against a continuation cap \(B\) is a one-stage
independent product action at which every action used by a player maximizes
that player's Quit-versus-Continue comparison against \(B\).  A word is exact
when each row is exact against the cap of the literal continuation following
it.

A complete minimum source consists of a global-minimum joint point, the hard
residual, a positive finite terminal-law atom, and arbitrarily deep exact
cap--Nash words over a literal realizing suffix family, with that atom
retained at an actual shifted date.

The producer rank (9)--(11) orders construction states.  It is not a payoff
charge and not an order on dates of one play.

## Source correspondence

The incoming source type is `FinFourMinimumAtomProducer` in
[Source.lean](../../Research/Quitting/FinFourProducerAtlas/Source.lean).
The finite-atom theorem at every hard-residual minimum is
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
[TerminalSemanticFinFourMinimumLawFiniteAtom.lean](../../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean).

The singleton moat (3) is
`minimumTerminalSemantic_singletonMargin` in
[TerminalSemanticAuxiliaryNashBudget.lean](../../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean).
The owner and collision partner are supplied respectively by
`QuittingTerminalExploitabilityWitness.exists_terminalGap_le_soloReward` in
[TerminalExploitabilityToggles.lean](../../UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean)
and
`FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
in
[PunishmentNormalAtomicCollisionHandoff.lean](../../UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean).

The exact finite-support late-release construction and the reviewed source
chronology are in
[Fin4 positive-Never late release](../notes/CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md).
Its checked ingredients include the common-quantile compression in
[EscapeAwareQuantileClockHierarchy.lean](../../Research/Quitting/EscapeAwareQuantileClockHierarchy.lean)
and
[QuantileClockCollision.lean](../../MathUE/Probability/QuantileClockCollision.lean),
the finite-cap strategy in
[TerminalSemanticStoppingLawFiniteSplice.lean](../../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteSplice.lean),
and exact cap--Nash root-stack access in
[TerminalSemanticLawCarrierCausalization.lean](../../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean).

The nonempty-host moving-mark theorem is proved in full in Section 4 and
separately recorded in
[Nonempty-host moving-mark minimum chord](../notes/SOCIAL_WEIGHT_REVIEW__NONEMPTY_HOST_MOVING_MARK_MINIMUM_CHORD.md).
Its positive-residual input is
positiveDebt_exists_actualJointReach_paidRow_mem_support in
[ActualReachPaidFirstDisagreement.lean](../../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean).
Its minimum-chord inequality is
quittingTerminalSemanticDebt_responseChord_le in
[MinimumResponseChordLaw.lean](../../Research/Quitting/MinimumResponseChordLaw.lean).
The two-player-host predecessor is Section 17 of
[Oriented pair to renewable chord](../notes/PAIRED_HULL_REVIEW__ORIENTED_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD.md);
it cannot by itself be instantiated at the singleton host used here.
Its complete-cap common-prefix estimate is proved in
[Common prescribed-prefix backward edge](../notes/SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE.md).
The actual-family causalization used there is
`nonempty_sourceFaithfulMinimumCausalization` in
[SourceFaithfulMinimumLawCausalization.lean](../../Research/Quitting/SourceFaithfulMinimumLawCausalization.lean).

The new content is the exact constant-suffix acceptance of the reconstructed
product point, the cardinality-free nonempty-host moving-mark theorem, and
their composition with the two-release construction and one-way phase rank.
Existing escape results did not supply that accepted source transition or
prevent reconstruction from appearing to reset the support rank.

There is an important overlap boundary.  The checked
[arbitrary-clock minimum purification theorem](../formalized/ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md)
already sends any positive-minimum realizing sequence through finite literal
replacement ancestry to the universal off-minimum paid port.  It does not
retain the input law, marked atom, tail, or a renewable rank.  The present
result is therefore not the first producer of an off-minimum descendant.  Its
new content is the exact accepted product source, its fresh two-release
calendar, and the alternative strict-support child inside one nonresetting
producer lane.  These distinctions must be retained when judging the packet's
conjecture-facing value.

## Proof

### 1. The product profile either exits or is a literal minimum point

The reconstructed \(\bar\rho\) is an actual behavioral profile, not merely a
law.  Therefore its joint semantic/law point lies in
\(\mathcal C^{\rm law}\), and global minimality gives

\[
 D(\bar\rho)\ge D_*.
\]

Strict inequality is the first exit.  In the equality case (5), (6) is an
actual global minimum carrying Never mass \(q>0\).

### 2. Literal all-Continue causal source at the product minimum

Apply the finite-atom theorem at the exact point \(\bar z\).  It gives a
nonempty coalition \(S\) and

\[
 m:=\operatorname{Law}(\bar\rho)(S)>0.
\]

The coordinate \(m\) is the sum of nonnegative stage-\(S\) masses.  Choose a
finite cutoff \(K\) for which the mass before \(K\) exceeds \(m/2\), then a
date \(t<K\) with positive stage-\(S\) mass.

By (3), every player strictly prefers Continue to quitting alone against the
all-Continue root at the cap \(B(\bar\rho)\).  Thus deterministic all Continue
is an exact cap--Nash root.  Prefixing it has survival one, creates no terminal
outcome, and leaves every prescribed payoff, unrestricted cap, ordinary law,
and deleted law unchanged.  Hence it remains exact after its own insertion.

For rank \(n\), take the constant suffix \(\bar\rho\), the word of \(n+1\)
all-Continue roots, cutoff \(K\), and mark \(t\).  The full prefixed profile
has debt exactly \(D_*\), and the positive atom occurs at shifted date
\(n+1+t\) with its original mass.  These data explicitly satisfy the causal
minimum-source fields.  Copying the table-level hard residual completes a
FinFourMinimumAtomProducer at \(\bar z\).

This proves the first nonexit transition in (11).  It does not construct an
admissible edge from the old escape source.

### 3. Fresh positive-Never late release

Starting from the accepted source, apply common-quantile finite-support
compression profilewise.  It gives \(\widehat\rho_n\to\bar z\) in complete
semantics and law, preserves every marginal Never atom, and puts every finite
clock below some \(T_n\).

Choose exact cap--Nash words \(R_n\) of increasing length against the literal
suffixes \(\widehat\rho_n\).  If \(c_n\) is their joint Continue product,
exact debt scaling and global minimality give

\[
 {D_*\over D(\widehat\rho_n)}\le c_n\le1.
\]

Therefore \(c_n\to1\).

Choose \(a\) by (1), and cap its clock by sure Quit at \(T_n\).  Since no
finite source clock reaches \(T_n\), source and target differ only on the
joint-Never event.  On that event the target terminal is exactly \(\{a\}\).
Before prefixing, both the singleton mass and \(a\)'s gain are respectively
\(q_n\) and \(q_n r_a(\{a\})\), where \(q_n\to q\).  Prefixing multiplies
both by \(c_n\).  Eventually they are at least \(q/4\) and \(q\Gamma/4\).
The opponents of \(a\) do not change, so \(a\)'s full behavioral cap is
unchanged and its debt drops by exactly the gain.

Now choose \(b\) by (2) and cap its clock at the same \(T_n\).  Conditional
on reaching the row, the first target has the pure singleton action
\(\{a\}\), while the second has the pure pair action \(\{a,b\}\).  Thus the
second gain is exactly

\[
 c_nq_n\bigl(r_b(\{a,b\})-r_b(\{a\})\bigr),
\]

which is eventually at least \(q\Gamma/4\).  Both replacements use the same
literal prefix, earlier calendar, moving date, and post-row tail.  This proves
(7).

### 4. Nonempty-host moving-row theorem

First pass to one common subsequence on which the complete singleton-target
packets \(X_n\) converge and their total debts converge to some
\(L_X\ge D_*\).  If \(L_X>D_*\), eventually the literal late-release targets
are uniformly off minimum, which is an exit.  If \(L_X=D_*\), their joint
limit \(x\) is a global minimum.  The singleton stage at the supplied moving
date has a uniform positive mass, so source-faithful minimum causalization on
this same family and these same marks gives a complete same-residual minimum
source.  This is the singletonMinimum entrance in (11).

The required moving-row result is proved here for every nonempty host, rather
than invoking the existing theorem whose statement fixes a two-player host.
Let

\[
 K=\{a\},\qquad K'=K\cup\{b\}=\{a,b\},
\]

and let \(\ell_n\ge q/4\) be the unconditional reach of the displayed
singleton row in \(X_n\).  Put

\[
 \Delta=r_b(K')-r_b(K)\ge\Gamma,\qquad
 R_n=d_b(Y_n),\qquad e_n=D(Y_n)-D_*.
\tag{13}
\]

The argument below uses only that \(K\ne\varnothing\), \(b\notin K\), and
\(\Delta>0\).

#### 4.1 Exact update, debt, and law

The profiles agree before the moving row.  On reach, the nonempty host
contains a sure quitter under both actions of \(b\), so play terminates at
that row, in \(K\) for \(X_n\) and in \(K'\) for \(Y_n\).  Therefore

\[
 U_b(Y_n)-U_b(X_n)=\ell_n\Delta.
\tag{14}
\]

The opponents of \(b\) are unchanged, so \(B_b(Y_n)=B_b(X_n)\), and hence

\[
 d_b(X_n)=\ell_n\Delta+R_n,\qquad d_b(Y_n)=R_n.
\tag{15}
\]

For fixed \(s\in(0,1)\), let \(H_n^s\) mix only \(b\)'s action at the mark by
probability \(s\) toward the pair endpoint.  The same pathwise coupling gives
the complete law identities

\[
 \operatorname{Law}(Y_n)
 =\operatorname{Law}(X_n)+\ell_n(\delta_{K'}-\delta_K),
\tag{16}
\]

\[
 \operatorname{Law}(H_n^s)
 =\operatorname{Law}(X_n)+s\ell_n(\delta_{K'}-\delta_K).
\tag{17}
\]

All earlier absorption and Never mass are unchanged.  These identities need
one sure-quitting host member, not two.

#### 4.2 Positive residual is strictly earlier

Every nonnegative sequence \(R_n\) has a strict subsequence bounded below by
some \(\rho>0\), or a strict subsequence tending to zero.  In the first arm,
apply positiveDebt_exists_actualJointReach_paidRow_mem_support to the actual
profile \(Y_n\), observer \(b\), and debt floor \(\rho\).  It gives a
source-supported pure-time first-disagreement row with realized gain at least
\(\rho/4\), together with

\[
 \rho\le4M\,\operatorname{OwnSurvival},\qquad
 \rho\le8M\,\operatorname{OppReach},
\]

\[
 \rho^2\le32M^2\,\operatorname{JointReach}.
\tag{18}
\]

This row starts strictly before the moving mark.  Conditional on reaching the
mark, the actual strategy of \(b\) in \(Y_n\) Quits surely.  A pure stopping
time in its induced stopping-law support therefore either stops earlier or
stops at that mark.  If it stops there, it receives \(r_b(K')\).  Every later
finite clock and Never is screened by the sure quitter in the nonempty host
\(K\) and receives \(r_b(K)<r_b(K')\).  Thus a positive improvement cannot
first disagree at or after the mark.  This proves the positive-residual
output in the singleton-host case.

Assume henceforth, after retaining the literal common indices, that
\(R_n\to0\).  Since \(Y_n\) is an actual carrier profile, \(e_n\ge0\).  Pass
again so either \(e_n\ge\eta>0\), giving the quantitative off-minimum target,
or \(e_n\to0\).

#### 4.3 Minimum squeeze and strict support

In the last arm jointly compactify

\[
 \bigl(\operatorname{SemLaw}(Y_n),
       \operatorname{SemLaw}(H_n^s),\ell_n\bigr)
 \longrightarrow (y,h^s,\ell),
\qquad \ell\ge q/4.
\tag{19}
\]

Closedness and \(e_n\to0\) give \(D(y)=D_*\).  For \(i\ne b\), the payoff of
each fixed complete behavioral response is affine in \(s\), so the supremum
over all responses is convex.  For \(i=b\), the opponents are unchanged and
the cap is constant.  Prescribed payoffs are affine.  Therefore

\[
 d_i(H_n^s)
 \le(1-s)d_i(X_n)+s d_i(Y_n)
 \qquad(i<4).
\tag{20}
\]

Global minimality squeezes the sum:

\[
 D_*\le D(H_n^s)
 \le(1-s)D(X_n)+sD(Y_n)\longrightarrow D_*.
\tag{21}
\]

Thus \(D(h^s)=D_*\).  Passing (20) to the common limit, all coordinate
slacks are nonnegative and their sum is zero, so

\[
 d_i(h^s)=(1-s)d_i(x)+s d_i(y)
 \qquad(i<4).
\tag{22}
\]

Equations (15) and (19) give

\[
 d_b(y)=0,\qquad
 d_b(x)=\ell\Delta,\qquad
 d_b(h^s)=(1-s)\ell\Delta>0.
\tag{23}
\]

For \(0<s<1\), (22) implies

\[
 \operatorname{supp}^+(h^s)
 =\operatorname{supp}^+(x)\cup\operatorname{supp}^+(y).
\]

The mover belongs to the source support and not to the target support.
Because \(D(y)=D_*>0\), the target support is nonempty.  Hence

\[
 \varnothing\ne\operatorname{supp}^+(y)
 \subsetneq\operatorname{supp}^+(h^s),
 \qquad |\operatorname{supp}^+(y)|\le3.
\tag{24}
\]

Passing (16)--(17) to the same common limit retains the exact law
displacements at \(K,K'\).

#### 4.4 Copied prefix and source regeneration

The law of \(H_n^s\) has \(K'\)-mass \(s\ell_n\) at the supplied moving mark.
Apply supplied-family source-faithful minimum causalization to this literal
family and these marks.  Let \(W_n\) be its selected nonempty exact
cap--Nash word, let \(c_n\) be joint survival through \(W_n\), and let
\(H_{i,n}\) be survival of all opponents of \(i\).  Put

\[
 A_n=W_n\star H_n^s,\qquad P_n=W_n\star Y_n.
\tag{25}
\]

Causalization gives

\[
 c_n\to1,\qquad H_{i,n}\to1\quad(i<4).
\tag{26}
\]

For every nonempty prescribed word \(W\), behavioral tail \(T\), and player
\(i\), the unrestricted cap satisfies

\[
 \left|B_i(W\star T)
 -\max\{r_i(\{i\}),B_i(T)\}\right|
 \le2M(1-H_i(W)).
\tag{27}
\]

To prove (27), reduce the cap to pure stopping times, including Never.  A
pure time either Quits inside \(W\), coupling on opponent survival to
singleton cash-out, or Continues through \(W\), coupling to the corresponding
tail time.  Outcomes differ only on opponent absorption inside \(W\).
Immediate Quit and a shifted epsilon-optimal tail time give the reverse
estimate.  Thus (27) covers finite early Quit, arbitrarily late Quit,
mixtures, and Never.

At the positive minimum limits, the singleton moat gives

\[
 B_i-r_i(\{i\})\ge D_*>0.
\tag{28}
\]

Therefore the maximum in (27) asymptotically selects the tail cap.
Prescribed-payoff and law coupling, (26), and (28) give

\[
 \operatorname{SemLaw}(A_n)\to h^s,\qquad
 \operatorname{SemLaw}(P_n)\to y.
\tag{29}
\]

The word is prescribed identically at both endpoints, so \(A_n\to P_n\) is
a literal complete \(b\)-strategy replacement.  Exactly,

\[
 U_b(P_n)-U_b(A_n)=c_n(1-s)\ell_n\Delta.
\tag{30}
\]

The two profiles have the same opponents for \(b\), hence equal complete
caps.  Exact cap--Nash debt scaling on the source side gives

\[
 d_b(A_n)=c_n\bigl((1-s)\ell_n\Delta+R_n\bigr).
\]

Subtracting (30) yields

\[
 B_b(P_n)=B_b(A_n),\qquad d_b(P_n)=c_nR_n\to0.
\tag{31}
\]

At the shifted mark \(|W_n|+t_n\), the target has exact \(K'\)-mass
\(c_n\ell_n\), eventually at least \(q/8\).  Tail-reindex once and causalize
this actual target family at its shifted marks.  Copy the incoming hard
residual.  This regenerates complete minimum sources at \(h^s\) and \(y\).
A paired wrapper stores the two causalizations, the actual families
\(A_n,P_n\), their literal replacement, (29)--(31), and the shifted marked
mass.  The ordinary producer itself is not claimed to contain the incoming
edge.

Equations (17), the off-minimum split, and (23)--(30) prove all three
nonempty-host outputs, including (8).

### 5. The phase rank is well founded

Since \(1\le s(w)\le4\), the four nonterminal phase ranges are

\[
\begin{array}{c|c}
\text{phase}&\text{rank range}\\ \hline
\mathsf{tangentMinimum}&1,\ldots,4\\
\mathsf{singletonMinimum}&6,\ldots,9\\
\mathsf{productMinimum}&11,\ldots,14\\
\mathsf{escapeOrigin}&16,\ldots,19.
\end{array}
\]

Every one-way phase transition strictly lowers rank even without comparing
supports.  Inside the final tangent phase, strict support inclusion lowers
the rank directly.  The transition type has no constructor returning to an
earlier phase, so the canonical product restart cannot be repeated after a
support child.  The child begins with support at most three, leaving at most
two further strict nonempty support drops.

## Boundary tests

1. **Zero Never mass.**  If \(q=0\), neither release has a positive mass or
   gain floor.  The theorem is deliberately restricted to the all-player
   escape arm \(q>0\).
2. **Off-minimum reconstructed product.**  If \(D(\bar\rho)>D_*\), the
   all-Continue source construction is not invoked.  Treating the product as
   a minimum would be false.
3. **Zero minimum.**  If \(D_*=0\), the singleton moat need not be strict and
   exact root-stack survival need not tend to one.  Positive minimum is
   essential.
4. **No finite atom.**  Positive Never alone does not give a retained earlier
   row.  The hard-residual finite-atom theorem is used at the same exact
   product point.
5. **Arbitrary dense finite clocks.**  Semantic density alone can lose the
   product law and its Never mass.  The proof uses profilewise common-quantile
   compression, which preserves the marginal Never coordinates.
6. **Root exactness.**  The word \(R_n\) is exact against
   \(\widehat\rho_n\), not against either released target.  The released
   profiles are legal unilateral targets, not new Nash--Bellman states.
7. **Old passport.**  The four marginal replacements leading to
   \(\bar\rho\) can have macroscopic law and cap seams.  Compact equality of
   the displayed product point does not transport an old marked row, charge,
   or continuation tail.
8. **Rank reset.**  Allowing an arbitrary outer-atlas edge from a tangent
   child back to a fresh escape origin would invalidate (11).  Such an edge
   is not among the proved transition constructors.
9. **Exact two-release calculation.**  Take four source clocks equal to
   Never, choose a finite \(T\), and suppose
   \(r_a(\{a\})=\Gamma\) and
   \(r_b(\{a,b\})-r_b(\{a\})=\Gamma\).  Capping \(a\) at \(T\) changes
   Never to the singleton with mass one and gain \(\Gamma\); then capping
   \(b\) at the same date changes the singleton to the pair with mass one and
   gain \(\Gamma\).  This local test verifies both exact row identities.  It
   is not asserted to be a positive-minimum hard-residual game.
10. **Empty host.**  The nonempty-host theorem is sharp.  If \(K=\varnothing\),
    Continue at the marked date need not absorb; a better receiving clock may
    live entirely in the later tail, so the positive residual need not
    localize strictly before the mark.
11. **Join orientation.**  Section 4 treats an outsider \(b\notin K\) joining
    a nonempty host.  It does not claim the same formulas for an insider
    leaving \(K\).

## Adapter and consumer

The actual-data adapter is the all-player-escape output of the reset-rigid
source analysis.  It supplies the four marginal limits, their actual product
profile, and the positive joint-Never coordinate.  The theorem tests the
actual product debt, constructs a complete source at that exact point in the
equality arm, and generates every later prefix, row, mark, and response
freshly from the product source.

The first nonrecursive arm is first a literal off-minimum product descendant;
a separately selected actual-reach paid row at that descendant enters the
standard off-minimum paid-port waist.  Its observer need not match the
four-step ancestry.
The positive-residual moving-pair arm enters the paid-cap waist.  The minimum
arm enters the existing renewable tangent trace with a strict support child.
These are producer-level contractions.  No terminal consumer for those exits
is claimed here.

The old escape passport is not an input to any downstream transition after
the product restart.  Consequently the absence of a profitable old-to-new
edge does not invalidate the producer rank, but it also cannot be used in a
chronological near-return.

## Lean handoff

Suggested new structures and declarations:

    FinFourEscapeProductRestart
    FinFourEscapeProductRestart.product_offMinimum_or_minimum
    FinFourEscapeProductRestart.minimumSource
    FinFourPositiveNeverTwoReleasePacket
    FinFourPositiveNeverTwoReleasePacket.singleton_gain
    FinFourPositiveNeverTwoReleasePacket.pair_gain
    QuittingNonemptyHostMovingMarkPacket
    QuittingNonemptyHostMovingMarkPacket.dispatch
    QuittingNonemptyHostMovingMarkPacket.positiveResidual_strictEarlier
    QuittingNonemptyHostMovingMarkPacket.minimumChord_support_lt
    FinFourResetRigidProducerState
    FinFourResetRigidProducerState.rank
    FinFourResetRigidProducerTransition
    FinFourResetRigidProducerTransition.rank_lt

The minimum-source constructor should use the literal constant profile
\(\bar\rho\), a finite atom selected at the same joint point, and deterministic
all-Continue words.  It must expose that the roots have survival one and that
the suffix profile is definitionally the supplied product profile.

The two-release packet should reuse the profilewise common-quantile
compression and finite-cap identities from the reviewed positive-Never
packet.  It must keep separate fields for root exactness at the source and
the merely legal released targets.

The nonempty-host adapter must quantify over
\(\varnothing\ne K\) and \(q\notin K\), not over a two-player host.  Its
strict-earlier proof must use the sure host member exactly as in Section 4.2.
The chord and copied-prefix parts should reuse the supplied-family
causalization and paired ancestry wrapper.  The regenerated source points
must copy the incoming hard residual, while their literal profile families
and moving marks remain those in (7).

The rank theorem should be proved only for the inductive transition type in
(11).  Do not add a field asserting an arbitrary outer-atlas transition
decreases rank.

## Scope and nonclaims

* This is ordinary mathematics, not yet a combined Lean declaration.
* It contracts the all-player-escape branch reached from reset rigidity; it
  does not by itself eliminate every reset-rigid source.
* The old escape source and the product source are not joined by a profitable,
  Nash--Bellman, punishment-floor, or vanishing-seam edge.
* No old marked atom, charge, deleted-law passport, or post-mark tail is
  transported across the product restart.
* The late singleton and pair releases are full legal behavioral
  replacements, not exact temporal Nash--Bellman rows.
* The paid, off-minimum, positive-slope, support-entry, and other tangent
  exits are not consumed.
* The rank is global only for the explicitly defined one-way producer lane.
  It is not a rank on arbitrary returns of the outer atlas.
* The universal arbitrary-clock purification already reaches the off-minimum
  paid-port waist without this structured restart; no novelty is claimed for
  that bare endpoint.
* No uniform-equilibrium payoff or counterexample is constructed.

## Lean formalization record

Pre-formalization packet SHA-256:
`7f51c351e295c9ba381a276d433b6ff732b1dc7ec4bb58009d34c57818e7ab15`.

The checked production and Research surfaces were integrated in commit
`1733c4b8e388c3ec587a16d3d3cbeda42ac92063`.  The audited reset scratch used
manifest SHA-256
`857a00c337f9ddfdb23b13b30fbaae7d0872bfa926afd20fc0eaf91e355d1cf7`;
its canonical relative-path-sorted six-source composite is
`91648224695c75e75e1c245ca780ba0798d9fedf8b0f3a6f6480d813849c1f67`.

The low production owners are
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveNeverTwoRelease.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockFreshRelease.lean`.
They expose `QuittingPositiveNeverTwoRelease`, its exact singleton and pair
gain identities, `stoppingLaw_survival_eq_none_of_isFiniteClock`, and
`quittingPositiveNeverTwoRelease_of_isFiniteClock`.

The Research owners
`PositiveNeverQuantileTwoRelease.lean`, `EscapeProductRestart.lean`,
`ResetRigidEscapeSupportContraction.lean`, and `ResetRigidProducerRank.lean`
contain the checked higher compiler.  Its principal declarations are
`FinFourPositiveNeverReleaseInput`, `FinFourEscapeProductRestart`,
`FinFourEscapeProductRestart.MinimumRestart.sourceAtProduct`,
`finFourResetRigidEscape_productExit_or_singletonExit_or_supportContraction`,
`FinFourResetRigidProducerTransition.rank_lt`, and
`resetRigidMovingSupportRenewal_furtherDescentCount_le_two`.  The minimum
restart constructs the literal product source with its own causal suffix atom;
the equality-arm cap bound is derived rather than assumed.

Evidence seals:

- **M:** PASS.  The product restart, exact two-release identities, moving-mark
  alternative, support contraction, and one-way rank match the reviewed
  mathematics and constants.
- **L:** PASS.  The production leaves are reachable from the production
  umbrellas and generated axiom audit; the Research compiler is checked with
  warnings as errors and representative axiom prints.
- **A:** absent at the escape origin.  The compiler consumes a supplied
  `FinFourEscapeProductRestart`; it does not construct the all-player-escape
  passport or prove that every reset-rigid source enters this lane.
- **C:** branch-local only.  The off-minimum and positive-residual alternatives
  attach to the checked paid-port and moving-support waists, while the minimum
  alternative supplies the checked support-contracted renewal/rank lane.  No
  terminal consumer is proved.

The formalization does not transport the old marked row, charge, deleted-law
passport, or continuation tail across the restart.  It does not turn the
released targets into Nash--Bellman states, rank arbitrary outer-atlas returns,
or construct a uniform-equilibrium payoff or counterexample.
