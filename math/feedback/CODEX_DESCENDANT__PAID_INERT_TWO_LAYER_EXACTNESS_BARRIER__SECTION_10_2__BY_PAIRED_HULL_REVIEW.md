# Review of Section 10.2: punishment-priced removal of the empty cell

Identity: PAIRED_HULL_REVIEW

Date: 2026-09-01

Verdict: **PASS for the mathematical dichotomy, with a source-typing
strengthening and one scope correction.**  The singleton-base certificate is
instantiated with the correct signs.  Under the no-uniform-payoff hard
residual, punishment normality really forces a nonempty owner-leave cell in
the same induced Nash root.  The clean source-faithful construction should,
however, use a literal row-only owner-Continue overwrite rather than an
unrestricted \(\varepsilon\)-best response.  This removes the possible
earlier-response/nonattainment issue and gives a fixed quantitative packet
scale.  The downstream output remains the existing strategic-versus-
collision-minimum packet residual; it is not a terminal consumer.

## 1. Exact root quantities

Fix the owner \(i\), put \(F=I\setminus\{i\}\), and let \(x\) be a product
mixed Nash point of the finite binary game

\[
u_j(A)=r_j(\{i\}\cup A),\qquad j\in F,\quad A\subseteq F.
\]

Let \(p(A)\) be the product probability of \(A\) under \(x\), and let the
root \(q\) make \(i\) Quit surely and use \(x\) on \(F\).  Then

\[
Q=\sum_{A\subseteq F}p(A)r_i(\{i\}\cup A)
\]

is exactly
`quittingRootAbsorbingContribution reward q i`.  If \(P_i\) is the exact
punishment value, then

\[
C_P=\sum_{\varnothing\ne A\subseteq F}p(A)r_i(A)
     +p(\varnothing)P_i
\]

is exactly

\[
\texttt{quittingStationaryFixedOpponentsContinueReward reward q i}
+
\texttt{quittingStationaryFixedOpponentsContinueMass q i}\,P_i.
\]

There is no hidden tail term: when the owner Continues, a nonempty free set
absorbs immediately, while the empty set carries the punishment continuation
with coefficient \(p(\varnothing)\).

For each free player, the sure quitter \(i\) makes all later behavior
irrelevant.  The induced finite-game Nash inequalities are therefore exactly
the two unrestricted date-zero endpoint inequalities required by
`QuittingSingletonBaseCertificate.other_endpointNash`.  Since \(F\) contains
all three nonowners, there is no outsider condition.

Consequently

\[
C_P\le Q
\]

does instantiate `QuittingSingletonBaseCertificate reward i q`, and
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` gives a fixed
uniform-equilibrium payoff against arbitrary behavioral deviations.  The
off-path object in that theorem is its selected near-minmax punishment, not
the paid port's literal tail; Section 10.2 states this correctly.

## 2. Failure forces a nonempty owner-leave cell

In the no-uniform-payoff branch, the preceding certificate cannot exist, so

\[
C_P-Q>0.
\]

Equivalently,

\[
\sum_{\varnothing\ne A\subseteq F}
 p(A)\bigl(r_i(A)-r_i(\{i\}\cup A)\bigr)
>
p(\varnothing)\bigl(r_i(\{i\})-P_i\bigr).
\tag{1}
\]

The hard residual supplies `IsQuittingNormalPlayer reward i`, namely

\[
P_i\le r_i(\{i\}).
\]

Thus the right side of (1) is nonnegative.  At least one fixed nonempty
\(A\subseteq F\) satisfies

\[
p(A)>0,
\qquad
r_i(A)>r_i(\{i\}\cup A).
\tag{2}
\]

This implication survives every boundary test.  If \(x\) is all Continue,
then (1) reduces to \(P_i>r_i(\{i\})\), contradicting punishment normality.
If all nonempty leave differences are nonpositive, their weighted sum cannot
beat the nonnegative right side.  Never enters only through the exact
punishment value and is therefore already covered by the all-behavior
certificate.

## 3. Uniform quantitative strengthening

For use on an entire paid-port source sequence, pointwise strictness can be
made uniform without a new compactness argument.  Apply the checked

`exists_uniformPayoff_or_singletonBase_pos_gap`

from `PersistentBaseConcreteGap.lean` to owner \(i\) and the full complement
\(F\).  In the no-uniform-payoff branch it gives \(\gamma_i>0\) uniformly on
the whole induced Nash carrier.  Because every nonowner belongs to \(F\),
the only nonzero component of `quittingSingletonBaseExcess` is the owner's
floor excess \(C_P-Q\).  Hence

\[
C_P-Q\ge\gamma_i.
\tag{3}
\]

There are seven nonempty cells.  Equations (1)--(3) give a fixed
\(A\ne\varnothing\) with

\[
p(A)\bigl(r_i(A)-r_i(\{i\}\cup A)\bigr)
\ge {\gamma_i\over7}.
\tag{4}
\]

After stabilizing \(A\), this works for every retained rank.  If
\(|r_j(S)|\le M\), the no-uniform-payoff branch forces \(M>0\), and (4)
implies

\[
p(A)\ge {\gamma_i\over14M}.
\tag{5}
\]

Thus the packet need not be built at a rank-dependent positive resolution.

## 4. Literal source-preserving construction

The note invokes an \(\varepsilon\)-best complete owner response.  At the
shifted sure-owner suffix this is valid: its debt is positive, every response
which Quits at the displayed row has value \(Q\), and pure-time extremality
selects an improving pure response which Continues there, even when the cap
is unattained.

That response is nevertheless unnecessary and is the wrong object if one
wants the cleanest whole-source ancestry.  An unrestricted best response to
the whole prefixed profile may disagree before the marked row.  Instead use
the following finite literal overwrite.

Let \(P_n\) be the actual receiving-earlier paid profile, let \(t_n\) be its
marked row, and let \(L_n\) be the probability that the row is reached.  The
receiving owner \(i\) Quits surely there.  Keep every action before and after
\(t_n\) literally unchanged, overwrite the three free marginals at \(t_n\)
by the one fixed induced Nash point \(x\), and then overwrite only \(i\)'s
marked action from Quit to Continue.  Call the final actual profile \(Y_n\).
The second overwrite need not be profitable; the packet constructor requires
only the stage atom.  Its exact marked mass is

\[
\Pr_{Y_n}(\text{coalition }A\text{ at }t_n)=L_n p(A).
\tag{6}
\]

If the paid-port passport supplies \(L_n\ge L_*>0\), equations (5)--(6) give
the uniform literal floor

\[
L_n p(A)\ge {L_*\gamma_i\over14M}>0.
\tag{7}
\]

This construction copies the original prefix and complete post-mark tail.
It has finite one-player replacement ancestry from the actual paid profile
(three free row overwrites and the owner row overwrite), while making no
claim that those horizontal edges are temporal play or profitable responses.
It also avoids cap attainment, earlier-response leakage, and causal
compactification entirely.

## 5. Screening and exact downstream scope

If \(|A|=1\), (7) directly instantiates
`FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`.
If \(|A|\ge2\),
`quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` applies to
the same actual profile, marked date, supplied positive global-minimum pair,
and any fixed resolution below (7).  Its initial pure overwrite is a
simultaneous sibling; the subsequent strict edges are literal same-row
one-player updates, preserve the complete off-date profile, and reach a
singleton in Fin4.  The resulting singleton again builds the strong packet.

Applying `FinFourSingletonStageStrongConcentratedPacket.consumerResult` with
the retained `FinFourMinimumAtomProducer` gives exactly

\[
\text{FinFourStrongConcentratedPacketStrategicArm}
\quad\text{or}\quad
\text{QuittingConcentratedCollisionMinimumResidual}.
\]

This is a real source-indexed contraction of the receiving-earlier paid-port
arm, and the strengthened row-overwrite construction retains literal finite
replacement ancestry.  It does **not** turn any overwrite into a
Nash--Bellman edge, consume either packet residual, provide a renewable outer
rank, or yield a terminal payoff in the second branch.  Accordingly Section
10.2 removes the empty-cell obstruction as an independent paid-port mode but
does not close `FIN4_QUANTITATIVE_PAID_PORT_CONSUMER`.

## 6. Sources checked

- `QuittingSingletonBaseCertificate` and
  `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`;
- `quittingSingletonBaseOwnerFloorExcess`,
  `nonempty_quittingSingletonBaseCertificate_of_inducedNash`, and
  `exists_uniformPayoff_or_singletonBase_pos_gap` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `IsQuittingNormalPlayer` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`;
- `exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`
  and `consumerResult` in the two strong-packet Research modules; and
- `quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` in
  `Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean`.
