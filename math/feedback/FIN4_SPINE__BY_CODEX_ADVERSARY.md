# Adversarial mathematical review of FIN4_SPINE.md

Reviewer: Codex Adversary

## Verdict

The normal unique-persistent-spine theorem is **correct as ordinary
mathematics**. I found no counterexample under its punishment-normality
hypothesis. The Bellman recursion, tail estimate, solo reprojection,
unrestricted outsider-cap formula, finite punishment seam, and
terminal-to-uniform quantifiers all survive direct reconstruction.

One source-facing correction is mandatory. The cited declaration
quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps
forgets the target payoff and its generic consumer yields only the existence
of some uniform-equilibrium payoff. It does not by its type prove that the
target is \(R=r(\{p\})\). The correct checked target-preserving consumer is
isUniformEquilibriumPayoff_soloReward_of_approximate_caps in
UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean.
Alternatively, the note's explicit estimates feed
quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
directly. This is a citation and Lean-handoff defect, not a counterexample to
the theorem.

The source also has malformed math markup, including === and the corrupted
norm/sum in (12). I reviewed the uniquely determined intended equalities.
Those displays need repair before export.

This is an ordinary-mathematics review. The two new analytic adapters are not
Lean-checked here.

## Exact claim and spine definition

The relevant repository predicate is
IsCanonicalExactQuittingNashBellmanSpine in
UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean:

\[
  |v_{t,i}|\le K,\qquad
  v_t=F_{x_t}(v_{t+1}),\qquad
  x_t\text{ is exact root Nash against }v_{t+1}.
\]

Here

\[
  q_{t,i}:=(x_{t,i}(\mathrm{Quit})).\mathrm{toReal}.
\]

The theorem assumes one player \(p\) has
\(\sum_t q_{t,p}=\infty\), every outsider has a finite hazard sum, and

\[
  \operatorname{Pun}_p(r)\le r_p(\{p\}).
\]

It concludes that the whole singleton reward vector \(R=r(\{p\})\) is a
uniform-equilibrium payoff.

## 1. The recursion and tail estimate are exact

Let

\[
  a_t=\prod_{j\ne p}(1-q_{t,j}),\qquad
  c_t=1-a_t,\qquad
  s_t=\sum_{j\ne p}q_{t,j}.
\]

The number \(c_t\) is the probability that at least one outsider Quits in
root \(x_t\). The product union bound gives

\[
  0\le c_t\le s_t,\qquad \sum_t c_t<\infty.
\]

On the complementary event, either \(p\) Quits and the terminal vector is
\(R\), or everyone Continues and the successor vector is \(v_{t+1}\). If
\(G_t\) is the unnormalised payoff contribution from outcomes containing an
outsider, Bellman gives

\[
  v_t=a_t\bigl((1-q_{t,p})v_{t+1}+q_{t,p}R\bigr)+G_t,
  \qquad \|G_t\|_\infty\le Kc_t.
\]

For \(d_t=v_t-R\),

\[
  d_t=a_t(1-q_{t,p})d_{t+1}+e_t,\qquad
  e_t=G_t-c_tR,\qquad
  \|e_t\|_\infty\le2Kc_t.
\]

Iteration gives the note's formula (10). For each fixed \(t\),

\[
  \prod_{u=t}^{T-1}a_u(1-q_{u,p})
  \le \exp\!\left(-\sum_{u=t}^{T-1}q_{u,p}\right)\longrightarrow0.
\]

The bounded terminal term therefore vanishes, while every remaining weight
is at most one. Hence

\[
  \boxed{
  \|v_t-R\|_\infty
  \le2K\sum_{s=t}^{\infty}c_s
  \le2K\sum_{s=t}^{\infty}s_s.}
\]

Thus \(v_t\to R\). No payoff sign is used.

## 2. Solo reprojection is valid

At an index with \(q_{t,p}>0\), let \(y_t\) retain \(p\)'s marginal from
\(x_t\) and prescribe Continue surely to every outsider. For \(i\ne p\),
forcing \(i\) to Quit gives

\[
  A_{t,i}=(1-q_{t,p})r_i(\{i\})
    +q_{t,p}r_i(\{i,p\}).
\]

Exact root Nash and Bellman imply

\[
  U_i(x_t[i\leftarrow Q];v_{t+1})\le v_{t,i}.
\]

Couple this forced-Quit root with \(y_t[i\leftarrow Q]\). They can differ
only if a player outside \(\{p,i\}\) Quits. That event has probability at
most \(s_t\), and two terminal rewards differ by at most \(2K\). Therefore

\[
  A_{t,i}\le v_{t,i}+2Ks_t
  \le R_i+\eta_t,\qquad
  \eta_t:=\|v_t-R\|_\infty+2Ks_t\longrightarrow0.
\]

This does not assume that \(y_t\) remains root Nash. It transports only the
forced-Quit comparison needed for the outsider cap.

## 3. The unrestricted outsider cap is exactly a two-endpoint maximum

This assertion is correct because the same solo root \(y_t\) is repeated
stationarily and \(q:=q_{t,p}>0\). It is not a statement about arbitrary
nonstationary solo environments.

For a pure stopping date \(n\), player \(p\) either Quits earlier, giving
\(R_i\), or survives to date \(n\), where the conditional Quit value is
\(A_{t,i}\). Thus

\[
  U_i(T_i=n)
  =\bigl(1-(1-q)^n\bigr)R_i+(1-q)^nA_{t,i}.
\]

Never gives \(R_i\), because \(p\)'s geometric clock is proper. The general
stopping-law mixture identity then makes every time-dependent randomized
behavioral deviation worth

\[
  (1-\theta)R_i+\theta A_{t,i}
  \quad\text{for some }\theta\in[0,1].
\]

Never and immediate Quit attain the endpoints, so

\[
  B_i(y_t^\infty)=\max\{R_i,A_{t,i}\}\le R_i+\eta_t.
\]

This matches quittingStationaryUnilateralCap_solo_other and
quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix in
UniformEquilibrium/Quitting/Boundary/Exceptional/TailFallback.lean and
UniformEquilibrium/Quitting/Stationary/SingletonStationaryRoot.lean. The
behavioral mixture identity is
quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime in
UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean.

Positivity of \(q\) is essential: at \(q=0\), waiting for \(p\) need not
deliver \(R_i\). The divergent owner clock supplies infinitely many positive
indices, so the note is safe.

## 4. The finite punishment seam handles negative singleton payoff

Repeat one selected positive solo hazard \(q\) for \(N\) dates and then
install an actual punishment profile \(\pi\) with

\[
  B_p(\pi)\le\operatorname{Pun}_p(r)+\delta\le R_p+\delta.
\]

Such a tail exists for every \(\delta>0\). The exact source facts are
quittingPunishmentValue_eq_stationaryPunishmentValue in
UniformEquilibrium/Quitting/Stationary/MinMax.lean and
exists_stationaryRoot_cap_lt_punishmentValue_add in
UniformEquilibrium/Quitting/Paths/SupportWitnessIndividualRational.lean.

Let \(\rho=(1-q)^N\). The prescribed payoff differs from \(R\) only upon
reaching the tail:

\[
  \|U(\sigma)-R\|_\infty\le2K\rho.
\]

For an outsider deviation, the finite-prefix environment and the infinite
stationary solo environment differ only after date \(N\). Reaching a
difference requires \(p\) to survive the prefix, an event of probability at
most \(\rho\) even under that deviation. Its gain is therefore at most
\(\eta_t+4K\rho\).

For the owner, quitting in the prefix gives exactly \(R_p\). Conditional on
reaching the tail, the restriction of any complete deviation is an arbitrary
behavioral reply against \(\pi\), worth at most \(R_p+\delta\). Thus

\[
  U_p(\sigma[p\leftarrow\tau_p])\le R_p+\delta
\]

for every \(\tau_p\), including Never. This argument is valid when
\(R_p<0\): it never multiplies an inequality by a sign-indefinite payoff.

### Sharp counterexample if punishment-normality is removed

Take a one-player quitting game with \(r_p(\{p\})=-1\). Put \(v_t=-1\) for
all \(t\), and let every \(x_t\) Quit with probability \(1/2\). Quit and
Continue both have value \(-1\), so this is an exact bounded Nash--Bellman
spine and \(p\) is persistent. The stationary solo profile has prescribed
terminal payoff \(-1\), but Never gives zero. Moreover
\(\operatorname{Pun}_p(r)=0>-1\), since there are no opponents who can punish
\(p\). Hence \(r(\{p\})=-1\) is not the asserted uniform payoff.

This falsifies the theorem with punishment-normality deleted and also
falsifies the tempting infinite-stationary shortcut. It does not contradict
the note; it shows the hypothesis and the finite actual tail are necessary.

## 5. Terminal-to-uniform quantifiers

For every requested \(\varepsilon>0\), the note's choices give

\[
  \operatorname{Exploit}(\sigma)<\varepsilon,\qquad
  \|U(\sigma)-R\|_\infty<\varepsilon.
\]

The target \(R\) is fixed across accuracies, although the selected spine
index, prefix length, and punishment vary. These are exactly the quantifiers
of
quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
in
UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean.
The direct terminal-to-uniform conclusion is therefore valid.

There is a shorter checked handoff. Enumerate increasing indices \(t_n\) with
\(q_{t_n,p}>0\), and put

\[
  h_n=x_{t_n,p},\qquad e_n=\eta_{t_n}.
\]

Then \(e_n\ge0\), \(e_n\to0\), and

\[
  \operatorname{Cap}_i(\operatorname{SoloRoot}(p,h_n))
  \le R_i+e_n\qquad(i\ne p).
\]

Together with punishment-normality, these are precisely the hypotheses of
isUniformEquilibriumPayoff_soloReward_of_approximate_caps. Its conclusion is
that \(R\) itself is a uniform-equilibrium payoff. It requires neither
\(q_{t_n,p}\to0\) nor a uniform positive lower bound on those hazards.

By contrast, QuittingStationarilyGeneratedApproximateEquilibria stores only
existence of approximate equilibria, not convergence of their payoffs to
\(R\). Its generic consumer cannot alone prove equation (31) with that
specific target.

## 6. Fin4 consequence

After unfolding IsQuittingNormalPlayer, the field
FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal says

\[
  \forall p,\quad \operatorname{Pun}_p(r)\le r_p(\{p\}).
\]

The declarations are in
UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean
and UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean.

Under the no-uniform-payoff hypothesis, the theorem therefore contradicts
every hypothetical exact bounded one-persistent spine. The conclusion that
every such spine has either zero or at least two persistent labels is
correct. If a separate selection supplies a nonempty persistent set,
finiteness then supplies two fixed persistent labels on that same spine. The
note correctly leaves nonempty-persistence selection open.

## Mandatory revisions

1. Replace the target-forgetting stationarily-generated citation by
   isUniformEquilibriumPayoff_soloReward_of_approximate_caps, or invoke the
   fixed-target terminal consumer explicitly.
2. In the Lean handoff, enumerate the positive owner-hazard indices and pass
   hazard \(n=x_{t_n,p}\) and error \(n=\eta_{t_n}\) to the checked solo-cap
   theorem. The third proposed new adapter is only this instantiation.
3. State the exact spine predicate and the .toReal convention for \(q_{t,i}\);
   repair displays (6), (8), (10), and (12), plus the Markdown delimiters.
4. Keep the two-endpoint assertion explicitly restricted to the repeated
   stationary solo root.

Subject to these revisions, the note is a valid positive answer to equivalent
output 4 of questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md.

## Source declarations inspected

- IsCanonicalExactQuittingNashBellmanSpine in
  UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean.
- quittingRootSuccessorPayoff in
  UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean.
- quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime in
  UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean.
- quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix,
  quittingStationaryUnilateralCap_solo_other, and
  quittingTerminalPayoff_soloStationary in
  UniformEquilibrium/Quitting/Stationary/SingletonStationaryRoot.lean and
  UniformEquilibrium/Quitting/Boundary/Exceptional/TailFallback.lean.
- quittingPunishmentValue, quittingBestReplyValue_stationary, and
  quittingPunishmentValue_eq_stationaryPunishmentValue in
  UniformEquilibrium/Quitting/Stationary/MinMax.lean.
- exists_stationaryRoot_cap_lt_punishmentValue_add in
  UniformEquilibrium/Quitting/Paths/SupportWitnessIndividualRational.lean.
- isUniformEquilibriumPayoff_soloReward_of_approximate_caps in
  UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean.
- quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps
  and QuittingStationarilyGeneratedApproximateEquilibria in
  UniformEquilibrium/Quitting/Classification/Existence/NoHarmSingletonGenerated.lean
  and StationarilyGeneratedBranch.lean.
- quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
  in
  UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean.
- IsQuittingNormalPlayer in
  UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean.
- FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal and its
  no-uniform-payoff producer in
  UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean.

No literature theorem is used.
