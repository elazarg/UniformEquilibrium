# Opponent-tight terminal-semantic realization

Authors: CHATGPT_EXTERNAL

Independent reviews:

- [Ramsey review](../feedback/POS_DEBT_REAL__BY_CODEX_RAMSEY.md)
- [Euler falsification review](../feedback/CHATGPT_EXTERNAL__OPPONENT_TIGHT_POSITIVE_MINIMUM_REALIZATION__BY_CODEX_EULER.md)

## Exact statement

Let \(I\) be a finite player type with \(2\le |I|\), and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table, with infinite all-Continue play paying
zero. For a behavioral profile \(\sigma\), write

\[
\operatorname{Sem}(\sigma)=(U(\sigma),B(\sigma)),
\qquad
D(U,B)=\sum_i(B_i-U_i),
\]

where \(B_i\) is the supremum over all unilateral behavioral deviations.

Let \(\sigma_n\) be actual behavioral profiles such that

\[
\operatorname{Sem}(\sigma_n)\longrightarrow z=(u,b).
\]

View each player's complete stopping law as a probability measure on

\[
\overline{\mathbb N}=\operatorname{WithTop}\mathbb N
\]

with its one-point compactification topology. After passing to a subsequence,
assume every law \(\mu_i^n\) converges weakly to \(\mu_i\). Let
\(\sigma_\infty\) be the actual behavioral profile reconstructed from the
limiting laws, and let \(T_i^n\) be the independent latent stopping times.
Put

\[
M_{-i}^n=\min_{j\ne i}T_j^n.
\]

### Theorem A: opponent-tight realization

If

\[
\forall i,\qquad
\lim_{H\to\infty}\limsup_{n\to\infty}
\Pr(M_{-i}^n>H)=0, \tag{OT}
\]

then

\[
\boxed{\operatorname{Sem}(\sigma_\infty)=z.}
\]

This includes simultaneous convergence of every prescribed payoff and every
best-response cap against the unrestricted behavioral strategy class.

### Theorem B: two proper clocks

Call \(\mu_i\) proper when
\(\mu_i(\{\infty\})=0\). If two distinct limiting laws are proper, then (OT)
holds and \(z\) is attained by \(\sigma_\infty\).

Consequently, on every fixed compactified realizing subsequence of a
nonattained semantic point, at most one limiting law is proper. On that
subsequence there are a player \(i\) and a constant \(\kappa>0\) such that

\[
\forall H,\qquad
\limsup_n
\Pr(T_j^n>H\text{ for every }j\ne i)\ge\kappa. \tag{1}
\]

The player and constant may depend on the selected subsequence. Equation (1)
is a common late-or-Never event in the approximants, not a claim that their
literal Never atoms are positive.

### Theorem C: one proper clock at a positive global minimum

Assume

\[
D(z)=D_*:=\min_{y\in K_r}D(y)>0,
\]

where \(K_r\) is the compact terminal-semantic carrier. Suppose the selected
law limit has exactly one proper law, belonging to player \(k\). Let

\[
\widehat\sigma=\sigma_\infty,\qquad
\widehat b_k=B_k(\widehat\sigma),\qquad
q_{-k}=\prod_{j\ne k}\mu_j(\{\infty\})>0,
\qquad s_k=r_k(\{k\}).
\]

Then

\[
U(\widehat\sigma)=u,\qquad
B_j(\widehat\sigma)=b_j\quad(j\ne k),\qquad
\widehat b_k\ge b_k.
\]

If \(z\) is not attained, then

\[
\boxed{
s_k<0,\qquad
0<\widehat b_k-b_k\le -q_{-k}s_k.} \tag{2}
\]

The excess cap at the limiting actual profile is Never; every finite pure
quitting time has value at most \(b_k\).

Thus, for each selected compactified realizing subsequence of a nonattained
positive global minimum, exactly one of these law-limit arms remains:

1. every limiting law has a positive Never atom; or
2. exactly one law is proper and the negative-singleton Never jump (2) occurs.

If all singleton rewards are nonnegative, only the first arm is possible.

## Conjecture-facing change

The maintained positive-minimum frontier supplies actual behavioral profiles
converging semantically to every minimum carrier point, but explicitly does
not realize that point by one profile. This blocks direct use of an attained
minimum source in the paid-port and Fin4 hard-residual routes.

The named live seams narrowed here are
[Paid admissible payoff near-return](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md)
and
[Fin4 hard-residual semantic closure](../questions/FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md).
Both identify nonattainment of a minimum source as an obstruction; neither
currently has a consumer for the residual escape arms below.

Theorems A--C strictly narrow that attainment seam:

- any approximating sequence with opponent-tight clocks realizes the full
  semantic minimum, including unrestricted caps;
- two proper limiting clocks already suffice; and
- failure with exactly one proper clock has one explicit coordinate, event,
  sign, and quantitative size.

What remains is the all-player escaped-law arm, together with the
negative-singleton one-proper arm when singleton rewards of mixed sign are
allowed. The result does not close the paid-port descent/inert disjunction or
the full conjecture.

## Definitions, probability mode, and agency

The game has one live public history at every date: all players have continued.
Each behavioral strategy therefore induces one complete stopping law on
\(\overline{\mathbb N}\), and independent private randomization makes the
players' latent stopping times independent. Conversely, hazard reconstruction
realizes every such probability law behaviorally.

Weak convergence is taken in the repository compact topology:

\[
\text{CompactStoppingLaw}
=\operatorname{ProbabilityMeasure}(\operatorname{WithTop}\mathbb N).
\]

For fixed \(H\), each finite singleton and the tail
\(\{H+1,H+2,\ldots,\infty\}\) are clopen. The singleton
\(\{\infty\}\) is closed but generally not open; its mass is not asserted to
converge.

The best-response cap ranges over arbitrary history-dependent behavioral
deviations. Pure-time extremality is used only as an exact representation of
that unrestricted supremum, not as a restriction on the deviator.

## Source correspondence

Existing checked inputs:

- MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean defines
  CompactStoppingTime, CompactStoppingLaw, and the probability-law/PMF bridge.
- UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean
  contains stopping-law hazard reconstruction and its exact inverse.
- UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean proves
  that the unrestricted cap is the supremum of deterministic finite quitting
  times and Never.
- UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean proves
  exists_terminalProfile_sequence_tendsto_semanticPair.
- UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean proves
  exists_profile_sequence_tendsto_minimumTerminalSemanticDebt.
- UniformEquilibrium/Diagnostics/Quitting/PositiveDebtTerminalSemanticNonattainment.lean
  gives a two-player nonattained positive-debt carrier point whose global
  minimum is zero.
- notes/CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md, Propositions 2--3,
  already contains the late-finite/Never identity and a qualitative
  negative-singleton boundary in ordinary mathematics. It does not prove
  opponent-tight uniform convergence of unrestricted caps, the two-proper
  realization criterion, or the quantitative global-minimum jump (2).

No checked declaration found in the audits proves uniform convergence of the
entire pure-time menu under (OT), realizes the full terminal semantic pair
under opponent tightness, or gives the quantitative jump (2). Those are the
new statements.

## Proof

### Prescribed payoff convergence

Fix \(H\). Terminal payoff restricted to absorption by time \(H\) is a finite
polynomial in the laws' point masses at dates \(0,\ldots,H\), so it converges
under weak convergence.

Let \(R=\max_{i,S}|r_i(S)|\) and \(M^n=\min_iT_i^n\). For any fixed player
\(i_0\),

\[
\left|U_i(\sigma_n)
-\mathbb E[r_i(Q)\mathbf 1_{\{M^n\le H\}}]\right|
\le R\Pr(M^n>H)
\le R\Pr(M_{-i_0}^n>H).
\]

The same bound holds for the limiting profile. For fixed \(H\), the tail event
is clopen, so its limiting probability is the limit of the approximating
probabilities. Let \(n\to\infty\), then \(H\to\infty\), and use (OT). This
proves

\[
U(\sigma_n)\to U(\sigma_\infty).
\]

### Uniform convergence of the pure-time menu

For player \(i\), define

\[
v_{i,n}(t)=U_i(\sigma_n[i\leftarrow Q_i^t]),
\qquad t\in\overline{\mathbb N}.
\]

Every fixed finite \(t\) depends only on finitely many opponent point masses
and one clopen tail coordinate, so
\(v_{i,n}(t)\to v_{i,\infty}(t)\).

If \(s,t>H\), allowing Never, the two deviations coincide whenever an opponent
has stopped by \(H\). Therefore

\[
|v_{i,n}(s)-v_{i,n}(t)|
\le2R\Pr(M_{-i}^n>H). \tag{3}
\]

Compare both tails to \(H+1\):

\[
\begin{aligned}
|v_{i,n}(t)-v_{i,\infty}(t)|
\le{}&
2R\Pr(M_{-i}^n>H)\\
&+|v_{i,n}(H+1)-v_{i,\infty}(H+1)|\\
&+2R\Pr(M_{-i}^\infty>H).
\end{aligned}
\]

For \(t\le H+1\), convergence is uniform because the menu is finite. The
clopen-tail convergence and (OT) make both tail probabilities small. Hence

\[
\sup_{t\in\overline{\mathbb N}}
|v_{i,n}(t)-v_{i,\infty}(t)|\to0.
\]

Pure-time extremality gives

\[
|B_i(\sigma_n)-B_i(\sigma_\infty)|
\le
\sup_t|v_{i,n}(t)-v_{i,\infty}(t)|\to0.
\]

Together with prescribed-payoff convergence, this proves Theorem A.

### Proper clocks and the common late event

If \(\mu_j\) is proper, its clopen tail probabilities tend to zero as
\(H\to\infty\), and weak convergence transfers the fixed-\(H\) tails from
\(\mu_j^n\). Two distinct proper players ensure that every player has a proper
opponent, proving (OT) and Theorem B.

If a selected law limit of a nonattained point had two proper coordinates,
Theorem B would realize it. Thus it has at most one. Choose \(i\) to be the
proper player when there is exactly one, and arbitrarily when there are none.
Then

\[
q_{-i}=\prod_{j\ne i}\mu_j(\{\infty\})>0.
\]

For fixed \(H\), independence and clopen-tail convergence give

\[
\Pr(T_j^n>H\ \forall j\ne i)
\to\prod_{j\ne i}\mu_j(\{H+1,H+2,\ldots,\infty\})
\ge q_{-i}.
\]

Taking \(\kappa=q_{-i}\) proves (1) on the selected subsequence.

### The one-proper minimum jump

Suppose only \(k\)'s law is proper. Since
\(\min_iT_i^n\le T_k^n\), prescribed absorption is uniformly tight, giving
\(U(\widehat\sigma)=u\). Player \(k\) is a proper opponent for every
\(j\ne k\), so the coordinatewise cap argument gives
\(B_j(\widehat\sigma)=b_j\).

Actuality of \(\widehat\sigma\) and global minimality imply

\[
D_*\le D(\operatorname{Sem}(\widehat\sigma))
=D_*+\widehat b_k-b_k,
\]

hence \(\widehat b_k\ge b_k\).

Every fixed finite pure-time value converges and is bounded by the
approximating cap. Thus

\[
\beta_k^{\mathrm{fin}}
:=\sup_{t<\infty}v_k(t)\le b_k.
\]

If equality \(\widehat b_k=b_k\) held, all semantic coordinates of
\(\widehat\sigma\) would equal \(z\), realizing it. Under nonattainment,

\[
\widehat b_k>b_k\ge\beta_k^{\mathrm{fin}},
\]

so pure-time extremality forces
\(\widehat b_k=v_k(\infty)\).

Pathwise dominated convergence gives

\[
v_k(t)\to v_k(\infty)+q_{-k}s_k.
\]

Indeed, if an opponent eventually stops, sufficiently late finite Quit and
Never produce the same terminal coalition. If all opponents Never, finite
Quit pays \(s_k\), while Never pays zero. Since all finite values are at most
\(b_k\),

\[
\widehat b_k+q_{-k}s_k\le b_k<\widehat b_k.
\]

This proves (2) and Theorem C.

## Boundary tests

1. If two players' laws are supported in one common finite horizon throughout
   the sequence, their limiting laws are proper opponents covering every
   player. The theorem reduces to ordinary finite-cylinder continuity.

2. The checked two-player table in
   PositiveDebtTerminalSemanticNonattainment.lean has actual semantic pairs
   converging to a nonattained point of positive debt. In the compactified
   law limit both players are Never, so there are zero proper clocks and (OT)
   fails. Its global minimum is zero. This shows why positive debt alone and
   weak law convergence are insufficient.

3. The one-proper jump bound is sharp as a sequence identity. Let players be
   \(k,j\), give player \(k\) reward \(-1\) at every nonempty terminal
   coalition, and give \(j\) reward zero. Prescribe \(k\) to Quit at date zero
   and \(j\) to Quit at date \(n\). Every approximating cap of \(k\) is
   \(-1\). In the limiting law profile, \(k\) remains proper and \(j\) Never;
   \(k\)'s Never cap is zero. Thus

   \[
   \widehat b_k-b_k=1=-q_{-k}s_k.
   \]

   The approximating semantic point is attained elsewhere and the global
   minimum is zero, so this is only a sharpness test for the formula, not a
   positive-minimum counterexample.

## Adapter and consumer

For any specified carrier minimum, the checked theorem
exists_terminalProfile_sequence_tendsto_semanticPair supplies the actual
semantic approximants. The separate theorem
exists_profile_sequence_tendsto_minimumTerminalSemanticDebt jointly selects
one minimum together with such a sequence; it is not the adapter for an
arbitrarily preselected minimum. Compactness of the finite product of
CompactStoppingLaw spaces supplies a weakly convergent law subsequence.

The new theorem consumes any such subsequence satisfying (OT) and returns an
actual profile realizing the minimum. If two limiting laws are proper, (OT)
is automatic. Otherwise, it outputs the exact remaining escape geometry (1)
or (2), which is a strictly smaller target for the minimum-attainment seam in
the paid-port and Fin4 routes.

No existing checked consumer closes either residual escape arm.

## Lean handoff

A narrow formalization should:

1. import MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean and the
   stopping-law reconstruction and pure-time extremality modules;
2. package simultaneous subsequence extraction for finitely many
   CompactStoppingLaw coordinates;
3. prove convergence of finite singleton masses and fixed clopen tails;
4. define opponent tail probability and prove the oscillation estimate (3);
5. prove uniform pure-time-value convergence and then cap convergence;
6. state opponent-tight semantic realization;
7. derive the two-proper criterion and selected-subsequence common late event;
8. derive the one-proper positive-minimum Never-jump bound.

Do not use a discrete topology on Option Nat. Do not assert convergence of
the singleton Never masses. Do not quantify one exceptional player uniformly
over all realizing sequences or all compactified subsequences.

## Scope and nonclaims

This packet does not prove that a positive global minimum is always attained.
It does not eliminate the all-nonproper escaped-law arm, and it eliminates the
one-proper arm only when singleton rewards are nonnegative. It does not
construct an admissible path, paid-source regeneration, or a uniform-equilibrium
payoff.

## Checked Lean realization

The packet is proved in
`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`.
The principal checked declarations are:

- `exists_quittingCompactStoppingLawsOfProfile_tendsto_subseq`, providing one
  simultaneous compact-law subsequence for all finitely many players;
- `quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile`, the exact
  actual-profile canonical-law adapter;
- `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit`, Theorem A with
  unrestricted behavioral caps;
- `quittingTerminalSemanticPair_eq_of_twoProper_lawLimits` and
  `exists_commonLateOpponentTail_of_not_attained_lawLimit`, the two arms of
  Theorem B;
- `oneProper_minimum_negativeSingletonJump_of_notAttained_lawLimit`, Theorem C,
  including the exact Never cap, negative singleton reward, and quantitative
  jump bound; and
- `all_not_compactStoppingLawIsProper_of_singleton_nonnegative`, which removes
  the one-proper arm when all singleton rewards are nonnegative.

Reusable probability and stopping-law bridges are checked in
`MathUE/Probability/FiniteIndependentMixture.lean`,
`MathUE/Probability/StoppingLawReconstruction.lean`,
`MathUE/ProbabilityMassFunction.lean`, and
`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`.

Evidence seals: `M` passes the packet proof and independent falsification
audits; `L` passes direct Lean checks and the named dependency build; `A`
passes through literal behavioral profiles and their canonical stopping laws;
`C` passes for the stated two-proper, one-proper, and nonnegative-singleton
internal consumers. No checked consumer turns either final residual law-limit
arm into a paid restart, admissible path, uniform-equilibrium payoff, or
conjecture closure.

The Lean proof deliberately does not assert positive-minimum attainment,
convergence of the approximants' Never atoms, one exceptional owner common to
different selected subsequences, elimination of the all-nonproper arm, or
elimination of the mixed-sign one-proper arm.

## Subsequent checked refinement

The downstream terminal-law escape account and social-sign split are checked
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeSocialSignAttainment.lean`.
They close the social-nonpositive part of the all-nonproper arm by attaining
the global minimum debt value, and strict aggregate negativity realizes the
supplied minimizing semantic point. The strict positive-social escape and the
mixed-sign one-proper arm remain without a return, renewal, or
uniform-equilibrium consumer.

## Historical question-link successors

`FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md`, cited in the preserved packet text
above, was removed when its umbrella question was split into narrower live
questions. No single current question is an equivalent successor. The
[maintained questions index](../questions/README.md) is the canonical entry
point. The relevant current routes are:

- the paid/reset [parent fork](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md),
  [regeneration child](../questions/FIN4_PAID_RESET_REGENERATION_RANK.md), and
  [paired-cap child](../questions/FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md);
- the [uniform-escape](../questions/FIN4_UNIFORM_ESCAPE_CAPSTONE.md) and
  [minimum-return](../questions/FIN4_MINIMUM_RETURN_CAPSTONE.md) components; and
- the current [full-debt](../questions/FIN4_FULL_DEBT_CHAMBER_CONSUMER.md) and
  [reset-rigid](../questions/FIN4_RESET_RIGID_CHAMBER_CONSUMER.md) capstones.

These successor links provide navigation only; they do not strengthen the
formalization record or nonclaims above.
