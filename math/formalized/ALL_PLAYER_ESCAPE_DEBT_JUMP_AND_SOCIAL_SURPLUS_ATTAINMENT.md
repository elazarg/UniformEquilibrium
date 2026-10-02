# All-player escape debt jump and social-surplus attainment

Author: `CHATGPT_EXTERNAL`

Independent reviews:
[adversarial falsification](../feedback/ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS__BY_NOTE_MINING_FALSIFIER.md),
[source and freshness audit](../feedback/ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS__BY_NOTE_MINING_SOURCE_AUDIT.md), and
[strengthening review](../feedback/ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS__BY_NOTE_MINING_STRENGTHENER.md)

## Exact statement

Let \(I\) be a finite nonempty player set. For every nonempty coalition
\(S\subseteq I\), let \(r(S)\in\mathbb R^I\) be its terminal reward vector;
all-Never pays zero.

Let \(\sigma_n\) be actual behavioral profiles with

\[
\operatorname{Sem}(\sigma_n)=(U^n,B^n)\longrightarrow z=(u,b).
\]

After a common subsequence, suppose every complete marginal stopping law
converges weakly on \(\mathbb N\cup\{\infty\}\) to \(\mu_i\), and the complete
terminal-outcome laws converge to \(m^*\). Let \(\bar\sigma\) be the actual
product behavioral profile reconstructed from the laws \((\mu_i)_i\), and let
\(m\) be its terminal-outcome law.

For every nonempty coalition define

\[
e(S)=m^*(S)-m(S),\qquad
R(S)=\sum_i r_i(S).
\]

### Escape account

For every nonempty \(S\),

\[
\boxed{e(S)\ge0,}
\tag{1}
\]

and

\[
\sum_{S\ne\varnothing}e(S)
=m(\mathsf{Never})-m^*(\mathsf{Never}).
\tag{2}
\]

For every player \(i\),

\[
\boxed{
u_i-U_i(\bar\sigma)
=\sum_{S\ne\varnothing}e(S)r_i(S).
}
\tag{3}
\]

Write

\[
q_i=\Pr_{\bar\sigma_{-i}}(\text{every opponent Never stops}),\qquad
s_i=r_i(\{i\}),
\]

and

\[
\kappa_i=q_i(-s_i)_+.
\]

Then the complete unilateral behavioral cap satisfies the sharp one-sided
bound

\[
\boxed{B_i(\bar\sigma)\le b_i+\kappa_i.}
\tag{4}
\]

In particular, if \(s_i\ge0\), then \(B_i(\bar\sigma)\le b_i\).

Put

\[
\Delta_i=b_i-B_i(\bar\sigma).
\]

The total-debt jump is the exact identity

\[
\boxed{
D(\bar\sigma)-D(z)
=
\sum_{S\ne\varnothing}e(S)R(S)-\sum_i\Delta_i.
}
\tag{5}
\]

Equations (1)--(5) require no global-minimum or positive-debt hypothesis.

### Minimum and nonattainment consequences

Assume \(z\) minimizes total debt on the terminal-semantic carrier and every
own singleton reward is nonnegative. Then \(\Delta_i\ge0\) and

\[
\boxed{
\sum_Se(S)R(S)\ge\sum_i\Delta_i\ge0.
}
\tag{6}
\]

If no actual behavioral profile attains the global minimum debt value, then
the first inequality is strict. More exactly, with

\[
\delta=D(\bar\sigma)-D(z)>0,
\]

\[
\sum_Se(S)R(S)=\delta+\sum_i\Delta_i.
\tag{7}
\]

If \(n=|I|\), all rewards have absolute value at most \(M>0\), and the
minimum value is genuinely nonactual, then some escaped-support coalition
\(S\) satisfies

\[
R(S)>0,\qquad
e(S)R(S)\ge\frac{\delta}{2^n-1},\qquad
e(S)\ge\frac{\delta}{(2^n-1)nM}.
\tag{8}
\]

### Social-surplus attainment chamber

Assume

\[
r_i(\{i\})\ge0\quad(i\in I),
\qquad
R(S)\le0\quad(S\ne\varnothing).
\tag{9}
\]

Then every terminal-semantic carrier point is weakly debt-dominated by an
actual behavioral profile. Consequently,

\[
\boxed{\text{the global carrier minimum debt value is attained by an actual profile}.}
\tag{10}
\]

No positivity assumption on the minimum value is needed.

At a minimum, every cap drop vanishes and escaped mass is supported only on
zero-social-reward coalitions:

\[
\Delta_i=0\quad(i\in I),\qquad
e(S)>0\Longrightarrow R(S)=0.
\tag{11}
\]

If the aggregate signs are strict,

\[
R(S)<0\qquad(S\ne\varnothing),
\tag{12}
\]

then every globally minimizing carrier point is itself behaviorally attained,
not merely matched in minimum value.

## Conjecture-facing change

The checked opponent-tight realization theorem reduced the remaining
nonattainment problem, under nonnegative own-singleton rewards, to an
all-nonproper marginal-law limit. It did not classify the loss of terminal
mass or compare the unrestricted caps there.

Equations (1)--(7) give the exact missing account. A genuinely nonactual
minimum must carry escaped positive social surplus which exceeds the entire
downward jump of the cap envelopes. The sign chamber (9) eliminates that
possibility and produces an actual minimum profile.

If the minimum is zero, the actual profile is an exact terminal Nash profile.
If the minimum is positive under a terminal-gap hypothesis, the checked
actual-profile paid-cap machinery sends it to the literal minimum-fibre inert
stall. This packet does not consume that stall.

## Definitions and assumptions

The complete terminal law lives on

\[
\{\mathsf{Never}\}\cup
\{S\subseteq I:S\ne\varnothing\}.
\]

The cap \(B_i\) is the supremum over all unilateral behavioral strategies.
Pure-time extremality includes every deterministic finite quitting date and
Never and is exact for this full strategy class. No supremum is assumed to be
attained.

The numbers \(e(S)\) are subsequential compactification defects of complete
terminal laws. They are not fixed-date atoms of \(\bar\sigma\).

## Source correspondence

Compact stopping laws and their behavioral reconstruction are in
`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`.

Exact pure-time extremality is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
Finite-time response continuity and the late-finite/Never identity are in
`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`.

The actual-data source selector
`nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier` supplies one
realizing profile sequence and simultaneous weak limits of all marginal
stopping laws. Compactness of the finite terminal-outcome simplex supplies
the further common outcome-law subsequence. The prescribed reward-moment
identity is also available through
`terminalSemanticLawCarrier_rewardMoment`.

The closest checked packet,
`formalized/OPPONENT_TIGHT_TERMINAL_SEMANTIC_REALIZATION.md`, stops before
(1), the all-nonproper cap estimate, (5), and the social-surplus attainment
theorem. No matching result was found in the checked tree or prior exports.

## Proof

### Escaped mass and prescribed payoff

Fix nonempty \(S\) and a finite horizon \(T\). The probability that \(S\) is
the first terminal coalition at some date at most \(T\) is a finite
polynomial in the marginal stopping-law masses at finitely many dates and
their finite tails. Weak convergence on the one-point compactification gives

\[
\Pr_{\bar\sigma}(S\text{ occurs by }T)
=\lim_n\Pr_{\sigma_n}(S\text{ occurs by }T)
\le m^*(S).
\]

Letting \(T\to\infty\) and using monotone convergence yields
\(m(S)\le m^*(S)\), proving (1). Summing all finite outcome coordinates in
the two probability laws gives (2).

Never pays zero and there are finitely many absorbing coalitions, so

\[
U_i(\bar\sigma)=\sum_Sm(S)r_i(S),\qquad
u_i=\sum_Sm^*(S)r_i(S).
\]

Subtraction proves (3).

### Complete cap estimate

Let \(V_i^n(t)\) be the payoff when \(i\) Quits deterministically at finite
date \(t\) against \(\sigma_{n,-i}\), and let \(\bar V_i(t)\) be the analogous
limiting payoff. For each fixed finite \(t\),

\[
V_i^n(t)\longrightarrow\bar V_i(t).
\]

Since \(V_i^n(t)\le B_i(\sigma_n)\to b_i\),

\[
\sup_{t<\infty}\bar V_i(t)\le b_i.
\tag{13}
\]

Against the limiting opponents,

\[
\lim_{t\to\infty}\bar V_i(t)
=\bar V_i(\mathsf{Never})+q_i s_i.
\tag{14}
\]

Thus

\[
\bar V_i(\mathsf{Never})
\le
\sup_{t<\infty}\bar V_i(t)+q_i(-s_i)_+.
\]

Exact pure-time extremality says that the complete behavioral cap is the
supremum of the finite-time values and Never. Combining this fact with (13)
proves (4).

### Debt account and minimum

Direct subtraction gives

\[
\begin{aligned}
D(\bar\sigma)-D(z)
&=\sum_i
 \bigl(B_i(\bar\sigma)-U_i(\bar\sigma)-b_i+u_i\bigr)\\
&=\sum_Se(S)R(S)-\sum_i\Delta_i,
\end{aligned}
\]

proving (5).

If \(z\) is globally minimizing, the semantic pair of \(\bar\sigma\) is an
actual carrier point, so the left side is nonnegative. Under nonnegative own
singletons, (4) gives \(\Delta_i\ge0\), proving (6). Strict nonattainment of
the minimum value gives (7). Finite pigeonhole over the \(2^n-1\) nonempty
coalitions and \(|R(S)|\le nM\) gives (8).

Under (9), the right side of (5) is nonpositive for the actual profile
constructed from any carrier point. This proves weak debt domination. At a
minimum, both inequalities force equality, proving (10)--(11). Under (12),
\(e=0\); then (3) and \(\Delta=0\) show
\(\operatorname{Sem}(\bar\sigma)=z\).

## Boundary tests

### The singleton sign is sharp

Take players \(i,j\). Give player \(i\) reward \(-1\) at every nonempty
coalition, let \(i\) Never quit, and let \(j\) quit deterministically at date
\(n\). Every response by \(i\) receives \(-1\), so

\[
B_i(\sigma_n)=-1.
\]

The limiting profile is all Never, against which Never gives zero. Hence

\[
B_i(\bar\sigma)=0>-1=\lim_nB_i(\sigma_n).
\]

Thus the nonnegative-singleton hypothesis is essential for
\(B_i(\bar\sigma)\le b_i\), and the correction \(\kappa_i\) in (4) is sharp.

### Global-minimum provenance is essential

There is a two-player sequence with both own singleton rewards zero whose
semantic pairs converge to a nonattained debt-one point while both marginal
laws converge to Never. The all-Never profile has debt zero. Thus positive
debt, nonnegative own singletons, and nonattainment of one carrier point do
not suffice; the selected debt value must be globally minimal.

### Aggregate sign is sufficient, not necessary

A coalition with positive \(R(S)\) does not force nonattainment. The universal
necessary condition is the sequence-specific strict inequality (7), not the
converse of (9).

## Adapter and consumer

For any carrier point, use the checked selected-law-limit theorem, then pass
to a further subsequence in the finite outcome simplex and reconstruct
\(\bar\sigma\). This is an unconditional actual-data adapter.

In chamber (9), a carrier minimizer becomes an actual minimum profile. At
zero minimum the checked terminal-Nash compiler yields a uniform payoff. At
positive minimum under a terminal gap, the actual-profile paid-cap port and
`QuittingActualProfileTerminalGapPaidCapPort.inertStall_of_minimumFiber`
yield the existing exact-minimum inert-stall node.

Outside the sign chamber, (7)--(8) produce a quantitative positive-social-
surplus escape packet. No current theorem consumes that packet.

## Lean handoff

Suggested declarations:

- `quittingTerminalEscapedCoalitionMass_nonneg`;
- `quittingTerminalEscapedMass_sum_eq_neverGain`;
- `quittingTerminalPrescribedPayoff_escapeMoment`;
- `quittingContinuationBestResponseValue_limit_le_add_singletonPenalty`;
- `quittingTerminalSemanticDebt_escapeJump`;
- `minimum_nonactual_implies_positiveSocialEscape`;
- `exists_actual_minimum_of_singleton_nonneg_social_nonpos`; and
- `minimum_point_attained_of_singleton_nonneg_social_neg`.

A general late-finite/Never identity should first be stated for arbitrary
opponent compact stopping laws. The existing all-nonproper theorem is its
only nontrivial case; if one opponent is proper, the opponents-all-Never
factor is zero.

The finite-horizon proof of (1) is preferable to an abstract Portmanteau proof
for Lean. The actual-data adapter must retain one common realizing sequence
through both marginal-law and outcome-law subsequences.

## Scope and nonclaims

This result does not prove that every carrier point is attained under weak
aggregate signs, does not prove a uniform payoff when the attained minimum is
positive, and does not consume the positive-social-surplus escape or inert
stall arms. It closes the all-nonproper nonattainment seam only in the stated
social-sign chamber.

## Lean formalization record

Pre-formalization packet SHA-256:
`e06b55ac9f61317517cf39a134d3d310cec99f64824d18a9309f1f9f22cbfeff`.

The common terminal-law escape account, including equations (1)--(3) and
the actual carrier-point adapter, landed in commit
`927e4e2baef1f883cf869da7656a8c1c7bbe3670`. The arbitrary compact-law
late-finite/Never identity, sharp cap correction (4), and debt account (5)
landed in commit `e964471c38cea8070e11a8972e5c0e4415a5ce3b`. The minimum,
strict nonattainment, and quantitative positive-social extraction consequences
(6)--(8) landed in commit
`cd323bf3380dca41c9781d24517ba2eefecc7bf2`. The weak and strict social-sign
attainment consequences (9)--(12) landed in commit
`31e7be988ef993b977c3a382fe4c229280cdcd1d`.

The production owners are
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeAccount.lean`,
`UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`,
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeDebtJump.lean`,
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeMinimumConsequences.lean`,
and
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeSocialSignAttainment.lean`.
The finite signed selector used in equation (8) is owned by
`MathUE/FinitePaidCollision.lean`.

Equations (1)--(3) are exposed by the fields
`QuittingTerminalSemanticEscapeAccount.escapeMass_nonneg`,
`QuittingTerminalSemanticEscapeAccount.totalEscapeMass_eq`, and
`QuittingTerminalSemanticEscapeAccount.escapedRewardMoment_eq`.
`exists_quittingTerminalSemanticEscapeAccount_of_mem_carrier` supplies the
common actual-data refinement for every carrier point.

The cap layer is exposed by
`quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`,
`quittingCompactStoppingLawProfile_cap_le_finiteBound_add_opponentNeverProduct_mul_negPart`,
`quittingCompactStoppingLawProfile_cap_le_target_add_opponentNeverProduct_mul_negPart_of_lawLimit`,
and the selected-law wrappers
`QuittingTerminalSemanticSelectedLawLimit.reconstructedCap_le_add_opponentNeverProduct_mul_negPart`
and
`QuittingTerminalSemanticSelectedLawLimit.reconstructedCap_le_of_singleton_nonneg`.
The exact debt account is
`QuittingTerminalSemanticEscapeAccount.debtSum_sub_target_eq_escapeSocialReward_sub_capDropSum`,
with its reoriented form
`QuittingTerminalSemanticEscapeAccount.escapeSocialReward_eq_reconstructedDebtJump_add_capDropSum`.

The minimum consequences are
`QuittingTerminalSemanticEscapeAccount.capDropSum_nonneg_and_le_escapeSocialReward_of_minimum`,
`QuittingTerminalSemanticEscapeAccount.reconstructedDebtJump_pos_of_minimumValue_not_attained`,
`QuittingTerminalSemanticEscapeAccount.exists_positiveSocialRewardEscape_of_pos_le_escapeSocialReward`,
and
`QuittingTerminalSemanticEscapeAccount.exists_positiveSocialRewardEscape_of_minimumValue_not_attained`.
They retain literal positive escape mass, positive social reward, the product
floor with denominator `2^card - 1`, and the escape-mass floor with denominator
`(2^card - 1) * card * M`.

The social-sign layer is exposed by
`QuittingTerminalSemanticEscapeAccount.reconstructedDebtJump_nonpos_of_singleton_nonneg_socialReward_nonpos`,
`QuittingTerminalSemanticEscapeAccount.MinimumSocialNonpositiveConsequences`,
`QuittingTerminalSemanticEscapeAccount.minimumSocialNonpositiveConsequences`,
`exists_actualProfile_debtSum_le_of_singleton_nonneg_socialReward_nonpos`,
`exists_actualProfile_debtSum_eq_of_minimum_singleton_nonneg_socialReward_nonpos`,
`exists_actual_minimum_of_singleton_nonneg_social_nonpos`, and
`minimum_point_attained_of_singleton_nonneg_social_neg`.

Evidence seals are `M` and `L` for equations (1)--(12). The carrier-facing
construction has `A`: it starts from actual behavioral profiles realizing an
arbitrary carrier point and retains one common semantic, marginal-law, and
terminal-law subsequence. There is branch-local `C` in the social-nonpositive
chamber, where an actual profile weakly debt-dominates the target and realizes
the global minimum debt value; strict aggregate negativity realizes the
supplied minimizing semantic point itself. The strict positive-social-surplus
branch has no downstream `C`.

Weak aggregate signs do not realize an arbitrary minimizing carrier point;
they attain only its minimum debt value. Strict signs identify the semantic
pair, not the selected limiting terminal law or its source chronology. The
checked results do not consume the positive-social escape, do not produce a
Fin4 return, renewal, rank transition, terminal Nash profile, or
uniform-equilibrium payoff, and do not settle the positive attained-minimum
inert branch. The earlier source-correspondence and Lean-handoff sections
describe the pre-formalization boundary and are superseded by this record.
