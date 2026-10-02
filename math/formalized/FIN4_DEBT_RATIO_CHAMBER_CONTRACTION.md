# Fin4 debt-ratio chamber contraction

Authors: SOCIAL_WEIGHT_REVIEW
Independent reviews:
[CODEX_DESCENDANT](../feedback/SOCIAL_WEIGHT_REVIEW__CERTIFIED_THIN_SLICE_DEBT_TOKEN_ROTATION__BY_CODEX_DESCENDANT.md),
[PAIRED_HULL_REVIEW](../feedback/SOCIAL_WEIGHT_REVIEW__CERTIFIED_THIN_SLICE_DEBT_TOKEN_ROTATION__BY_PAIRED_HULL_REVIEW.md)

## Exact statement

Let \(I\) be a finite nonempty player set.  Consider a quitting game whose
terminal rewards satisfy

\[
  |r_i(S)|\le M
  \qquad
  (i\in I,\ \varnothing\ne S\subseteq I),
\]

where \(M>0\).  For an actual behavioral profile \(\sigma\), write

\[
  U_i(\sigma)
\]

for its prescribed terminal payoff and

\[
  B_i(\sigma)
\]

for player \(i\)'s unrestricted behavioral best-response value against
\(\sigma_{-i}\).  Define

\[
  d_i(\sigma):=B_i(\sigma)-U_i(\sigma),
  \qquad
  D(\sigma):=\sum_{i\in I}d_i(\sigma).
\]

Put

\[
  \eta:=\inf_\sigma\max_{i\in I}d_i(\sigma),
  \qquad
  D_*:=\inf_\sigma D(\sigma),
\]

and assume \(\eta>0\).

### Theorem A: universal separation

\[
  \boxed{
  D_*-\eta
  \ge
  \sqrt{4M^2+\eta^2}-2M
  =
  \frac{\eta^2}{\sqrt{4M^2+\eta^2}+2M}
  >0.}
\tag{A}
\]

Thus a positive terminal exploitability floor forces a strictly larger
minimum total debt.  This conclusion does not require either infimum to be
attained and does not require exact attainment of a best response.

### Theorem B: conditional exact-attainment estimate

Let \(\sigma\) be an actual profile and put

\[
  S:=D(\sigma),\qquad
  a:=\max_i d_i(\sigma).
\]

Assume

\[
  \eta<S<2\eta,
\]

choose \(p\) with \(d_p(\sigma)=a\), and assume player \(p\)'s complete
behavioral best response is attained by a strategy \(\tau_p\).  Let

\[
  \rho:=(\tau_p,\sigma_{-p}).
\]

Then \(a>\eta\), player \(p\)'s debt is killed exactly at \(\rho\), and

\[
  \boxed{
  D(\rho)-S
  \ge
  \frac{a(2\eta-S)}{a-\eta}
  \ge
  \frac{S(2\eta-S)}{S-\eta}
  >0.}
\tag{B}
\]

The gain of player \(p\) is exactly \(a\).

### Theorem C: unconditional carrier and actual-source form

Let \(x\) be a terminal-semantic carrier point satisfying

\[
  D(x)=D_*,
  \qquad
  \eta<D_*<2\eta.
\]

Define

\[
  \Delta_{\mathrm{port}}
  :=
  \frac{D_*(2\eta-D_*)}{D_*-\eta}
  >0.
\]

Then there are:

- one fixed player \(p\);
- actual profiles \(\sigma_n\) converging semantically to \(x\);
- positive errors \(\zeta_n\downarrow0\);
- \(\zeta_n\)-best complete behavioral responses \(\tau_{p,n}\) to
  \((\sigma_n)_{-p}\);
- literal one-player replacement profiles
  \[
    \rho_n:=(\tau_{p,n},(\sigma_n)_{-p});
  \]

such that \(p\) is a maximum-debt player of every \(\sigma_n\), the opponents
of \(p\) are unchanged literally, and

\[
  U_p(\rho_n)-U_p(\sigma_n)
  \ge d_p(\sigma_n)-\zeta_n,
\tag{C1}
\]

\[
  \liminf_n
  \bigl(U_p(\rho_n)-U_p(\sigma_n)\bigr)
  \ge\eta,
\tag{C2}
\]

and

\[
  \boxed{
  \liminf_n\bigl(D(\rho_n)-D_*\bigr)
  \ge\Delta_{\mathrm{port}}.}
\tag{C3}
\]

After passing to a subsequence, the semantic pairs of \(\rho_n\) converge to
a carrier point \(y\) with

\[
  D(y)\ge D_*+\Delta_{\mathrm{port}}.
\tag{C4}
\]

For every fixed terminal-gap constant \(0<\gamma<\eta\), this gives a
two-stage actual-data adapter.  The first stage is the literal full-response
edge

\[
  \sigma_n\longrightarrow\rho_n
\]

with fixed payer \(p\), asymptotic gain at least \(\eta\), and target excess
\(\liminf_n(D(\rho_n)-D_*)\ge\Delta_{\mathrm{port}}\).  After discarding
finitely many indices, every retained target has the uniform concrete excess

\[
  D(\rho_n)-D_*\ge\frac{\Delta_{\mathrm{port}}}{2}.
\]

The second stage applies the checked
terminal-gap first-disagreement construction separately at the supplied
target profile \(\rho_n\).  It produces a paid cap port based at \(\rho_n\).
The port's selected observer and paid row need not be \(p\) or the full
response edge above.  A composite certificate retains the incoming
\(p\)-response edge externally together with this separately selected port.

## Conjecture-facing change

Under failure of a uniform-equilibrium payoff, the checked terminal
exploitability infimum is positive.  Theorem A then deletes the formal
boundary \(D_*=\eta\).  Theorems B and C consume the complete open ratio
chamber

\[
  1<\frac{D_*}{\eta}<2
\]

into the already isolated quantitative off-minimum paid-port interface.

This is a genuine chamber contraction.  It is not a uniform-equilibrium
consumer: the downstream paid-cap trichotomy still has descent and inert
outputs that require separate treatment.

## Definitions and assumptions

The game is the standard infinite-horizon quitting game with public
observation of past all-Continue outcomes.  Each player may use an arbitrary
behavioral strategy, equivalently an arbitrary randomized stopping time
taking values in \(\mathbb N\cup\{\infty\}\).  The cap \(B_i(\sigma)\) is the
supremum over this complete unilateral strategy class; it is not restricted
to stationary, bounded-deadline, or pure-time responses.  The stopping-law
mixtures used below mix whole behavioral stopping laws, including their Never
mass and all late stopping times.

The payoff mode is terminal: a finite nonempty quitting coalition receives
the table reward, while Never receives the game's declared Never payoff.
The bound \(M\) applies to every terminal payoff coordinate and therefore to
every prescribed payoff and unilateral response payoff.  All continuity and
compactness statements concern the checked terminal-semantic carrier, whose
coordinates are prescribed payoffs and unrestricted behavioral caps.

Theorem B assumes exact attainment only to state a literal endpoint formula.
The conjecture-facing Theorem C assumes no such attainment and uses
\(\zeta_n\)-optimal actual behavioral responses.

## Source correspondence

The proof uses the following checked declarations and their definitions.

- *quittingContinuationBestResponseValue*,
  *quittingTerminalPayoff_update_le_continuationBestResponseValue*, and
  *exists_quittingContinuation_deviation_ge_sub* in
  UniformEquilibrium/Quitting/Root/FirstBranch.lean provide the complete
  unrestricted behavioral cap and approximate best responses.
- *quittingTerminalDeviationDebt_nonneg* in
  UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean gives debt
  nonnegativity.
- *quittingStoppingLawMixtureBehaviorStrategy* and
  *quittingBehaviorStoppingLaw_stoppingLawMixture* in
  UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean provide the
  mixture of complete stopping laws.
- *quittingTerminalPayoff_stoppingLawMixture_eq*,
  *quittingContinuationBestResponseValue_stoppingLawMixture_le*,
  *quittingTerminalSemanticDebt_stoppingLawMixture_le*, and
  *quittingTerminalSemanticDebt_stoppingLawMixture_eq_self* in
  UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean
  provide payoff affinity, cap convexity, debt convexity, and the exact mover
  identity.
- *quittingContinuationBestResponseValue_update_self* in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTightness.lean
  identifies the mover's unchanged cap under a self-strategy replacement.
- *quittingTerminalSemanticDebtSum*,
  *continuous_quittingTerminalSemanticDebtSum*,
  *quittingTerminalExploitabilityInf_le_semanticCarrier*,
  *exists_minimum_quittingTerminalSemanticDebtSum*, and
  *exists_profile_sequence_tendsto_minimumTerminalSemanticDebt* in
  UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean
  provide the carrier minimum, continuity, and realizing sequences.
- *quittingTerminalExploitabilityInf*,
  *quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff*, and
  *hasTerminalExploitabilityGap_of_lt_quittingTerminalExploitabilityInf* in
  UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean
  connect failure of a uniform payoff to \(\eta>0\) and to a chosen terminal
  gap \(\gamma<\eta\).
- *QuittingActualProfileTerminalGapPaidCapPort* and its
  *exactTrichotomy* in
  UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean
  are the downstream paid-port interface and dispatch.

Reward boundedness is available through *quittingRewardBound*,
*abs_reward_le_quittingRewardBound*, and
*abs_quittingTerminalPayoff_le*.  A Lean implementation may use a strictly
positive bound such as

\[
  \max\{1,\text{quittingRewardBound}\}
\]

to avoid a vacuous \(M=0\) branch.

The new content is the quadratic separation (A), the ratio-chamber crossing
estimate (B), and the unconditional actual-source port theorem (C).  None is
assumed as a source field.

The checked stopping-law convexity module already gives a linear sandwich
relating total debt and terminal exploitability.  It does not contain (A),
the ratio-chamber crossing argument, or the off-minimum port floor (C3).
The scratch theorem named *FableThinSliceToken* is a different golden-ratio
fixed certificate and does not subsume these statements.  Conversely, this
packet does not strengthen the existing off-minimum paid-port trichotomy; it
supplies a new quantitative source for that interface.

## Proof

### Theorem A

Put

\[
  h:=D_*-\eta.
\]

Since \(\max_i d_i(\sigma)\le D(\sigma)\) for every actual profile,
\(h\ge0\).

Assume for contradiction that

\[
  h^2+4Mh-\eta^2<0.
\tag{1}
\]

This is equivalent to

\[
  \frac{h}{\eta+h}
  <
  \frac{\eta-h}{4M}.
\tag{2}
\]

In particular \(h<\eta\).  Choose

\[
  \frac{h}{\eta+h}
  <
  \theta
  <
  \min\left\{1,\frac{\eta-h}{4M}\right\}.
\tag{3}
\]

Take an actual profile \(\sigma\) with

\[
  D(\sigma)\le D_*+\delta=\eta+h+\delta,
\]

where \(\delta>0\) will be chosen sufficiently small.  Let \(p\) be a
maximum-debt player and write \(a=d_p(\sigma)\).  By the definition of
\(\eta\),

\[
  a\ge\eta.
\tag{4}
\]

For every \(i\ne p\),

\[
  d_i(\sigma)
  \le D(\sigma)-a
  \le h+\delta.
\tag{5}
\]

Choose a complete behavioral response of player \(p\) whose payoff is within
\(\zeta>0\) of \(B_p(\sigma)\), and mix the complete stopping laws with weight
\(\theta\).  Denote the mixed profile by \(\sigma^\theta\).

The mover's cap is unchanged because the opponents are unchanged.  The
stopping-law payoff is affine, so

\[
  d_p(\sigma^\theta)
  \le
  (1-\theta)d_p(\sigma)+\theta\zeta
  \le
  (1-\theta)(\eta+h+\delta)+\theta\zeta.
\tag{6}
\]

For \(i\ne p\), changing player \(p\)'s stopping law by mixture weight
\(\theta\) changes player \(i\)'s prescribed payoff by at most \(2M\theta\).
Uniformly over every behavioral replacement by \(i\), the same coupling
changes its payoff by at most \(2M\theta\), hence changes its complete cap by
at most \(2M\theta\).  Therefore

\[
  d_i(\sigma^\theta)
  \le d_i(\sigma)+4M\theta
  \le h+\delta+4M\theta.
\tag{7}
\]

By (3), the right sides of (6) and (7) are strictly below \(\eta\) when
\(\delta,\zeta\) are sufficiently small.  Hence

\[
  \max_i d_i(\sigma^\theta)<\eta,
\]

contradicting the definition of \(\eta\).  Thus

\[
  h^2+4Mh-\eta^2\ge0.
\]

Solving the quadratic inequality for \(h\ge0\) gives (A).

### Theorem B

Let \(\sigma^\theta\) be the profile obtained by mixing player \(p\)'s original
complete stopping law with its exact best response, with response weight
\(\theta\in[0,1]\).  Because the opponents of \(p\) do not change,

\[
  d_p(\sigma^\theta)=(1-\theta)a.
\tag{8}
\]

First, \(a>\eta\).  If \(a=\eta\), then immediately after entering the chord
the mover's debt is below \(\eta\).  The universal floor
\(\max_i d_i\ge\eta\) forces some nonmover's debt to be at least \(\eta\).
Stabilizing that label as \(\theta\downarrow0\) and using continuity gives a
second source debt at least \(\eta\), contradicting \(S<2\eta\).

Set

\[
  \theta_0:=\frac{a-\eta}{a}\in(0,1).
\tag{9}
\]

At \(\theta_0\), the mover debt is exactly \(\eta\).  For every
\(\theta>\theta_0\), the mover debt is below \(\eta\), so a nonmover has debt
at least \(\eta\).  Stabilize a nonmover label along
\(\theta\downarrow\theta_0\).  Continuity gives

\[
  D(\sigma^{\theta_0})\ge2\eta.
\tag{10}
\]

Total debt is convex along a stopping-law mixture.  Therefore

\[
  D(\sigma^{\theta_0})
  \le
  (1-\theta_0)D(\sigma)+\theta_0D(\rho).
\]

Combining with (10) and solving for \(D(\rho)\) gives

\[
  D(\rho)-S
  \ge
  \frac{a(2\eta-S)}{a-\eta}.
\tag{11}
\]

Because \(a\le S\) and \(z\mapsto z/(z-\eta)\) is decreasing on
\((\eta,\infty)\),

\[
  \frac{a(2\eta-S)}{a-\eta}
  \ge
  \frac{S(2\eta-S)}{S-\eta}.
\]

The exact best response gains \(a\), leaves \(B_p\) unchanged, and therefore
kills player \(p\)'s debt exactly.

### Theorem C

Choose actual profiles \(\sigma_n\) converging semantically to \(x\).  Pass to
a subsequence on which one player \(p\) maximizes debt for every \(n\), and
put

\[
  S_n:=D(\sigma_n),\qquad
  a_n:=d_p(\sigma_n).
\]

Then

\[
  S_n\to D_*,
  \qquad
  a_n\to a:=d_p(x),
  \qquad
  a\ge\eta.
\tag{12}
\]

In fact \(a>\eta\).  If \(a=\eta\), then every nonmover has limiting debt
strictly below \(\eta\), because \(D_*<2\eta\).  Choose a sufficiently small
fixed mixture weight toward \(o(1)\)-best replies.  The mover debt becomes
strictly below \(\eta\); the other debts remain below \(\eta\) by the same
uniform \(4M\theta\) estimate used in Theorem A.  This contradicts the
definition of \(\eta\).

Choose \(\zeta_n\downarrow0\) and \(\zeta_n\)-best responses
\(\tau_{p,n}\).  Put

\[
  \rho_n:=(\tau_{p,n},(\sigma_n)_{-p}),
  \qquad
  e_n:=d_p(\rho_n).
\]

Then

\[
  0\le e_n\le\zeta_n,
\tag{13}
\]

and (C1)--(C2) follow.

Along the complete stopping-law chord, the mover debt is exactly

\[
  d_p(\sigma_n^\theta)
  =
  (1-\theta)a_n+\theta e_n.
\tag{14}
\]

Let

\[
  \theta_n:=\frac{a_n-\eta}{a_n-e_n}.
\tag{15}
\]

For large \(n\), this lies in \((0,1)\), and

\[
  \theta_n\to\theta_*:=\frac{a-\eta}{a}\in(0,1).
\tag{16}
\]

Choose \(\widehat\theta_n>\theta_n\) with
\(\widehat\theta_n-\theta_n\to0\).  At
\(\widehat\theta_n\), the mover debt is below \(\eta\), so some nonmover debt
is at least \(\eta\).  Stabilize the nonmover label and pass to the limit.
Equation (14) shows that the mover debt tends to \(\eta\).  Consequently

\[
  \liminf_n D(\sigma_n^{\widehat\theta_n})\ge2\eta.
\tag{17}
\]

Convexity of total debt gives

\[
  D(\sigma_n^{\widehat\theta_n})
  \le
  (1-\widehat\theta_n)S_n
  +
  \widehat\theta_n D(\rho_n).
\tag{18}
\]

Taking lower limits and solving yields

\[
  \liminf_n D(\rho_n)
  \ge
  \eta\,\frac{2a-D_*}{a-\eta}.
\tag{19}
\]

Subtracting \(D_*\),

\[
  \liminf_n\bigl(D(\rho_n)-D_*\bigr)
  \ge
  \frac{a(2\eta-D_*)}{a-\eta}.
\tag{20}
\]

Since \(a\le D_*\) and \(z/(z-\eta)\) is decreasing,

\[
  \frac{a(2\eta-D_*)}{a-\eta}
  \ge
  \frac{D_*(2\eta-D_*)}{D_*-\eta}
  =
  \Delta_{\mathrm{port}}.
\tag{21}
\]

This proves (C3).  Compactness of the terminal-semantic carrier gives a
convergent target subsequence, and continuity of total debt gives (C4).

## Boundary tests

### The boundary \(D_*=\eta\)

This boundary is impossible by Theorem A.  The gap is quantitative:

\[
  D_*-\eta
  \ge
  \frac{\eta^2}{\sqrt{4M^2+\eta^2}+2M}.
\]

### The boundary \(D_*=2\eta\)

Here

\[
  \Delta_{\mathrm{port}}=0.
\]

No strict off-minimum conclusion follows from this proof.  The abstract debt
chord

\[
  (\eta,\eta,0,0)
  \longrightarrow
  (0,\eta,\eta,0)
\]

has maximum coordinate \(\eta\) and total debt \(2\eta\) at both endpoints.
It shows that the convex debt argument cannot replace \(D_*<2\eta\) by
\(D_*\le2\eta\).  This is only an abstract debt-vector boundary test; it is
not claimed to be realized by a positive-gap quitting game.

### Best-response nonattainment

Theorem B is explicitly conditional on exact attainment.  Theorem C uses
\(\zeta_n\)-best complete behavioral responses and takes an actual/carrier
limit.  It therefore makes no compactness or attainment claim about the
behavioral strategy space itself.

### Quantitative blow-up near the lower boundary

As \(D_*\downarrow\eta\),

\[
  \Delta_{\mathrm{port}}
  =
  \frac{D_*(2\eta-D_*)}{D_*-\eta}
\]

diverges.  Theorem A prevents the denominator from approaching zero
independently of \(M\).  Thus the formula is consistent with the bounded
semantic carrier.

## Adapter and consumer

Assume a Fin4 quitting game has no uniform-equilibrium payoff.  The checked
hard-residual reduction supplies

\[
  \eta>0,
\]

and the compact carrier machinery supplies a point \(x\) with

\[
  D(x)=D_*.
\]

If \(D_*<2\eta\), Theorem A first gives \(D_*>\eta\), so Theorem C applies.
Choose any fixed

\[
  0<\gamma<\eta.
\]

Each actual source profile \(\sigma_n\) has terminal exploitability at least
\(\eta>\gamma\), and its literal response target \(\rho_n\) satisfies
(C1)--(C3).  Retain this incoming full-response edge as the first component
of the adapter.

The target profile \(\rho_n\) is itself an actual profile, so its terminal
exploitability is also at least \(\eta>\gamma\).  Apply
*HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort* with source
profile \(\rho_n\).  This selects a terminal-gap first-disagreement observer
and row at \(\rho_n\), yielding a
*QuittingActualProfileTerminalGapPaidCapPort*.  By first discarding finitely
many indices, its initial semantic debt has the uniform off-minimum excess
\(\Delta_{\mathrm{port}}/2\) supplied by (C3).  Its observer and paid row may be
unrelated to \(p\), and its stored source gain is the chosen \(\gamma\), not
the \(\eta\)-scale gain of the incoming full response.

What is obtained is a quantitative entrance:

\[
  \text{ratio chamber}
  \Longrightarrow
  \begin{array}{c}
  \text{literal fixed-payer full-response edge}\\
  \text{to an off-minimum actual target}\\
  \text{together with a separately selected paid cap port at that target.}
  \end{array}
\]

The existing exact trichotomy may then be invoked.  This packet does not
consume all of its outputs.

## Lean handoff

A faithful implementation should separate the following declarations.

1. A game-independent bounded-mixture lemma: changing one player's complete
   stopping law with mixture weight \(\theta\) changes every other player's
   payoff and unrestricted behavioral cap by at most \(2M\theta\), hence
   changes every other debt by at most \(4M\theta\).
2. The universal quadratic separation theorem (A), stated using the terminal
   exploitability infimum and minimum total semantic debt.
3. The exact-attainment chord estimate (B), with the attainment hypothesis
   explicit.
4. The carrier/actual-source theorem (C), using approximate responses,
   stabilization of the principal debtor, the proof that its limiting debt is
   strictly greater than \(\eta\), and the approximate crossing parameters
   \(\widehat\theta_n\).
5. A Fin4 two-stage adapter from no uniform-equilibrium payoff and
   \(D_*<2\eta\): first retain the fixed-payer actual response edge
   \(\sigma_n\to\rho_n\), its asymptotic excess
   \(\liminf_n(D(\rho_n)-D_*)\ge\Delta_{\mathrm{port}}\), and the eventual
   concrete floor \(\Delta_{\mathrm{port}}/2\); then
   invoke
   *HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort* at
   \(\rho_n\), allowing the port observer and paid row to be newly selected.
   A small composite wrapper may retain both objects without identifying
   their payers or gains.

The implementation must not introduce an exact best-response selection in
the general theorem and must not infer convergence of strategies from
convergence of semantic pairs.

## Scope and nonclaims

This packet proves a theorem about unrestricted behavioral terminal caps and
actual one-player response profiles.  It does not prove:

- existence of a uniform-equilibrium payoff;
- consumption of the off-minimum paid port;
- a renewable well-founded descent;
- source-attached terminal atoms or deleted-law convergence;
- an executable multi-step chronology;
- exact attainment of complete best responses;
- or any claim in the boundary chamber \(D_*\ge2\eta\).

The exact achievement is

\[
  \boxed{
  \eta>0
  \Longrightarrow
  D_*-\eta\ge
  \sqrt{4M^2+\eta^2}-2M,
  }
\]

and

\[
  \boxed{
  \eta<D_*<2\eta
  \Longrightarrow
  \text{a literal paid response to an off-minimum target,
  followed by a paid cap port based at that target}.
  }
\]
## Lean formalization record

Pre-formalization packet SHA-256:
`daa1051755c9fbd265a8f8525c93f247740ef6c21eda5d114953e1ba0f0dc005`.

The debt-ratio chamber was integrated in production Lean by commit
`87d9ec3a762952f6a63f402afdeaae0e6cb73469`.

The strongest checked separation is
`quittingTerminalExploitabilityInf_sq_div_two_bound_le_debtSumInf_sub`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticDebtRatioSeparation.lean`),
which proves the bound `eta^2 / (2 * M)`. The packet's displayed
square-root bound is stated literally by
`quittingTerminalExploitabilityInf_sqrt_separation_le_debtSumInf_sub`.

The conditional exact-response estimate is stated literally by
`quittingTerminal_exactResponse_debtRatioCrossing`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticDebtRatioResponse.lean`).
It includes exact response gain, zero target payer debt, both ordered ratio
comparisons, and strict target total-debt increase.

The actual-source layer is owned by
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticDebtRatioCarrierResponse.lean`.
`nonempty_quittingDebtRatioCarrierSource` selects one fixed maximal-debt payer
on an actual cofinal carrier-realizing sequence, and
`nonempty_quittingDebtRatioApproximateResponseSource` attaches literal
approximate behavioral responses with a positive decreasing error sequence.
`QuittingDebtRatioApproximateResponseSource.ratioCrossing_le_liminf_target_debtExcess`,
`eventually_half_ratioCrossing_le_target_debtExcess`, and
`exists_targetCarrierCluster_debtSum_ge_ratioCrossing` state the liminf,
eventual concrete half-floor, and carrier-cluster conclusions.

For Fin4, `FinFourDebtRatioResponsePaidCapPort` and
`exists_eventually_nonempty_finFourDebtRatioResponsePaidCapPort`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourDebtRatioChamberPaidCapPort.lean`)
attach a separately selected actual paid-cap port at each sufficiently late
response target. The direct theorem
`exists_eventually_nonempty_finFourDebtRatioResponsePaidCapPort_of_no_uniformEquilibriumPayoff`
starts from failure of a uniform-equilibrium payoff, the invariant upper
chamber `D_* < 2 * eta`, a positive reward bound, and `0 < gamma < eta`; it
chooses the minimum carrier point internally and derives the strict lower
chamber from the checked separation.

The universal separation, its packet corollary, the exact-response estimate,
the carrier/approximate-response theorem, and the direct Fin4 wrapper have
`M` and `L`. The carrier realization and direct wrapper provide actual-source
`A`. The Fin4 port attachment provides branch-local paid-port `C`: it consumes
the actual response targets into the already checked paid-cap interface.

There is no downstream trichotomy-consumption or uniform-equilibrium
conclusion. In particular, this record does not consume the paid-cap
descent-or-inert alternatives, prove a renewable return, identify the port
observer with the response payer, or derive uniform-equilibrium existence.

