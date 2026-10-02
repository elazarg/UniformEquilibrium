# Mass-good cap switch or paid-row localization

Author: `CODEX_DIRICHLET`

## Status

Ordinary mathematics, not checked in Lean.  `RESEARCH-ONLY`.

This note addresses the receiving-clock quantifier gap in
`CODEX_JOULE__JENSEN_ACTIVE_PASSPORT_DICHOTOMY.md`.  The global Jensen
pair need not have its receiving clock in the mass-good set.  Conditioning
that pair on the mass-good set is not justified by the Jensen ledger: the
global Jensen excess can be carried by the complementary clocks.

There is nevertheless an exact two-stage repair.  Select a mass-good clock
first and inspect a coordinate of its total debt.  For an outsider, compare a
pure response selected near the cap at the original source with one selected
near the cap at the mass-good clock.  Either they make a charged response
square whose receiving clock is mass-good, or the source response remains
good at the clock and its advantage over the clock's prescribed mixture
gives a paid first-disagreement row there.  If the selected debt coordinate
is the clock owner, only the latter alternative is needed.

Thus the exact output is

\[
 \boxed{\text{source-to-mass-good response square}
 \quad\text{or}\quad
 \text{paid row based at the mass-good clock}.}
\]

This does not make the separated clock near-minimum and does not preserve its
singleton atom after the response replacement.  It is not a return theorem,
a uniform-equilibrium theorem, or an export candidate in its present form.

## 1. Exact separated-clock setting

Fix a Fin4 quitting reward table.  For every actual behavioral profile `P`
and player `k`, write

\[
 U_k(P)=\text{the prescribed terminal payoff},\qquad
 B_k(P)=\sup_{\tau_k}U_k(P[k\leftarrow\tau_k]),
\]

where the supremum is over all complete behavioral deviations, and put

\[
 d_k(P)=B_k(P)-U_k(P),\qquad D(P)=\sum_k d_k(P).
\tag{1.1}
\]

Assume the literal infimum over actual profiles is

\[
 D_*=\inf_P D(P)>0.
\tag{1.2}
\]

Let `S_n` be actual profiles satisfying `D(S_n) -> D_*`.  Fix an owner `j`,
finite anchors `a_n`, and the anchored conditional disintegration from the
Jensen note.  Thus `alpha_n` is the conditional law of the owner's clock on

\[
 \{a_n,a_n+1,\ldots\}\cup\{\mathsf{Never}\},
\]

and `P_(n,t)` copies the whole source strictly before `a_n`, replaces only
the owner after the anchor by Continue through `t-1` and sure Quit at finite
`t`, and leaves all opponents unchanged.  For a fixed outsider response,
the source is the `alpha_n`-mixture of these clock components.

Let

\[
 G_n=\{t<\infty:\alpha_n(t)>0,\quad
       m_{n,t}\ge\mu/2\},
\tag{1.3}
\]

where `m_(n,t)` is the singleton-`{j}` stage mass at `t`.  The anchored
mass ledger gives `G_n != empty`.  Work in the separated arm: after a strict
subsequence, there is `eta>0` such that

\[
 t\in G_n\quad\Longrightarrow\quad
 D(P_{n,t})\ge D_*+\eta.
\tag{1.4}
\]

Set

\[
 \rho:=D_*+\eta,\qquad
 \ell:=\rho/4,\qquad
 g_0:=\ell/4=\rho/16.
\tag{1.5}
\]

Select any `t_n in G_n` and write `T_n=P_(n,t_n)`.  Then `t_n` is finite,
`T_n` retains the literal source prefix and every opponent, and

\[
 m_{n,t_n}\ge\mu/2,\qquad D(T_n)\ge\rho.
\tag{1.6}
\]

Because there are four players and all debts are nonnegative, some player
`p_n` satisfies

\[
 d_{p_n}(T_n)\ge\ell.
\tag{1.7}
\]

Pass to a strict subsequence fixing `p_n=p`.  Choose positive errors
`epsilon_n -> 0` with

\[
 \epsilon_n\le\ell/8.
\tag{1.8}
\]

All pure response labels below range over `Option Nat`; `none` is Never.
Pure-time extremality is used only to select an `epsilon_n`-optimal witness
for an unrestricted behavioral cap.

## 2. The outsider priority split

Suppose first that the fixed player `p=i` is an outsider, `i != j`.  Choose
pure-time responses `q_n^-` and `q_n^+` such that

\[
 \begin{aligned}
 B_i(S_n)-U_i(S_n[i\leftarrow Q_{q_n^-}])&\le\epsilon_n,\\
 B_i(T_n)-U_i(T_n[i\leftarrow Q_{q_n^+}])&\le\epsilon_n.
 \end{aligned}
\tag{2.1}
\]

For brevity put

\[
 V_{S,n}(q)=U_i(S_n[i\leftarrow Q_q]),\qquad
 V_{T,n}(q)=U_i(T_n[i\leftarrow Q_q])
\tag{2.2}
\]

and define the receiving response increment

\[
 A_n:=V_{T,n}(q_n^+)-V_{T,n}(q_n^-).
\tag{2.3}
\]

There are two exhaustive cases.

### 2.1. Cap switch: a square received in `G_n`

If

\[
 A_n\ge\ell/2,
\tag{2.4}
\]

then the source optimality of `q_n^-` and the cap upper bound on every pure
response give

\[
 V_{S,n}(q_n^+)-V_{S,n}(q_n^-)\le\epsilon_n.
\tag{2.5}
\]

Consequently the owner-clock/outsider-response square satisfies

\[
 \begin{aligned}
 &[V_{T,n}(q_n^+)-V_{T,n}(q_n^-)]
   -[V_{S,n}(q_n^+)-V_{S,n}(q_n^-)]\\
 &\hspace{30mm}\ge \ell/2-\epsilon_n
 \ge 3\ell/8>g_0.
 \end{aligned}
\tag{2.6}

The receiving edge itself is at least `ell/2`.  Both correct response
endpoints have vanishing observer debt:

\[
 d_i(S_n[i\leftarrow Q_{q_n^-}])\le\epsilon_n,
 \qquad
 d_i(T_n[i\leftarrow Q_{q_n^+}])\le\epsilon_n.
\tag{2.7}

Indeed, replacing a player's own prescribed strategy leaves that player's
cap unchanged.  The four corners in (2.6) are actual profiles.  The two
replacements commute because `i != j`.  More precisely, the two base
profiles share the anchored source prefix, and after either fixed outsider
replacement the corresponding two corners still agree literally apart from
the named owner-clock replacement.  The outsider replacement itself need
not preserve the original prefix or singleton mass.

Unlike the pair selected from the global Jensen average, the receiving base
here is the preselected `T_n` with

\[
 t_n\in G_n,\qquad m_{n,t_n}\ge\mu/2,\qquad
 D(T_n)\ge D_*+\eta.
\tag{2.8}
\]

### 2.2. No cap switch: an installed-source-cap paid row

Suppose instead that

\[
 A_n<\ell/2.
\tag{2.9}
\]

The response selected at the source then remains within
`epsilon_n+ell/2` of the cap at the receiving clock:

\[
 \begin{aligned}
 B_i(T_n)-V_{T,n}(q_n^-)
 &=B_i(T_n)-V_{T,n}(q_n^+)+A_n\\
 &<\epsilon_n+\ell/2.
 \end{aligned}
\tag{2.10}

Combining this with the selected debt coordinate (1.7) gives

\[
 \begin{aligned}
 V_{T,n}(q_n^-)-U_i(T_n)
 &=d_i(T_n)-[B_i(T_n)-V_{T,n}(q_n^-)]\\
 &>\ell/2-\epsilon_n\ge3\ell/8.
 \end{aligned}
\tag{2.11}

Disintegrate the prescribed strategy of `i` in `T_n` into its pure-time
stopping law.  The exact expectation identity says that `U_i(T_n)` is the
expectation of `V_(T,n)` under that law.  Pure-time payoffs are bounded, so
there is a support atom `q_n^0` at most equal to the expectation:

\[
 V_{T,n}(q_n^0)\le U_i(T_n).
\tag{2.12}

Because the owner-clock replacement leaves the outsider's prescribed
strategy unchanged, this is also an atom of the prescribed stopping law of
`i` in `S_n`.  Equations (2.11)--(2.12) give

\[
 V_{T,n}(q_n^-)-V_{T,n}(q_n^0)>3\ell/8>g_0.
\tag{2.13}

Hence the checked first-disagreement decoder applies at the literal
mass-good base `T_n`, with source witness `q_n^0`, receiving witness
`q_n^-`, and gain `g_0`.  It produces

\[
 \operatorname{QuittingPaidFirstDisagreementRow}
   (T_n,i,g_0).
\tag{2.14}

This fallback retains a named response that is `epsilon_n`-cap-attaining at
the original near-minimum source:

\[
 d_i(S_n[i\leftarrow Q_{q_n^-}])\le\epsilon_n.
\tag{2.15}

At the receiving response endpoint one has only the exact bound

\[
 d_i(T_n[i\leftarrow Q_{q_n^-}])
 <\ell/2+\epsilon_n,
\tag{2.16}

not vanishing debt.  The paid-row consumer does not require more.

## 3. The owner coordinate

Suppose now that the fixed player in (1.7) is the owner, `p=j`.  Choose a
pure-time `q_n^-` within `epsilon_n` of `B_j(S_n)`.  The source and every
owner-clock component have exactly the same opponents.  Therefore, after
replacing `j` by any fixed response `Q_q`, the resulting profiles are
identical:

\[
 V_{T,n}(q)=V_{S,n}(q),\qquad B_j(T_n)=B_j(S_n).
\tag{3.1}

Thus `q_n^-` is also `epsilon_n`-optimal at `T_n`.  Apply the prescribed-law
expectation identity at `T_n` to choose a pure support atom `q_n^0` with

\[
 V_{T,n}(q_n^0)\le U_j(T_n).
\tag{3.2}

Then

\[
 V_{T,n}(q_n^-)-V_{T,n}(q_n^0)
 \ge d_j(T_n)-\epsilon_n
 \ge\ell-\epsilon_n>g_0.
\tag{3.3}

This again gives a paid first-disagreement row of gain `g_0` based at the
mass-good profile `T_n`, and `q_n^-` has debt at most `epsilon_n` after being
installed at both `S_n` and `T_n`.

There is deliberately no claim that the owner's first-disagreement date is
at most the forced clock `t_n`.  The clock component's prescribed owner
strategy is overwritten when evaluating an owner deviation, so the outsider
screening argument used below is unavailable.

## 4. Exhaustive mass-good localization theorem

Combining the finite player pigeonhole with a further binary subsequence in
the outsider case proves the following exact statement.

### Theorem 4.1 (mass-good cap switch or paid row)

Under (1.1)--(1.8), after passing to a strict subsequence there are finite
supported clocks `t_n in G_n`, one fixed player `p`, and pure response labels
such that exactly one of the following persistent alternatives holds.

1. **Owner installed-cap row.**  `p=j`.  A response `epsilon_n`-optimal at
   the original source remains `epsilon_n`-optimal at `T_n` and, against a
   pure support atom of the prescribed owner law at `T_n`, gives a paid
   first-disagreement row at `T_n` of gain `g_0`.

2. **Outsider co-localized square.**  `p=i != j`.  Equations
   (2.4)--(2.8) hold.  In particular, the receiving clock of the charged
   response square belongs to `G_n`, its square charge is at least `g_0`,
   and the source and receiving response endpoints have observer debt
   tending to zero.

3. **Outsider installed-source-cap row.**  `p=i != j`.  Equations
   (2.9)--(2.16) hold.  A response `epsilon_n`-optimal at the original source
   is the receiving witness of a paid first-disagreement row at `T_n` of
   gain `g_0`.

Every alternative is based at the same kind of actual mass-good/off-minimum
component:

\[
 m_{n,t_n}\ge\mu/2,\qquad
 D(T_n)\ge D_*+\eta,qquad
 g_0=(D_*+\eta)/16>0.
\tag{4.1}
\]

The result does not assert that the particular pair extracted by the global
Jensen expectation can be conditioned into `G_n`.  It constructs a new
source-to-clock square after selecting `T_n`, or returns a paid row already
accepted by the checked cap-lifted consumer.

## 5. First-disagreement chronology and probability mode

In Alternatives 2 and 3, both row witnesses belong to the outsider
`i != j`, and the receiving owner clock `t_n` is finite.  A positive payoff
edge forces the two pure responses to have a finite first disagreement
`r_n`.  Moreover,

\[
 r_n\le t_n.
\tag{5.1}
\]

Indeed, if the outsider responses agreed through `t_n`, all absorption
before `t_n` would be common to them, and conditional on reaching `t_n` the
owner Quits surely.  Their receiving payoffs would be equal, contradicting
the positive edge.  This is a literal deterministic-clock statement, not an
almost-sure selection assertion.  Never is allowed for either response; a
positive edge still makes their first disagreement finite.

All mass statements in the theorem concern the actual base `T_n`.  No claim
is made that `T_n[i <- Q_q]`, for either response corner, retains the
singleton mass `m_(n,t_n)`: an outsider may Quit before or with `j` and
destroy that atom.  The row is co-located with the mass-good base, not with a
mass-good response endpoint.

## 6. Exact checked consumer

Assume a compact-carrier semantic minimum realizing `D_*>0` has been chosen.
In Alternatives 1 and 3, (2.14) or (3.3) directly supplies the row field of a
`QuittingPaidCapLiftedSource` whose literal profile field is `T_n` and whose
gain is the fixed `g_0`.  In Alternative 2, apply
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` to the
receiving edge, again at `T_n` and with gain `g_0`.

For every alternative,
`QuittingPaidCapLiftedSource.nonempty_summablePort` constructs a port and
`QuittingPaidCapLiftedSource.exactTrichotomy` returns charged near-return,
quantitative debt descent, or inert stall.  Under the positive-minimum/no-
uniform-payoff hypotheses used in the current program, the charged arm is
excluded by its uniform-equilibrium payoff, leaving descent or inert stall
after a subsequence.

This consumer does not turn the theorem into a return result.  A descent
limit need not be an actual regenerated profile and can lose the selected
singleton atom.  Inertness retains the semantic pair of the selected
off-minimum base, not the original near-minimum source.  Thus the paid row is
consumable in the precise checked sense while the source/atom/minimum
regeneration problem remains.

There is also a checked generic route from a global terminal exploitability
gap to a paid row at every actual profile,
`HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at`.  The extra
content here is therefore not bare paid-row existence.  It is the priority
split retaining either the full source-to-mass-good response square with two
vanishing endpoint debts, or a paid row whose high response was selected at
the original source cap.

## 7. Attachment to the current minimum-singleton chronology

For a current `FinFourMinimumAtomProducer`, choose a chronology from
`FinFourMinimumAtomProducer.nonempty_chronology` and set

\[
 S_n=\operatorname{prefixedProfile}
   (\text{chronology.profiles}_n,\text{chronology.roots}_n),
 \qquad a_n=|\text{chronology.roots}_n|.
\tag{7.1}
\]

The field `FinFourMinimumAtomChronology.prefix_debt_tendsto` gives
`D(S_n)->D_*`, while
`FinFourMinimumAtomChronology.tendsto_prefixedTailMass` supplies the positive
post-anchor singleton floor after discarding finitely many ranks.  The
anchored clock components used above therefore retain the current root word
literally and leave every opponent unchanged.

In the separated arm of the Jensen dichotomy, Theorem 4.1 now gives either a
source-attached square received at an actual mass-good clock, or a paid row
at such a clock.  It does not claim that
`FinFourOwnerCompressedSingletonEndpoint.rootStack_nash` survives the owner
clock replacement: that declaration concerns the unmodified suffix.  Nor
does the theorem provide a new minimum singleton chronology starting from
`T_n`.  These are the remaining attachment boundaries.

## 8. Boundary checks

1. **Owner curvature is identically zero.**  If the large debt coordinate
   is `j`, all fixed owner-deviation payoffs are identical at `S_n` and
   `T_n`, because the opponents are identical.  A source-to-clock owner
   response square cannot carry positive charge.  The installed-cap paid-row
   alternative is therefore essential, not an artifact of the proof.

2. **Threshold equality is harmless.**  Put `A_n=ell/2` in the square arm.
   The charge is at least `ell/2-epsilon_n>=3ell/8`, still strictly above
   `g_0=ell/4`.  The complementary strict inequality yields the strict edge
   in (2.13).

3. **No attainment is used.**  Both high responses are only
   `epsilon_n`-optimal.  The low response `q_n^0` is obtained from the exact
   prescribed stopping-law expectation, not by assuming a minimizing pure
   response exists.

4. **The global Jensen pair is untouched.**  No sign is imposed on its
   receiving-clock contribution inside `G_n`, and no conditional Jensen
   identity is asserted.  The construction changes the order of selection:
   mass-good clock first, response comparison second.

These checks also explain why no rational counterexample of the requested
type is needed: the stronger square-or-consumable-row split is valid even
though direct conditioning of the original Jensen selector remains
unsupported.

## 9. Declarations and files inspected

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`
  and `bddAbove_range_quittingPureTimeDeviationPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`;
- `Math.ProbabilityMassFunction.exists_mem_support_le_expect` in
  `MathUE/ProbabilityMassFunction/BoundedSupportAverage.lean`;
- `Math.Optimization.OrientedSupremumWitnessSwitch` and
  `Math.Optimization.orientedSupremumWitnessSwitch_of_regret` in
  `MathUE/Optimization/SupremumTwoResetWitnessSwitch.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `QuittingPaidCapLiftedSource.nonempty_summablePort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
- `QuittingPaidCapLiftedSource.exactTrichotomy` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
- `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`;
- `FinFourMinimumAtomProducer.nonempty_chronology`,
  `FinFourMinimumAtomChronology.prefix_debt_tendsto`,
  `FinFourMinimumAtomChronology.tendsto_prefixedTailMass`, and
  `FinFourOwnerCompressedSingletonEndpoint.rootStack_nash` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `CODEX_JOULE__JENSEN_ACTIVE_PASSPORT_DICHOTOMY.md`; and
- `CODEX_RESPONSE_SWITCH__ADJACENT_REACTIVATION_CLOCK_OR_BUBBLE.md`,
  especially its mass-good switch boundary.

## 10. Verdict and next question

The Jensen receiving-clock gap admits the exact stronger repair in Theorem
4.1.  It does **not** admit, from the current ledger alone, the narrower
claim that the original globally averaged Jensen pair can be chosen with its
receiver in `G_n`.

There is no strict export-worthy contraction yet.  The local priority split
is a plausible future formalization target, but bare paid-row existence is
already checked and the new square branch has no checked regeneration
consumer.  The next concrete question is whether Alternative 2's response
endpoint can be screened or rebased while retaining a quantitative fraction
of `m_(n,t_n)`, or whether Alternative 3's installed source-cap label can be
carried through the cap-lifted descent/inert output.  Either would be a new
adapter rather than another Jensen selection argument.
