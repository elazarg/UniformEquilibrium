# Feedback on anchored Jensen dichotomy: active singleton passport or separated response square

Target: [`CODEX_JOULE__JENSEN_ACTIVE_PASSPORT_DICHOTOMY.md`](../notes/CODEX_JOULE__JENSEN_ACTIVE_PASSPORT_DICHOTOMY.md)
Reviewer: `CODEX_DIRICHLET`
Verdict: `NEEDS_REPAIR` (`REVISE`)

## Claim checked

The note starts from actual Fin4 profiles with total unrestricted behavioral
debt tending to a positive literal infimum and with a fixed owner's
post-anchor singleton mass bounded below. It conditionally disintegrates that
owner's post-anchor stopping law into finite deterministic clocks and Never,
then claims an exhaustive strict-subsequence alternative:

1. a supported mass-good clock is itself near-minimum and carries a fixed
   executable deviation gain; or
2. all mass-good clocks are uniformly separated from the minimum, while one
   fixed outsider carries an oriented pure-time response square with a fixed
   positive charge and approximately cap-attaining response endpoints.

The note further attaches this abstraction to one
`FinFourMinimumAtomChronology`, passes the response edge through the paid-cap
trichotomy, and gives a two-date zero-minimum regression.

I checked the conditional disintegration, the exact Jensen ledger, the
mass-good selection, both alternatives and all constants, the paid-cap
composition, the chronology attachment, and the regression. I did not run
Lean or check any declaration beyond the narrow source set listed below.

## Independent check

### 1. Anchored conditional disintegration and Jensen ledger

Let `alpha_n` be the owner's stopping law conditional on its survival to the
anchor. Every component copies the whole source before the anchor. Therefore
the terminal contribution from absorption before the anchor is literally the
same in every component, while on anchor survival the conditional clock law
reproduces the owner's source hazard. This remains true after replacing a
fixed outsider by any complete behavioral strategy: that replacement changes
the common reach probabilities, but not the owner's independent conditional
hazard decomposition. Thus the payoff affinities used in (2.1) and in the
fixed-response calculation (3.17) are valid.

The owner's cap is component-independent because its opponents are unchanged.
For an outsider, each fixed complete-deviation payoff is affine in the owner
clock law, and supremum after averaging is at most the average of the
component suprema. Hence, writing `U`, `B`, and `D` as in the note,

\[
\begin{aligned}
 \int (D(P_{n,t})-D_*)\,d\alpha_n(t)
 &= \sum_k\left(\int B_k(P_{n,t})\,d\alpha_n(t)-U_k(\sigma_n)\right)-D_*\\
 &= D(\sigma_n)-D_*+
    \sum_{i\ne j}\left(\int B_i(P_{n,t})\,d\alpha_n(t)-B_i(\sigma_n)\right)\\
 &= e_n+J_n.
\end{aligned}
\]

This verifies (2.5) with unrestricted behavioral caps. Bounded rewards make
all countable expectations harmless. The existing checked mixture lemmas are
binary; the countable anchored, arbitrary-observer form used here is valid
ordinary mathematics but is not itself one of the named checked declarations.

### 2. Mass-good selection and exhaustive split

Because `m_(n,infinity)=0`, `0 <= m_(n,t) <= 1`, and
`E_alpha[m]=M_n >= mu`,

\[
 \mu\le \alpha_n(G_n)+(1-\alpha_n(G_n))\mu/2
\]

gives

\[
 \alpha_n(G_n)\ge \beta:=\frac{\mu}{2-\mu}>0.
\]

In particular `G_n` is nonempty and contains only finite clocks. Since every
component is actual, `delta_(n,t)>=0`. The split according to
`liminf inf_(t in G_n) delta_(n,t)` is exhaustive. In the zero-liminf arm, an
approximate infimum selector in `G_n` gives (3.4). In the positive-liminf arm,
after a tail/subsequence one has `delta_(n,t)>=eta` on `G_n`, and therefore

\[
 e_n+J_n=\mathbb E\delta_{n,T}
 \ge \mathbb E[\delta_{n,T}{\bf 1}_{G_n}]
 \ge \beta\eta.
\]

Thus eventually `J_n>=beta*eta/2`. The separation-to-Jensen-floor step and
its constants are correct.

### 3. Alternative A: marked-root localization

At the suffix starting at the selected finite owner clock, the owner Quits
surely. Joint Continue mass is therefore zero. The exact cap recursion gives
total suffix debt equal to the sum of the four root defects against the
post-tail cap. The suffix is an actual profile, so that sum is at least
`D_*`; one coordinate has defect at least `D_*/4`.

If that coordinate is an outsider, the sure-quitting owner makes the
outsider's opponent-Continue mass zero. The cap continuation endpoint and
literal continuation endpoint coincide, so a Boolean root endpoint realizes
the defect. If the coordinate is the owner, Continue at the mark followed by
a post-mark response within `D_*/8` of the tail cap realizes at least
`D_*/8` locally. The live probability of the mark is at least the selected
singleton stage mass `mu/2`. Consequently the global gain is at least

\[
 (\mu/2)(D_*/8)=\mu D_*/16.
\]

Splicing after the unchanged past is a legal complete unilateral behavioral
deviation. Finite pigeonhole then fixes the gaining player. Alternative A and
its constant pass.

### 4. Alternative B: response-square ledger

After fixing an outsider with `J_(n,i)>=h:=beta*eta/6`, choose for every
supported owner clock `u` a pure-time response `q_(n,u)` within `epsilon_n`
of its unrestricted cap. Pure-time extremality justifies this choice,
including Never. For independent `T,S` with law `alpha_n`, fixed-response
affinity gives

\[
 \mathbb E V_{n,T}(q_{n,S})\le B_i(\sigma_n),
 \qquad
 \mathbb E V_{n,T}(q_{n,T})
 \ge \mathbb E B_i(P_{n,T})-\varepsilon_n.
\]

Hence a supported ordered pair `(s_n,t_n)` satisfies the receiving-edge
bound `>=h-epsilon_n`. Approximate optimality at `s_n` gives the other oriented
edge `<=epsilon_n`. With `epsilon_n<=h/4` and `g=h/2`,

\[
 V_{t_n}(q_n^+)-V_{t_n}(q_n^-)\ge g,
\]

and

\[
 [V_{t_n}(q_n^+)-V_{t_n}(q_n^-)]
 -[V_{s_n}(q_n^+)-V_{s_n}(q_n^-)]\ge g.
\]

The orientation and constants in (3.16)--(3.20) are correct. Replacing an
outsider's own strategy leaves its cap unchanged, so the two endpoint debts
in (3.10) are indeed at most `epsilon_n`.

The crucial limitation is that this pair selection is over the **entire**
support of `alpha_n`, not over `G_n`. Nothing proved in (3.13)--(3.20) implies

\[
 t_n\in G_n,
 \qquad t_n<\infty,
 \qquad\text{or}\qquad D(P_{n,t_n})\ge D_*+\eta.
\tag{R}
\]

The note correctly acknowledges in Section 7 that the square may be
mass-poor, but Section 4 later calls its receiving component off-minimum. That
does not follow.

### 5. First-disagreement chronology

The checked decoder returns `row.start`, the first finite disagreement of the
two ordered pure-time witnesses. If the receiving owner clock `t_n` is finite
and `row.start>t_n`, the two outsider responses agree through date `t_n`;
the owner's sure Quit absorbs there, so their receiving payoffs are equal,
contradicting (3.8). Thus

\[
 t_n<\infty\quad\Longrightarrow\quad row.start\le t_n
\tag{C}
\]

is valid.

But the selection does not prove `t_n<infinity`: Never is in the support
space and can be the receiving component. Accordingly, (3.11) needs an
explicit type and case split. It is correct only if owner clocks are ordered
in the extended order `Nat union {infinity}`, where every finite
`row.start<=infinity` tautologically; if (3.11) is intended as a natural-date
bound, the theorem is unsupported. The prose proof treats only the finite
case. The safe statement is (C), plus the tautological Never case in the
extended order.

### 6. Paid-cap composition

A compact-carrier minimum, the positive value `D_*`, the receiving profile,
and the decoded paid row do define a `QuittingPaidCapLiftedSource`. Its
summable port and exact trichotomy are checked. The charged arm contains a
uniform-equilibrium payoff and is incompatible with `D_*>0`; binary infinite
pigeonhole then leaves quantitative descent at every retained rank or inert
stall at every retained rank.

What survives in the inert arm is equality to the selected receiving
profile's semantic pair. Because (R) is unavailable, it is not necessarily
an "off-minimum receiving component." The accurate conclusion is:

- if `t_n in G_n`, inertness stays at a component at least `eta` above the
  minimum and carrying the mass floor;
- if `t_n notin G_n`, no mass floor or fixed distance from the minimum is
  supplied;
- in either case, the port does not co-realize all of the original minimum
  source, marked singleton atom, and response square.

The last bullet is the sound obstruction; the stronger off-minimum wording
must be removed.

### 7. Minimum-chronology attachment

For a singleton `FinFourMinimumAtomProducer`, one chronology supplied by
`FinFourMinimumAtomProducer.nonempty_chronology` has literal prefixed profiles
whose debt tends to the literal infimum. Its `prefixedTailMass` is exactly the
post-root-word atom mass, and
`FinFourMinimumAtomChronology.tendsto_prefixedTailMass` sends it to the fixed
positive minimum-law singleton coordinate. After discarding finitely many
ranks and choosing any fixed smaller positive `mu`, these are exactly
(1.2)--(1.3), with anchor equal to the retained root-word length.

The note also states the essential scope restriction correctly:
`FinFourOwnerCompressedSingletonEndpoint.rootStack_nash` concerns the
unmodified suffix only. None of the disintegrated clock components inherits
that cap--Nash stack certificate.

### 8. Regression

The four-player example is correct. With active rewards equal to one exactly
on coalitions containing both active players, matching either of the
opponent's equiprobable dates gives cap `1/2`, and no behavioral stopping law
can exceed that matching probability. Thus the mixed source has zero debt.
At either deterministic owner component the outsider's prescribed payoff is
`1/2` and its cap is one, while the owner and dummies have zero debt. Hence
both component debts and the Jensen gap are `1/2`.

Only the date-zero owner component is mass-good. The two pure responses have
receiving edge one, reverse edge minus one, and square charge two; both
correctly matched response endpoints have zero outsider debt. This faithfully
extends the checked two-player `StoppingLawMixtureKink` calculation by passive
zero-payoff players. It is explicitly a `D_*=0` boundary test, not evidence
against a positive-minimum theorem.

## Source audit

I inspected these declarations in place:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`
  (`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`);
- `quittingTerminalPayoff_stoppingLawMixture_eq`,
  `quittingContinuationBestResponseValue_stoppingLawMixture_le`, and
  `quittingTerminalSemanticDebt_stoppingLawMixture_eq_self`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`);
- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`);
- `quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul`
  and the literal/cap surcharge comparison
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`);
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`);
- `QuittingPaidCapLiftedSource.nonempty_summablePort`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`)
  and `QuittingPaidCapLiftedSource.exactTrichotomy`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`);
- `quittingTerminalDebtSum_eq_terminalSemanticDebtSum` and
  `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`);
- `exists_minimum_terminalSemanticLawCarrier_of_debtSumInf_pos`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`);
- `exists_quittingAnchoredSingletonClockCompression` and its exact mass,
  tail, and owner-cap preservation lemmas
  (`Research/Quitting/AnchoredSingletonClockCompression.lean`);
- `FinFourMinimumAtomProducer.nonempty_chronology`,
  `FinFourMinimumAtomChronology.tendsto_prefixedTailMass`, and
  `FinFourOwnerCompressedSingletonEndpoint.rootStack_nash`
  (`Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`);
- the declarations in namespace `StoppingLawMixtureKink`
  (`Research/Quitting/StoppingLawMixtureWitnessStrata.lean`); and
- the current clock-compression, paid-port, normalized-passport, and
  response-chord boundaries in `docs/FRONTIER.md` and `docs/TOOLKIT.md`.

These sources support the scoped claims above. They do not supply the missing
localization (R), nor do they turn the response square into a source-faithful
return.

## Findings

1. **PASS:** the anchored conditional terminal-law decomposition is sound,
   including after any fixed outsider complete behavioral replacement.
2. **PASS:** the unrestricted-cap Jensen ledger (2.5), mass-good bound (3.3),
   and separation-to-`J_n` floor (3.13)--(3.16) are exact.
3. **PASS:** Alternative A's root-defect localization and
   `mu*D_*/16` executable-gain floor are correct.
4. **PASS:** Alternative B's outsider selection, square orientation,
   `g=beta*eta/12`, and the two `epsilon_n` endpoint-debt bounds are correct.
5. **REVISE:** the selected square receiver is not shown mass-good, finite,
   or off-minimum. The finite first-disagreement argument proves only (C),
   unless (3.11) is explicitly interpreted in the extended clock order.
6. **REVISE:** Section 4's assertion that inertness stays at an off-minimum
   receiving component is unsupported. The weaker no-co-realization
   conclusion remains valid.
7. **PASS:** the minimum-singleton chronology attachment and the warning that
   root-stack Nash does not transport to changed clock components are correct.
8. **PASS:** the exact regression and its `D_*=0` limitation are correct.

## Suggested next move

Revise Theorem 3.1 so owner clocks are explicitly elements of
`Nat union {infinity}`. Replace (3.11) by the conditional finite statement
(C), or define the extended order and prove the finite and Never cases
separately. In Section 4, replace every unqualified "off-minimum receiving
component" by "selected receiving component" and retain the case split above.

If a mass-good finite receiver is desired, it requires a genuinely new
weighted localization lemma; (3.13)--(3.20) do not provide it. Do not repair
the statement by silently declaring the selected support pair to lie in
`G_n`.

## Export assessment

**Research-only; no export-worthy strict contraction.** Even after the scope
repairs, Alternative B supplies a paid response square at an arbitrary
supported clock and the already checked generic paid-cap trichotomy. It does
not produce a source-faithful return, an intrinsic lower rank, a terminal
approximation, or a uniform-equilibrium payoff, and it does not close a named
question. The zero-minimum regression is a useful boundary test but does not
exclude a positive-minimum route.

The note should remain in `notes/`. The core dichotomy is worth preserving
after revision, but it does not make the qualifying strict boundary change
and has no downstream semantic consumer of either surviving hard branch, as
required by export-gate item 4.
