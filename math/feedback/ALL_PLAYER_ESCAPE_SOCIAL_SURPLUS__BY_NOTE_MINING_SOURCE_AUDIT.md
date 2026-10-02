# Source audit: all-player escape social-surplus account

Reviewer: `GATE_SOURCE_AUDIT`

Sources audited:

- [`CHATGPT_EXTERNAL__ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS_ACCOUNT.md`](../notes/CHATGPT_EXTERNAL__ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS_ACCOUNT.md);
- [`ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS__BY_NOTE_MINING_FALSIFIER.md`](ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS__BY_NOTE_MINING_FALSIFIER.md).

Verdict: **PASS for export after assembling the corrected packet described by
the falsifier review.**  The escaped-mass sign, prescribed-payoff moment,
unrestricted-cap lower semicontinuity, debt-jump identity, and minimum-value
attainment theorem are all correct.  I found no checked duplicate.  The result
strictly reduces the all-nonproper nonattainment seam and solves a genuine
aggregate-reward sign chamber.

The current author note is not itself the final packet: its bubble proof and
carrier adapter are abbreviated, and its headline special case unnecessarily
assumes a positive minimum.  Those are presentation/scope repairs, not a
mathematical failure.  This audit treats the theorem in the corrected form
stated by the falsifier.

## Exact corrected theorem

Let `I` be a finite nonempty player set.  For each nonempty coalition `S`, let
`r(S)` be its reward vector, and let all-Never pay zero.  Let

\[
 \operatorname{Sem}(\sigma_n)=(U^n,B^n)\longrightarrow z=(u,b)
\]

for actual behavioral profiles.  Pass to a subsequence on which every
player's complete stopping law converges weakly on
`WithTop Nat` to a compact stopping law `mu_i`.  Reconstruct the actual product
behavioral profile `barSigma` from these limiting laws.  Pass to a further
subsequence on which the complete finite terminal-outcome laws converge to
`mStar`; write `m` for the actual complete outcome law of `barSigma`.

For every nonempty coalition define

\[
 e(S)=m^*(S)-m(S),
 \qquad R(S)=\sum_i r_i(S).
\]

Then:

1. `e(S)>=0` for every nonempty `S`;
2. for every player `i`,
   \[
     u_i-U_i(\bar\sigma)=\sum_{S\ne\varnothing}e(S)r_i(S);
   \]
3. if every own singleton reward is nonnegative, then
   \[
     B_i(\bar\sigma)\le b_i;
   \]
4. putting `Delta_i=b_i-B_i(barSigma)>=0`,
   \[
     D(\bar\sigma)-D(z)
       =\sum_{S\ne\varnothing}e(S)R(S)-\sum_i\Delta_i; \tag{A}
   \]
5. if `z` globally minimizes total semantic debt on the carrier, then
   \[
     \sum_Se(S)R(S)\ge\sum_i\Delta_i\ge0. \tag{B}
   \]
   If no actual profile attains the minimum *value*, the first comparison is
   strict.

Consequently, under

\[
 r_i(\{i\})\ge0\quad\text{for every }i,
 \qquad
 \sum_i r_i(S)\le0\quad\text{for every nonempty }S, \tag{C}
\]

the global minimum total-debt value is attained by an actual behavioral
profile.  Positivity of that minimum is not needed.  The actual profile may
have a different semantic pair and terminal law from the originally selected
carrier minimizer.

## 1. Carrier-to-selected-law adapter

The required source sequence exists without an added compactness assumption.
`exists_minimum_quittingTerminalSemanticDebtSum` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`
selects a global carrier minimizer.  For any carrier point,
`nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier` in
`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`
provides:

- one actual realizing profile sequence;
- one strict subsequence;
- simultaneous weak limits of all complete stopping laws; and
- convergence of the full semantic pairs to the selected point.

The selected structure does not yet contain the outcome-law limit required by
the escape account.  This is not a gap: the complete outcome laws belong to
the finite compact simplex by
`quittingTerminalOutcomeMass_mem_stdSimplex` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean`.  Passing to a
further strict subsequence produces `mStar`.  Semantic convergence and every
stopping-law convergence survive that refinement.  Equivalently, one may use
compactness of `quittingTerminalSemanticLawCarrier`, identify the first
coordinate by uniqueness of limits, and retain the already selected weak-law
limits through the further subsequence.

This ordering matters.  An arbitrary law lift from
`exists_terminalSemanticLawCarrier_lift` need not be co-realized with the
selected stopping-law limit, so it cannot be substituted into the bubble
argument.  The corrected adapter uses one literal profile sequence throughout.

The actual limiting profile is
`quittingCompactStoppingLawProfile reward selected.laws`.  Exact
reconstruction of prescribed payoffs and unrestricted caps for every source
profile is checked by

- `quittingTerminalPayoff_eq_compactStoppingLawsOfProfile`;
- `quittingContinuationBestResponseValue_eq_compactStoppingLawsOfProfile`;
  and
- `quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile`.

Thus no strategy class or source semantics is lost when passing from each
source profile to its compact stopping laws.

## 2. Escaped coalition masses

Fix a nonempty coalition `S` and a finite horizon `T`.  The probability that
`S` is the first terminal coalition at some date at most `T` is a finite sum
of products of:

- stopping-law masses at the isolated finite dates `0,...,T`; and
- finite tail probabilities of the form `Pr(T_i>t)`.

All these quantities converge under weak convergence on the one-point
compactification.  Hence

\[
 \Pr_{\bar\sigma}(S\text{ occurs by }T)
 =\lim_n\Pr_{\sigma_n}(S\text{ occurs by }T).
\]

The finite-horizon event is contained in the complete `S`-outcome event, so
outcome-law convergence gives

\[
 \Pr_{\bar\sigma}(S\text{ occurs by }T)\le m^*(S).
\]

Letting `T` increase and using monotone convergence gives

\[
 m(S)\le m^*(S).
\]

Therefore `e(S)>=0`.  This argument does not select a large date atom and
does not assert that escaped mass is present at any fixed time.  It is a
coordinatewise defect of complete terminal laws.

Because both complete laws have total mass one,

\[
 \sum_{S\ne\varnothing}e(S)=m(\mathrm{Never})-m^*(\mathrm{Never}).
\]

Thus the finite-outcome defect is exactly balanced by extra Never mass in the
reconstructed limiting profile.

The same proof can be phrased with Portmanteau: for fixed `S`, the event that
the product stopping-time tuple eventually terminates in `S` is open.  The
finite-horizon polynomial proof is the safer Lean handoff because it uses
only finite point-mass convergence and existing live-path formulas.

## 3. Prescribed-payoff jump

Never pays zero and there are finitely many terminal coalitions.  Hence

\[
 U_i(\bar\sigma)=\sum_Sm(S)r_i(S),
 \qquad
 u_i=\sum_Sm^*(S)r_i(S).
\]

The first equality is
`quittingTerminalRewardMoment_outcomeMass`; the second follows by passing the
same finite reward moment through the jointly convergent source subsequence,
or from `terminalSemanticLawCarrier_rewardMoment` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`.
Subtracting proves the escaped reward-moment identity coordinatewise.

## 4. Unrestricted-cap lower semicontinuity

Fix player `i`.  Pure-time extremality is exact for the full behavioral
deviation class:

\[
 B_i(\sigma)=\sup_{t\in\mathbb N\cup\{\infty\}}
   V_i(t;\sigma_{-i}).
\]

This is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

For every fixed finite `t`,
`quittingTerminalPayoff_update_compactStoppingLawProfile_finiteTime_tendsto`
gives

\[
 V_i(t;\sigma_{n,-i})\longrightarrow
 V_i(t;\bar\sigma_{-i}).
\]

Since `V_i(t;sigma_n)<=B_i^n` and `B_i^n->b_i`, every finite limiting value is
at most `b_i`.

It remains to compare Never with finite dates.  For arbitrary limiting
opponent laws—not only in the all-nonproper case—bounded event decomposition
gives

\[
 \lim_{t\to\infty}V_i(t;\bar\sigma_{-i})
 =V_i(\infty;\bar\sigma_{-i})
   +q_i r_i(\{i\}), \tag{D}
\]

where `q_i` is the probability that every opponent Never stops.  The only
events on which late finite Quit differs persistently from Never are the
all-opponents-Never event; exact ties at date `t` have probability tending to
zero.  If one opponent law is proper then `q_i=0`; if all opponents are
nonproper the checked specialized form is
`quittingTerminalPayoff_update_finiteTime_tendsto_never_add_singleton`.

Under `r_i({i})>=0`, equation (D) shows that Never is weakly approximated from
above by sufficiently late finite Quit times.  Thus

\[
 B_i(\bar\sigma)
 =\sup_{t\in\mathbb N}V_i(t;\bar\sigma_{-i})
 \le b_i.
\]

This is the correct direction.  It is lower semicontinuity in the convention
`B(limit)<=liminf B_n`: the semantic approximants may retain a premium at a
moving response date that disappears from the actual limiting cap.

The all-behavior claim therefore rests on exact pure-time extremality, not on
a restriction of the deviation class.  Never and arbitrarily late stopping
are included explicitly.

## 5. Debt identity and attainment

Define `Delta_i=b_i-B_i(barSigma)`.  Cap lower semicontinuity gives
`Delta_i>=0`.  Direct subtraction gives

\[
\begin{aligned}
D(\bar\sigma)-D(z)
 &=\sum_i\bigl(B_i(\bar\sigma)-U_i(\bar\sigma)-b_i+u_i\bigr)\\
 &=\sum_Se(S)R(S)-\sum_i\Delta_i.
\end{aligned}
\]

The semantic pair of `barSigma` is an actual carrier point.  If `z` is a
global minimizer, the left side is nonnegative, proving (B).  If no actual
profile has debt equal to `D(z)`, it is strictly positive.

Under (C), the escaped reward term is nonpositive because each `e(S)>=0`, and
the cap-drop term is also nonpositive.  Hence (A) makes the left side at most
zero.  Global minimality gives the reverse inequality, so equality holds and
`barSigma` attains the minimum debt value.

This proof does not use `D(z)>0`.  If the attained minimum value is zero, the
actual profile has zero coordinate debt and gives an exact terminal Nash
profile, hence a uniform-equilibrium payoff through the checked exact terminal
compiler.  If the minimum is positive, the theorem supplies an actual
positive-minimum profile but does not contradict the terminal gap.

## 6. Boundary tests

### Negative singleton reward

The falsifier's two-player example is exact.  Give player `i` payoff `-1` at
every nonempty terminal coalition, let `i` play Never, and let the opponent
quit at deterministic date `n`.  Every response by `i`, including Never, pays
`-1`, so `B_i(\sigma_n)=-1`.  The opponent clock converges weakly to Never;
against the limiting all-Never opponent, player `i` obtains zero by Never, so

\[
 B_i(\bar\sigma)=0>-1=\liminf_nB_i(\sigma_n).
\]

Thus the singleton sign is essential for the cap inequality.

### Lack of global minimum provenance

The note's two-player example with

\[
 r_c\equiv0,\quad
 r_a(\{c\})=-1,\quad r_a(\{a\})=0,\quad
 r_a(\{c,a\})=1
\]

is correct.  With `c` uniform on dates `0,...,n` and `a` Never, the semantic
pairs converge to a nonattained debt-one point while both clocks converge to
Never.  All-Never has debt zero.  This proves that nonnegative own singleton
rewards and positive debt do not suffice; the selected point must be globally
minimal.

### Aggregate reward sign

The condition `R(S)<=0` is sufficient, not necessary.  Positive aggregate
reward at one coalition does not force nonattainment.  What is necessary for
genuine nonattainment under nonnegative singleton rewards is the strict
sequence-specific inequality

\[
 \sum_Se(S)R(S)>\sum_i\Delta_i\ge0.
\]

The export must not state an equivalence.

## 7. Freshness and overlap

The closest checked package is
`formalized/OPPONENT_TIGHT_TERMINAL_SEMANTIC_REALIZATION.md`.  Its checked
theorems prove:

- full semantic realization under opponent tightness;
- realization when two limiting clocks are proper;
- a negative-singleton Never jump when exactly one clock is proper at a
  nonattained minimum; and
- under nonnegative own singleton rewards, reduction of nonattainment to a
  selected law limit in which every clock is nonproper.

It does **not** prove coordinatewise positivity of the escaped finite-outcome
defect, cap lower semicontinuity in the non-tight arm, identity (A), or the
aggregate-sign attainment theorem.  The new result begins exactly where that
packet stops.

`formalized/POSITIVE_DEBT_TERMINAL_SEMANTIC_NONATTAINMENT.md` proves that a
positive-debt carrier point need not be attained, but its checked example has
a negative own singleton reward and global minimum zero.  The current note's
example has both own singleton rewards zero and is a sharper boundary test.

The checked `TerminalSemanticMinimumAggregateSurplus.lean` and
`TerminalSemanticMinimumAggregateSurplusConsumer.lean` establish static
reward-moment surplus certificates at a positive minimum.  They do not compare
one source subsequential outcome law with the actual law of its weak stopping-
law limit, and contain neither the escaped-mass sign nor the cap-jump account.

Narrow searches in `UniformEquilibrium/`, `Research/`, `formalized/`,
`exports/`, and `revisit/` found no theorem with conclusions (A)--(C).

## 8. Adapter and consumers

The actual-data adapter is complete:

1. choose a carrier minimizer using
   `exists_minimum_quittingTerminalSemanticDebtSum`;
2. choose one source-attached stopping-law limit using
   `nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier`;
3. refine that same sequence to a convergent outcome law; and
4. reconstruct the actual limiting product profile.

Under (C), this produces an actual profile on the exact minimum-debt fibre.
There are two downstream uses.

- At minimum value zero, the actual profile is an exact terminal Nash profile
  and feeds the checked terminal-to-uniform compiler.
- In the positive-minimum/no-uniform-payoff branch, obtain a terminal gap and
  use
  `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` followed by
  `QuittingActualProfileTerminalGapPaidCapPort.inertStall_of_minimumFiber` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`.
  Equivalently, use the exact-fibre contraction in
  `PaidCapMinimumFiberContraction.lean`.  This moves the nonattained escape arm
  into the existing literal actual-profile inert-stall arm; it does not prove
  a uniform payoff.

Without condition (C), the strict positive-social-surplus packet has no
current consumer.  This nonclaim is essential.

## 9. Lean handoff

Suggested new file:

```text
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeAccount.lean
```

Minimal conceptual imports:

- `UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization`;
- `UniformEquilibrium.Quitting.Root.TerminalSemanticMoment`;
- `UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn`;
- `UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum`.

The paid-cap file should be imported only by a separate conjecture-facing
adapter, not by the core compactness/accounting theorem.

Recommended declaration order:

1. `exists_terminalOutcomeMass_tendsto_refinement`

   Given a `QuittingTerminalSemanticSelectedLawLimit`, choose a further strict
   subsequence and a mass in the standard terminal-outcome simplex such that
   the literal source outcome laws converge to it.  Retain semantic and
   stopping-law convergence through composition.

2. `quittingAbsorbedMassLimit_compactLawLimit_le_outcomeLimit`

   For one nonempty terminal coalition, prove
   `outcomeMass limitProfile (some terminal) <= limitMass (some terminal)`
   from finite-horizon absorption convergence and monotonicity.

3. `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_singleton_general`

   Prove equation (D) for arbitrary opponent compact laws.  The existing
   theorem of the same stem with the `opponents not proper` hypothesis is a
   specialization.  When the opponent-Never product is zero, the added term
   vanishes.

4. `quittingContinuationBestResponseValue_lawLimit_le_of_singleton_nonneg`

   From the selected source's semantic convergence, fixed-finite response
   convergence, generalized late-finite/Never comparison, and pure-time
   extremality, prove the reconstructed profile's cap coordinate is at most
   the selected target cap.

5. `terminalSemanticSelectedLawLimit_escapeAccount`

   Return the outcome-law refinement, actual limit profile, nonnegative
   escaped masses, prescribed reward moments, cap drops, and identity (A) as
   theorem conclusions.  Do not make those desired properties assumptions of
   a new structure.

6. `exists_actualProfile_debt_eq_globalMinimum_of_aggregateReward_nonpos`

   Given (C), a carrier point and its global-minimum proof, return an actual
   profile whose total debt equals that point's debt.

7. `exists_actualProfile_attains_minimumDebt_of_aggregateReward_nonpos`

   Compose declaration 6 with
   `exists_minimum_quittingTerminalSemanticDebtSum`; no positive-minimum
   hypothesis is needed.

8. A separate positive-minimum adapter may package the actual profile into
   `QuittingActualProfileTerminalGapPaidCapPort` and conclude its inert-stall
   arm.

The finite-horizon mass lemma is the only substantial new measure-transport
piece.  The remaining proof uses existing finite-dimensional compactness,
reward moments, pure-time extremality, and semantic convergence.

## Final export recommendation

Promote a final packet only after it incorporates the falsifier's eight listed
repairs: full carrier adapter, explicit escaped-mass proof, the stronger
zero-or-positive attainment theorem, both negative tests, named consumers,
and the Lean handoff above.  With those repairs the result meets the export
gate as a complete reduction of a checked nonattainment arm and a genuine
special-class attainment theorem.  It does not settle that sign chamber's
uniform-equilibrium question when the attained minimum remains positive.
