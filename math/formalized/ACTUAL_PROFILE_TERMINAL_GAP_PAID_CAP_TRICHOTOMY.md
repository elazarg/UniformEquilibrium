# Actual-profile terminal-gap paid-cap trichotomy

Author: CODEX_EULER

Independent mathematical review:
[`CODEX_MINER`](../feedback/CODEX_EULER__FIN5_LITERAL_NEVER_SPARE_PRODUCER_AUDIT__BY_CODEX_MINER.md),
[`CODEX_RAMSEY`](../feedback/ACTUAL_PROFILE_TERMINAL_GAP_PAID_CAP_TRICHOTOMY__BY_CODEX_RAMSEY.md)

## Exact statement

Let `I` be a finite player type, let `reward` be a finite quitting-game reward
table, and let `gamma>0`.  Assume

```lean
gap : HasTerminalExploitabilityGap reward gamma
minimum : QuittingTerminalSemanticPair I
minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
minimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
  quittingTerminalSemanticDebtSum minimum ≤
    quittingTerminalSemanticDebtSum candidate
minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum
```

Then for every literal behavioral profile `sigma` there exist a player `j`
and two pure stopping times `s,t : Option Nat` such that

\[
 U_j(\sigma[j\leftarrow t])-U_j(\sigma[j\leftarrow s])\geq\gamma. \tag{1}
\]

Consequently there exist, on the same literal profile `sigma`,

```lean
row    : QuittingPaidFirstDisagreementRow reward sigma j gamma
source : QuittingPaidCapLiftedSource reward
port   : source.SummablePort
```

where `source.minimum=minimum`, `source.profile=sigma`,
`source.observer=j`, `source.gain=gamma`, and `source.row=row`.  The selected
port satisfies the checked exhaustive, pairwise-disjoint alternative

```lean
QuittingPaidCapLiftedSource.ChargedNearReturn source port
  ∨ QuittingPaidCapLiftedSource.QuantitativeDebtDescent source port
  ∨ QuittingPaidCapLiftedSource.InertStall source port.
```

Thus every actual behavioral profile in a positive-terminal-gap game with a
positive global semantic-debt minimum enters the already checked paid-cap
trichotomy with the full weak gap `gamma`.  No deletion condition, floor
condition, stationary restriction, finite-horizon approximation, or
preselected observer is required.

## Conjecture-facing change

The paid-cap trichotomy previously began from a supplied
`QuittingPaidCapLiftedSource`, whose paid-row field could be a provenance gap
at an actual profile selected by an upstream construction.  This theorem
removes that gap: the ambient terminal-exploitability witness produces the
required full-gap paid row at every literal behavioral profile.

In particular, any Fin5 literal-Never deletion endpoint and any other actual
same-table endpoint can be sent unconditionally to the paid-cap trichotomy.
This eliminates separate paid-row producer obligations for conservative
deletion-test failures.  It does not eliminate the checked `InertStall` arm,
make quantitative real-valued descent well founded, or align the selected
observer with an omitted/reset/collision label.

## Probability, information, and agency

Strategies are unrestricted behavioral quitting strategies.  Against fixed
opponents, each strategy induces its complete stopping law, a probability
mass function on `Option Nat`; `none` is literal Never.  The proof compares
the stopping law of the profitable behavioral deviation with the stopping
law of the prescribed behavioral strategy.  It does not replace either law
by a finite cutoff or assume attainment of a behavioral best-response cap.

The two pure times extracted below may independently be finite or Never.
They are atoms used by the paid-row decoder.  The theorem does not assert that
the prescribed strategy itself is one of those pure atoms.

## Proof

Fix `sigma`.  By `gap sigma`, choose `j` and an unrestricted behavioral
replacement `tau` such that

\[
 U_j(\sigma[j\leftarrow\tau])-U_j(\sigma)\geq\gamma. \tag{2}
\]

For `q : Option Nat`, put

\[
 V(q)=U_j(\sigma[j\leftarrow q]),
\]

where the update uses the pure-time behavioral strategy associated with
`q`.  Let `mu_tau` be the complete stopping law of `tau`, and let `mu_sigma`
be the complete stopping law of the prescribed strategy `sigma(j)`.  The
checked stopping-law disintegration gives

\[
 U_j(\sigma[j\leftarrow\tau])=\mathbb E_{\mu_\tau}V,
 \qquad
 U_j(\sigma)=\mathbb E_{\mu_\sigma}V.                \tag{3}
\]

Both laws are countable probability mass functions and `V` is bounded by the
finite reward bound.  On their product law,

\[
 \mathbb E[V(q)-V(s)]
 =\mathbb E_{\mu_\tau}V-\mathbb E_{\mu_\sigma}V
 \geq\gamma.                                        \tag{4}
\]

Suppose every positive-mass product atom satisfied
`V(q)-V(s)<gamma`.  The deficit
`gamma-(V(q)-V(s))` would then be nonnegative almost surely and strictly
positive at every support atom.  The two probability laws each have nonempty
support, so their product has a positive-mass atom.  A nonnegative bounded
function which is positive at a positive-mass atom has strictly positive
expectation.  This would make the left side of (4) strictly less than
`gamma`, a contradiction.  Hence some support pair `(t,s)` satisfies (1).
Since `gamma>0`, the two pure times are distinct.

Apply
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` to (1).  It
returns a paid row on the literal receiving profile `sigma`, with observer
`j`, source witness `s`, receiving witness `t`, and gain `gamma`.  Combine
that row with the supplied `minimum`, `minimum_le`, and `minimum_pos` to form
`QuittingPaidCapLiftedSource reward`.  Apply
`QuittingPaidCapLiftedSource.nonempty_summablePort`, then apply
`QuittingPaidCapLiftedSource.exactTrichotomy` to the selected port.  This
proves the statement.

## Quantitative minimum-fiber consequence

Write `D_*` for the debt of `minimum`, `D_sigma` for the debt of
`Sem(sigma)`, `R=quittingRewardBound reward`, and `D_infinity` for the selected
port limit debt.  In the quantitative branch, with cap displacement `rho>0`,

\[
 D_\sigma-D_\infty\geq D_*\frac{\rho}{2R}.           \tag{5}
\]

The source debt is `D_sigma`; it must not be replaced by `D_*` off the
minimum fiber.  If `D_sigma=D_*` and the terminal-gap witness is retained,
the charged arm is impossible because it produces a uniform-equilibrium
payoff, and the quantitative arm is impossible because (5) contradicts
global minimality of `minimum`.  Therefore a minimum-fiber actual source can
only enter the inert arm.

## Boundary tests

1. The strict-average step retains the full weak gap.  For two point masses it
   reduces to the literal inequality between their two pure-time values.  For
   diffuse countable laws, replacing the profitable law by a near-maximizing
   atom alone would generally lose an arbitrary error; the product-law
   argument does not.
2. Either extracted time may be `none`.  The disintegration and paid-row
   decoder both use `Option Nat`, so date zero, later finite dates, and Never
   are included without endpoint conventions being changed.
3. The assumption `gamma>0` is essential for a paid row: at `gamma=0` the
   two selected atoms need not differ and the decoder's positive-gain field
   cannot be filled.
4. A positive global minimum is not used to extract the paid row.  It is
   needed only to build the cap-lifted source and obtain summability and the
   exact trichotomy.
5. In the inert branch every selected cap root is all Continue while the paid
   row persists under literal time shifts.  This is consistent because the
   roots are Nash against the cap annotation, whereas the paid row compares
   deviations from the prescribed literal profile.

## Source correspondence and novelty audit

The checked ingredients are:

- `HasTerminalExploitabilityGap` and
  `quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `QuittingPaidCapLiftedSource` and
  `QuittingPaidCapLiftedSource.nonempty_summablePort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
  and
- `QuittingPaidCapLiftedSource.exactTrichotomy` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`.

The maintained checked packet
[`PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL`](../formalized/PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md)
starts from a supplied paid cap-lifted source.  Specialized pair-base,
singleton-base, and stationary handoffs also manufacture paid rows under
their own incidence hypotheses.  The narrow search found no checked theorem
which derives a full-gap paid first-disagreement row at an arbitrary literal
profile directly from `HasTerminalExploitabilityGap`.  The new content is
exactly that product-stopping-law extraction and its composition with the
checked source and trichotomy.  No external paper is used.

## Actual-data adapter and consumer

The actual-data adapter is direct: input the behavioral profile produced by
any upstream same-table construction as `sigma`.  No semantic-pair
re-realization or profile reselection is performed.  The consumer is the
checked exact trichotomy.  Its charged arm reaches the checked cumulative
near-return uniform-payoff compiler; its quantitative arm gives (5); its
inert arm is the precise surviving obstruction.

For the Fin5 literal-Never application, set
`sigma=x_2[w<-quittingNeverBehaviorStrategy]`.  The deletion endpoint
alternative and this paid-port trichotomy are parallel facts, not a combined
four-way partition.

## Lean handoff

The narrow new declaration should first package the extraction:

```lean
theorem HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at
    (hgamma : 0 < gamma)
    (gap : HasTerminalExploitabilityGap reward gamma)
    (sigma : (quittingGame reward).BehaviorProfile) :
    ∃ j, Nonempty
      (QuittingPaidFirstDisagreementRow reward sigma j gamma)
```

Its proof should use the two exact expectation identities and a product-PMF
strict-average lemma for bounded functions.  A second theorem can take the
minimum fields, construct `QuittingPaidCapLiftedSource`, choose
`nonempty_summablePort`, and return `exactTrichotomy`.  The latter should not
reprove any cap-port estimates.

Useful tests are a finite two-atom PMF, one finite/one Never witness, equality
in (2), and an off-minimum source verifying that the left side of (5) is
`D_sigma-D_infinity`.

## Scope and nonclaims

- The selected observer is arbitrary and need not match any upstream role.
- The pure source witness is an atom of the prescribed stopping law, not the
  whole prescribed behavioral strategy.
- No floor-admissible prescribed-payoff Bellman edge is produced.
- No accumulated exact return or restart at the abstract port limit is
  produced.
- Quantitative displacement descent is not made well founded.
- The inert all-Continue stall is not excluded.
- The theorem does not prove the finite-quitting uniform-equilibrium
  conjecture.

## Checked Lean realization

The formalization is split into four narrow modules.

- `exists_support_pair_expect_sub_le_sub`
  (`MathUE/ProbabilityMassFunction/BoundedSupportAverage.lean`) selects one
  support atom above a bounded PMF average and one below another average.
- `HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` and
  `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`)
  retain the full weak gap at every literal behavioral profile.  The two
  stopping times are support atoms of the profitable and prescribed stopping
  laws, respectively.
- `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` and
  `QuittingActualProfileTerminalGapPaidCapPort.exactTrichotomy` (same file)
  construct the actual source and its summable port and expose the checked
  exhaustive, pairwise-disjoint trichotomy.  Under the terminal gap,
  `quantitativeDebtDescent_or_inertStall` excludes the charged-return arm.
- `QuittingPaidCapLiftedSource.minimum_mul_totalAbsorption_le_excess` and
  `minimum_mul_capDisplacement_le_twoRewardBound_mul_excess`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapMinimumFiberContraction.lean`)
  prove, with `D_source = source.initialDebt`,

  \[
  D_* A\le D_{\mathrm{source}}-D_*,\qquad
  D_*\rho\le 2R(D_{\mathrm{source}}-D_*).
  \]

  Consequently `inertStall_of_initialDebt_eq_minimum` makes every exact-fiber
  paid cap port literally inert without a terminal-gap hypothesis.
- `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapMinimumApproximation`
  (`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfilePaidCapMinimumApproximation.lean`)
  uses carrier density to produce actual full-gap paid ports with source debt
  tending to `D_*`, total absorption tending to zero, and cap displacement
  tending to zero.  It does not assert that the carrier minimum is realized
  by a behavioral profile.

Evidence seals: the bounded-average mathematics has `M` and `L`; the
actual-profile extraction, source construction, minimum-fiber wrapper, and
carrier-density approximation have `M`, `L`, and `A`.  The charged-return arm
has the previously checked `C` into unrestricted-behavior uniform-payoff
existence.  Quantitative descent and literal inertness have no regenerated
source or closing `C`.

Direct and named Lean builds, the production umbrellas, the exhaustive axiom
audit, trust scan, import graph, duplicate check, telescope check, line-length
check, and documentation checks passed.  The only transitive axioms are
`propext`, `Quot.sound`, and `Classical.choice`.

## Formalized nonclaims

- The selected observer need not agree with an upstream reset, deletion, or
  collision label.
- Either pure stopping time may be `Never`; neither is asserted to equal the
  prescribed behavioral strategy.
- The cap-port limit is a carrier point, not an attained behavioral profile
  or a regenerated paid source.
- Convergence of actual ports toward the minimum fiber gives
  `A_n -> 0` and `rho_n -> 0`; it does not produce an attained inert source.
- The real-valued quantitative descent is not well founded, and the literal
  inert stall has no positive outer absorption event.
- The remaining conjecture-facing task is to consume or regenerate the
  quantitative descent, or to consume the literal inert stall.  No result in
  this wave proves the finite-quitting uniform-equilibrium conjecture.
