# Paid cap-port exact trichotomy and inert-stall boundary

Authors: external ChatGPT submission supplied by the user; conference packet
assembled by Codex

Independent mathematical and final whole-packet review:
[`CODEX_EULER`](../feedback/CHATGPT_EXTERNAL__PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL__BY_CODEX_EULER.md)

## Exact statement

Let `iota` be a nonempty finite player type and let `reward` be a bounded
finite quitting-game reward table.  Let

```lean
source : QuittingPaidCapLiftedSource reward
port   : source.SummablePort
```

be the checked literal paid cap lift.  At time `n`, write

\[
x_n=\texttt{quittingCapLiftedPrefixProfile}(n),\qquad
q_n=\texttt{quittingCapLiftedPrefixRoot}(x_n),
\]

\[
p_n=(u_n,b_n)=\operatorname{Sem}(x_n),\qquad
d_n=b_n-u_n,\qquad D_n=\sum_i d_{n,i},
\]

and

\[
a_n=\operatorname{Abs}(q_n),\qquad c_n=1-a_n,qquad
A=\sum_{n=0}^{\infty}a_n.
\]

Let `p_infinity` be `port.semanticPort.limit`; its envelope is the cap-port
limit.  Put

\[
\rho=\lVert p_\infty.2-p_0.2\rVert_\infty,qquad
D_*=D(\texttt{source.minimum})>0,
\]

and let `M = quittingRewardBound reward`.  Then exactly one of the following
three mutually exclusive cases holds.

1. **Charged cap return:** `0 < A` and `rho = 0`.  For every endpoint error
   `eta > 0`, some finite literal cap prefix starts at `b_0`, ends within
   `eta` of `b_0` coordinatewise, and has cumulative absorption at least
   `A / 2 > 0`.  These prefixes form a
   `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily reward`, hence
   the checked cumulative-charge consumer produces a uniform-equilibrium
   payoff.

2. **Quantitative semantic-debt descent:** `0 < rho`.  The literal semantic
   limit satisfies

   \[
   D_0-D(p_\infty)\ge D_*A
   \ge D_*\frac{\rho}{2M}>0.
   \]

   Consequently, on every fixed slice `eta <= rho`, the decrease is at least

   \[
   D_*\frac{\eta}{2M}.
   \]

3. **Literal inert marked stall:** `A = 0`.  Every absorption charge is zero,
   every cap root is exactly all Continue, and for every `n`

   \[
   u_n=u_0,\qquad b_n=b_0,\qquad d_n=d_0,\qquad D_n=D_0.
   \]

   The checked shifted paid row at depth `n` has observer reach one and its
   two shifted pure-time deviation payoffs have exactly the original
   difference.  Hence the original paid gain, live mass, temporal
   orientation, and reached-gain identity persist without loss.

The three cases are exhaustive because `A >= 0`; if `A > 0`, either `rho = 0`
or `rho > 0`, and if `A = 0` the third case holds.

The theorem does **not** assert that the third case occurs for a complete
positive-minimum frontier or terminal exploitability witness.  It asserts
that the current paid cap-lift output has this exact residual unless further
ambient data excludes it.

## Conjecture-facing change

The live producer gap is the arrow

```text
paid first-disagreement row
  -> cumulative admissible payoff near-return or well-founded frontier drop.
```

The exact trichotomy closes two quantitative subcases and isolates the only
zero-charge residual.  It also prevents later work from counting a generic
cap port, a merely strict real-valued debt decrease, or a persistent paid row
as a completed discharge.  The remaining named obligation is:

> eliminate or give a recursively preserved natural-valued rank decrease for
> the literal inert paid-cap stall, using additional frontier or terminal-gap
> provenance.

This is a strict narrowing of the paid-port discharge problem, not a proof of
the conjecture and not a counterexample to any theorem whose hypotheses
include additional ambient data.

## Probability, information, and agency audit

Each `x_n` is the actual behavioral profile obtained by prefixing the exact
product cap-Nash root `q_n` to `x_{n-1}`.  No public selector, correlated
randomness, reconstructed semantic source, or bounded deviation class is
introduced.  The paid row continues to compare two literal pure stopping
times in the same actual profile; its underlying cap remains the unrestricted
behavioral best-response envelope.  The exact floor orbit is annotated by
`b_n`, not by `u_n`.  These two coordinates are never identified.

## Proof

### 1. Exact debt scaling

`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` gives,
coordinatewise,

\[
d_{n+1,i}=c_n d_{n,i}.
\]

The literal-profile specialization
`quittingCapLiftedPrefixProfile_debt_succ` gives the corresponding identity
for the total debt sum.

Induction and `quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul` give

\[
d_{N,i}=P_Nd_{0,i},\qquad D_N=P_ND_0,qquad
P_N=\prod_{n<N}c_n.
\]

Every semantic pair belongs to the carrier, so global minimality gives
`D_* <= D_N`.  The finite products decrease to a limit `P` and

\[
P\ge D_*/D_0>0,\qquad D(p_\infty)=PD_0.
\]

The last equality follows by the checked semantic convergence of
`SummableSemanticPort` and continuity of the finite debt sum.

### 2. Charge controls debt decrease

For every finite `N`, the survival inequality gives

\[
P_N\left(1+\sum_{n<N}a_n\right)\le1.
\]

Passing to the limit yields `P(1 + A) <= 1`, hence the valid auxiliary bound

\[
D_0-D(p_\infty)=D_0(1-P)
\ge D_*\frac{A}{1+A}.
\]

The already checked finite debt budget is stronger:

\[
D_*\sum_{n<N}a_n\le D_0-D_N.
\]

Passing to the limit gives

\[
\boxed{D_*A\le D_0-D(p_\infty).}
\]

Every exact Bellman cap edge has coordinate increment bounded by
`2 M a_n`.  Summing the absolutely convergent series gives

\[
\rho\le2MA.
\]

When `rho > 0`, necessarily `M > 0`, so

\[
D_0-D(p_\infty)
\ge D_*A
\ge D_*\frac{\rho}{2M}.
\]

This proves branch 2, including the uniform bound on a slice `eta <= rho`.
It does not make repeated decreases well-founded when `rho` may tend to zero.

### 3. Positive charge with zero cap displacement

Assume `A > 0` and `rho = 0`.  Since the nonnegative partial sums converge
to `A`, eventually they are at least `A/2`.  Since `b_N` converges to
`b_infinity=b_0`, for every positive endpoint error a sufficiently large
prefix has the requested seam and charge.  The checked cap orbit supplies
the exact punishment-floor path as follows.  Let `orbit` be
`quittingCapLiftedPunishmentFloorOrbit reward source.profile` and set
`cert := orbit.toFinitePrefix N`.  Then
`quittingFinitePrefixAdmissiblePath cert cert.horizon (by omega)` is the
required tail-to-current path, and
`chargeSum_quittingFinitePrefixAdmissiblePath_horizon` identifies its charge
with the selected prefix sum.  These literal prefixes instantiate
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` with the correct
relation orientation; apply
`quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`.

### 4. Zero charge is literal inertness

Assume `A=0`.  Every `a_n` is nonnegative and the series is summable, so each
`a_n=0`.  A product root has zero absorption iff every player Continues with
probability one; thus every `q_n` is `quittingAllContinueRoot`.

Root-then-continuation prefixing by all Continue merely shifts every stopping
time one date.  Time-homogeneous quitting rewards imply

\[
U(x_{n+1})=U(x_n),\qquad B(x_{n+1})=B(x_n).
\]

The semantic-prefix identity gives the same conclusion directly, and hence
the debt coordinates and their sum remain fixed.

For the paid observer, `source.pureTimePayoff_sub_shift` multiplies the
original pure-time payoff difference by `source.observerReach n`.  With every
outer root all Continue, this reach is one.  Therefore

\[
P_o^{x_n}(\operatorname{shift}_n\tau_r)
-P_o^{x_n}(\operatorname{shift}_n\tau_s)
=P_o^{x_0}(\tau_r)-P_o^{x_0}(\tau_s)\ge g.
\]

The row decoder's chronology is shifted but otherwise unchanged, which proves
the marked inert-stall branch.

## Exact cap-to-prescribed boundary

The checked identity

```lean
capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt
```

shows why branch 3 is not already a prescribed-payoff edge.  For an exact
cap-Nash root `q`, exact Nash at the prescribed payoff holds iff, in every
coordinate, the continuation-option surcharge equals joint survival times
the terminal debt.  At all Continue the survival factor is one.  Cap Nash
supplies only the cap inequality; the `QuittingPaidCapLiftedSource` fields do
not supply this coordinatewise equality.

This is a source audit and a nonclaim, not a formal countermodel proving that
no stronger theorem can use additional frontier data.

## Boundary tests

1. If one prefix root has positive absorption and the cap limit returns to
   `b_0`, branch 1 applies even if every individual charge is arbitrarily
   small; cumulative rather than pointwise charge is essential.
2. If `rho >= eta > 0`, branch 2 gives the fixed positive decrement
   `D_* eta/(2M)`.  Analytically, `rho_k=2^(-k)` and
   `a_k=rho_k/(2M)` demonstrate why individually positive certified
   decrements can still be summable.  This is a scale test, not a claimed
   sequence of actual restart sources.
3. The checked regression
   `source_positiveTotalOpponentIncidence_but_onlyAllContinue_capNash` has
   positive terminal incidence and positive total debt while every exact
   cap-Nash root is all Continue.  It tests the local cap-selection
   obstruction but is not a full paid positive-minimum counterexample.
   Independently, if every cap-lift root is all Continue, then `A=0` and all
   literal invariants in branch 3 hold; shifting both paid witnesses preserves
   their payoff difference.
4. Positive signed outer absorption cannot be multiplied by the paid suffix
   gain: the former occurs on absorption and the latter only on survival of
   all outer roots.  A theorem spending both needs a new product-realizable
   rerouting construction.

## Source correspondence

The narrow checked dependency set is:

- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `QuittingPaidCapLiftedSource`,
  `quittingCapLiftedPrefixProfile_debt_succ`,
  `quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul`,
  `QuittingPaidCapLiftedSource.minimum_mul_partialAbsorption_le_debtDrop`,
  `QuittingPaidCapLiftedSource.absorption_summable`,
  `QuittingPaidCapLiftedSource.pureTimePayoff_sub_shift`,
  `QuittingPaidCapLiftedSource.nonempty_shiftedPaidRow`, and
  `QuittingPaidCapLiftedSource.nonempty_summablePort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
- `SummableChargeAllContinuePort` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbitChargeDichotomy.lean`;
- `quittingFinitePrefixAdmissiblePath` and
  `chargeSum_quittingFinitePrefixAdmissiblePath_horizon` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorFinitePrefixAdmissiblePath.lean`;
- `abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass` in
  `UniformEquilibrium/Quitting/Debt/Marked/TimeAdvance.lean`;
- `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`
  in `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`;
- `capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointSeam.lean`;
- the survival estimates in `MathUE/SummableChargeSurvival.lean`; and
- `source_positiveTotalOpponentIncidence_but_onlyAllContinue_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticIncidenceDebtRatioRegression.lean`.

The maintained checked account
`formalized/PAID_CAP_LIFTED_SUMMABLE_PORT.md` already records the source,
literal cap chronology, finite debt budget, summability, semantic port, and
shifted rows.  The maintained checked account
`formalized/CUMULATIVE_CHARGE_NEAR_RETURN_AND_SUMMABLE_PORT.md` already records
the cumulative near-return consumer and general charge-or-stall theorem.
This packet does not duplicate those producers or consumers.  Its new content
is their exact composition into one exhaustive interface trichotomy, the
infinite-limit `rho`-to-debt-drop estimate, and the zero-charge
marked-inertness specialization.  No existing declaration found in the
narrow source audit exposes that boundary as one theorem.

No literature theorem is used.

## Checked Lean realization

The result is proved in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`.
The headline declaration `QuittingPaidCapLiftedSource.exactTrichotomy` returns
the exhaustive disjunction and all three pairwise exclusions.  The branch
structures are `ChargedNearReturn`, `QuantitativeDebtDescent`, and
`InertStall`.  The exact infinite budget and displacement estimates are
`minimum_mul_totalAbsorption_le_debtDrop` and
`capDisplacement_le_two_mul_totalAbsorption`; the charged-family constructor
is `nonempty_cumulativeNearReturnFamily_of_totalAbsorption_pos_of_capDisplacement_zero`.

The charged branch has `M`, `L`, `A`, and `C` through the checked unrestricted
behavioral uniform-payoff consumer.  The quantitative descent and inert
branches have `M`, `L`, and `A`, but no recursive or closing `C`.  Direct and
named builds, the Diagnostics umbrella build, axiom inspection, import-graph,
duplicate, telescope, line, lexical, and diff checks passed.  The only
transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Scope and nonclaims

- No full positive-minimum frontier is shown to realize the inert branch.
- No terminal exploitability witness is contradicted.
- Branch 2 is not a natural-valued or otherwise well-founded recursive rank.
- The cap annotations `b_n` are not prescribed payoffs `u_n`.
- A persistent paid row is not an exact prescribed-payoff Nash--Bellman edge.
- Signed outer absorption and paid-suffix reach are not co-realized events.
- The result neither proves nor refutes the quitting-game uniform-equilibrium
  conjecture.
