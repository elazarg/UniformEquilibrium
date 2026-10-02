# Paid cap-lifted summable port

Authors: external `ChatGPT` contribution supplied by the user; export
assembly and source audit by `CODEX_ROOT`

Independent review:
[`CODEX_ROOT`](../feedback/CHATGPT_EXTERNAL__PAID_CAP_LIFTED_SUMMABLE_PORT__BY_CODEX_ROOT.md)

## Exact statement

Let `I` be a nonempty finite player set, let `r` be a finite quitting-game
reward table, and let `z*` be a global minimizer of total terminal semantic
debt.  Assume

```text
D* := DebtSum(z*) > 0.                                      (1)
```

Let `x0` be an attained behavioral profile carrying a
`QuittingPaidFirstDisagreementRow r x0 observer gain` with `gain>0`.  In the
intended source adapter, `x0` is the actual full-replacement receiving profile
stored by a `QuittingStoppingLawCurvaturePaidWitness`.

There exist literal behavioral profiles `x_n`, product roots `q_n`, and
semantic pairs

```text
(u_n,b_n) = Sem(x_n) = (U(x_n),B(x_n))
```

such that

```text
x_0 = x0,
x_(n+1) = rootThenContinuation(q_n,x_n),
q_n is exact Nash against b_n,
u_(n+1) = rootSuccessorPayoff(r,u_n,q_n),
b_(n+1) = rootSuccessorPayoff(r,b_n,q_n).             (2)
```

The cap-root sequence `((b_n,q_n))` is an exact punishment-floor infinite
Nash--Bellman orbit.  No hypothesis that `U(x0)` dominates the punishment
floor is required.

Writing

```text
a_n = rootAbsorptionMass(q_n),
c_n = 1-a_n,
D_n = DebtSum(Sem(x_n)),
S_n = product_(k<n)c_k,
sigma = D*/D_0,
```

one has

```text
D_(n+1)=c_nD_n,
D* sum_(n<N)a_n <= D_0-D_N <= D_0-D*,                 (3)
sum_n a_n <= (D_0-D*)/D* < infinity,                  (4)
D_n=S_nD_0,
S_n>=sigma>0                                          (5)
```

for every finite `N,n`.  Thus every finite profile `x_n` reaches the unchanged
paid receiving suffix `x0` with probability at least `sigma`.

For each `n`, shift each finite pure-time witness in the original row by `n`
dates and leave `Never` unchanged.  These shifted witnesses produce a
`QuittingPaidFirstDisagreementRow r x_n observer (sigma*gain)`.  Its observer,
orientation, and relative delay agree with the original row; its first
disagreement is shifted by `n`; and its live mass is the original live mass
multiplied by the opponents' Continue probability through the outer roots.

Finally the cap orbit has an exact floor-safe all-Continue limit port:

```text
q_n -> all-Continue,
b_n -> b_infinity,
punishmentValue(r,i) <= b_infinity(i),
r_i({i}) <= b_infinity(i),
rootSuccessorPayoff(r,b_infinity,all-Continue)=b_infinity.
```

The actual semantic pairs `Sem(x_n)` converge in the closed terminal semantic
carrier to an all-Continue fixed semantic port.  This is a carrier limit of
finite literal profiles; it is not asserted to be a behavioral profile which
runs `x0` after infinitely many prefix dates.

If the initial row comes from a
`QuittingStoppingLawCurvaturePaidWitness`, the original source and receiving
near-optimality inequalities remain stored as immutable provenance.  The
shifted rows are not asserted to retain those near-optimality inequalities at
the later profiles.

## Conjecture-facing change

The previously checked
`QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`
requires the paid profile's prescribed payoff `U(x0)` to dominate the
behavioral punishment floor.  That upstream floor adapter was explicitly
open.

The present theorem removes it.  The exact relation is lifted canonically to
the same actual profile's envelope `B(x_n)`, which always dominates the floor,
while the same roots simultaneously preserve the honest prescribed-payoff and
paid-row chronology.  Positive global minimum debt then forces the cap orbit
into the summable arm and supplies the quantitative reach floor `D*/D_0`.

The remaining paid-route obligation is now only downstream: consume or
restart the marked summable all-Continue port so that a fixed amount of its
paid or signed terminal budget is spent, or total semantic debt/support rank
strictly decreases.  This theorem does not perform that restart.

## Definitions, probability, information, and agency

Every `q_n` is a simultaneous product root.  The profile
`rootThenContinuation(q_n,x_n)` plays this root at a newly inserted first date
and, conditional on everyone Continuing, runs `x_n` literally.  The recursive
construction adds finite prefixes outward; it introduces no public
randomization or extra observations.

`B_i(x)` is the supremum over all behavioral strategies of player `i` against
the fixed opponents in `x`.  The behavioral punishment value is the infimum,
over opponent profiles, of this same best-response value.  Therefore

```text
punishmentValue(r,i) <= B_i(x)                         (6)
```

for every actual profile `x`.

The paid row concerns two deterministic quit times, including `Never`, but it
is valid against the project's unrestricted behavioral-deviation semantics.
Its live mass is opponents' survival to the first disagreement.  The root
charge `a_n` is joint absorption at a newly prefixed exact root.  These are not
identified.

## Source correspondence

The following existing declarations supply the cap chronology and its debt
budget.

- `quittingMaximalCapPrefixRoot`,
  `quittingMaximalCapPrefixRoot_exactNash`,
  `quittingMaximalCapPrefixProfile`,
  `quittingMaximalCapPrefixProfile_debt_succ`,
  `minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop`,
  `summable_maximalCapPrefix_absorption`,
  `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`,
  and `quittingMaximalCapPrefixPunishmentFloorPrefix` in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionDispatch.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `quittingTerminalSemanticPair_rootThenContinuation` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort` and
  `nonempty_summableChargeAllContinuePort_of_summable_absorption` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbitChargeDichotomy.lean`.

The actual paid source is already packaged by
`QuittingStoppingLawCurvaturePaidWitness` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvatureStrategicDispatch.lean`.
The exact decoder
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`
repackages any positive shifted pure-time payoff edge as a paid row.

The integrated
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidRowExactPortAlternative.lean`
constructs a marked exact orbit from `U(x0)` only after assuming its floor
inequality.  It does not contain the cap lift or the shifted paid-row transport.

The new mathematical content is:

1. the source-facing observation that the maximal-cap prefix sequence removes
   the explicit prescribed-payoff floor obstruction while staying on the same
   literal profiles;
2. the infinite cap-orbit wrapper and simultaneous honest semantic chronology;
3. the exact finite shift identity transporting a paid row through the outer
   roots with the uniform debt-ratio gain floor.

No external-paper claim is used.

## Proof

### 1. Exact cap lift

Set `x_0=x0`.  Given `x_n`, choose the canonical maximal-absorption exact root
`q_n` against `b_n=B(x_n)` and set `x_(n+1)=q_n ▷ x_n`.

Literal semantic prefixing gives the prescribed identity in (2).  For the cap
coordinate, the Quit endpoint is invariant under changing the continuation
annotation from `u_n` to `b_n`, while the Continue endpoint uses the deviating
player's cap coordinate on joint Continue.  Exact Nash against `b_n` identifies
the mixed root payoff with the maximum of the two pure endpoints.  Hence the
envelope identity in (2) is exact.

Equation (6) makes every `b_n` floor-safe.  Best-response values obey the
canonical reward bound.  Thus the roots and caps form an exact
punishment-floor infinite orbit.  The same roots generate the actual profiles
and their prescribed coordinates in parallel.

### 2. Debt budget

Let `d_n(i)=b_n(i)-u_n(i)`.  Exact cap-Nash semantic prefixing gives

```text
d_(n+1)(i)=c_n d_n(i).
```

Summing over the finite player set yields the first identity in (3).  Each
`Sem(x_n)` is an actual terminal semantic carrier point, so global minimality
gives `D_n>=D*`.  Therefore

```text
D_n-D_(n+1)=a_nD_n>=a_nD*.
```

Summing this finite identity proves (3), and the uniform bound on partial sums
proves (4).  Iterating the exact multiplicative recursion proves
`D_n=S_nD_0`.  Since `D_n>=D*>0`, division by `D_0` proves (5).

### 3. Paid-row transport

Define `shift_n(none)=none` and
`shift_n(some t)=some(n+t)`.  At one outer root, both shifted deviations make
the observer Continue.  The two payoffs therefore have the form

```text
fixed outer opponent-absorption reward
  + OppCont(q,observer) * continuation payoff.
```

Subtracting cancels the common term.  Induction over the `n` roots gives

```text
Payoff(x_n,shift_n(t_recv))-Payoff(x_n,shift_n(t_src))
 = Lambda_(n,observer)
     [Payoff(x0,t_recv)-Payoff(x0,t_src)],             (7)
```

where `Lambda` is the product of opponent Continue masses through the outer
word.  At every root, deleting the observer's Continue factor can only
increase survival, so `Lambda_(n,observer)>=S_n>=sigma`.  The original paid
edge is at least `gain`; (7) is therefore at least `sigma*gain>0`.

The exact first-disagreement decoder applied to the two shifted times gives
the claimed row at `x_n`.  The same calculation of opponent survival shows
its live mass equals `Lambda` times the original live mass.  No comparison
between this live mass and any individual root charge is used.

### 4. All-Continue port

Summability gives `a_n->0`.  Each marginal Quit probability is at most `a_n`,
so `q_n->all-Continue`.  The standard exact-orbit estimate

```text
|b_(n+1)(i)-b_n(i)| <= 2M a_n
```

makes every cap coordinate Cauchy.  The punishment floor is closed.  Passing
to the limit in exact root Nash yields singleton domination, so all Continue
is exact Nash at `b_infinity`; its Bellman successor is `b_infinity`.

The prescribed coordinates converge either by the same Bellman increment
bound or from `u_n=b_n-d_n` and exact debt scaling.  The semantic pairs are
actual carrier points, so their limit remains in the closed carrier and is
fixed by all-Continue semantic prefixing.

## Boundary tests

- **Prescribed floor failure.**  `U_i(x0)` may lie below punishment.  The
  theorem never inserts `U(x0)` into the punishment-floor relation.
- **Cap/prescribed separation.**  The relation annotations are `B(x_n)`, while
  the paid rows live on the parallel literal profiles with payoffs `U(x_n)`.
  The theorem does not assert these coordinates coincide.
- **Zero minimum.**  If `D*=0`, debt scaling supplies neither a summability
  budget nor a positive reach ratio.  The positive minimum is essential.
- **No shifted optimality.**  A fixed positive shifted row does not show its
  two shifted witnesses are near-best responses at `x_n`.
- **No infinite literal suffix.**  `x0` is a literal suffix of every finite
  `x_n`.  The limit is a semantic/Bellman port, not a strategy that begins
  `x0` after infinitely many dates.
- **No charge/live-mass conflation.**  The only survival comparison is
  opponent outer survival `>=` joint outer survival.

## Adapter and consumer

Given a `QuittingStoppingLawCurvaturePaidWitness` with positive gain, take its
actual receiving profile and its `row`; no floor field is requested.  A
positive-minimum tangent family supplies `z*`, its global minimality, and
`D*>0`.  These are the actual-data inputs of the theorem.

The output is an exact punishment-floor summable all-Continue port with one
literal finite-depth profile sequence carrying a uniformly positive paid row.
It replaces the upstream floor-safe-source adapter of the former exact-port
alternative.

No checked consumer currently restarts this summable port or turns the
persistent paid row into divergent exact cumulative charge.  That is the
remaining paid-route producer.

## Checked Lean realization

The result is proved in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`.
The implementation proves a slightly stronger selection-independent form:
it recursively chooses an arbitrary exact Nash root against each current cap;
maximal absorption is not needed.

- `QuittingPaidCapLiftedSource.nonempty_summablePort` packages the exact cap
  orbit, finite debt budget, summable absorption, uniform suffix reach,
  shifted paid rows, and the cap and semantic all-Continue ports.
- `QuittingStoppingLawCurvaturePaidWitness.nonempty_capLiftedSummablePort`
  supplies the actual paid-profile adapter without a prescribed-payoff floor
  hypothesis.
- `QuittingStoppingLawCurvaturePaidWitness.nonempty_capLiftedSummablePort_of_tangentFamily`
  supplies the positive-minimum tangent-family adapter.
- `quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one` and
  `QuittingPaidCapLiftedSource.pureTimePayoff_sub_shift` prove the exact
  finite-time and `Never` transport identities.
- `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  is owned canonically by
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.

### Fin4 same-source paid/reset adapter

The checked production module
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourSameSourcePaidResetCapPort.lean`
now supplies the source composition directly from every
`QuittingTerminalExploitabilityWitness` on `Fin 4`.

For any prescribed reset owner and disjoint pairwise distinct sure-Quit base,
`QuittingTerminalExploitabilityWitness.nonempty_finFourSameSourcePaidResetCapPort`
packages:

- a positive global-minimum point of the closed terminal-semantic carrier;
- one actual pair-base stationary profile and complete terminal law;
- the full-gap paid row whose observer lies in the forced pair;
- the same profile/law as fixed-law reset target, with the separately returned
  reset pair and dispatch retained;
- the canonical `QuittingPaidCapLiftedSource` using that exact stationary
  profile as its unchanged suffix; and
- the full `QuittingPaidCapLiftedSource.SummablePort`.

The forwarding theorems `debt_succ`, `partialAbsorption_budget`,
`reachFloor_le_suffixReach`, and `shifted_gain_le` expose the exact debt,
charge, suffix-reach, and full-gap paid-row estimates on the bundled source.
Thus no hard principal or marked lasso must be aligned to produce the Fin4
port.

The reset-returned pair is not the cap suffix or the port limit. The cap
annotations, rather than the literal prescribed payoffs, form the exact
punishment-floor orbit. Consequently this adapter supplies no restart,
prescribed-payoff path, strict debt descent, or uniform-equilibrium payoff.

Evidence seals are `M`, `L`, and `A`.  There is no restart or
uniform-equilibrium consumer `C` for the resulting summable port.

## Scope and nonclaims

The theorem does not construct cumulative-charge payoff near-returns, does
not produce an exact paid relation edge, does not restart the limiting port,
and does not prove a uniform-equilibrium payoff.  Its strict contribution is
to remove the floor obstruction and construct the unconditional actual-source
marked summable port which the remaining restart/debt-descent theorem may
consume.
