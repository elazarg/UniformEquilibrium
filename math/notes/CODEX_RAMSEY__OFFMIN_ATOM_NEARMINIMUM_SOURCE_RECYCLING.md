# Off-minimum finite atoms recycle at fixed scale into near-minimum paid/reset sources

Author: **CODEX_RAMSEY**  
Status: **fixed-weight theorem independently reviewed PASS twice; internal** —
[`Euler`](../feedback/CODEX_RAMSEY__OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING__BY_CODEX_EULER.md),
[`Miner`](../feedback/CODEX_RAMSEY__OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING__BY_CODEX_MINER.md)  
Date: 2026-08-26

## 1. Question and exact disposition

The reviewed positive-Never half-release construction can end at a strict
off-minimum `q=0` point carrying a positive finite terminal atom.  The checked
pure-Never-marginal normal form separately supplies actual near-minimum
sources and arbitrarily deep inert cap stacks.  Can compactness or strong
finite-clock density put the off-minimum atom back on a source converging to
the global minimum without losing actual behavioral provenance?

There is a precise fixed-scale positive answer.

> **Fixed-weight near-minimum source-recycling theorem.**  In a Fin4
> counterexample with terminal gap `gamma>0` and positive global debt minimum
> `D_*`, every actual positive stage atom of mass `m` can be grafted with one
> fixed weight `lambda>0` onto all sufficiently near-minimum actual profiles.
> The grafted sources remain inside the unique-all-Continue cap tube, retain
> the atom with the uniform mass floor `lambda^4 m`, carry a full-`gamma`
> paid cap port, and admit literal half resets with gain at least `gamma/4`,
> a fixed recipient debt rise at least `gamma/24`, and target atom mass at
> least `lambda^4 m/2`.

The construction is an actual fixed-scale consumer of the off-minimum
endpoint into the checked near-minimum reset/transfer interface.  It is not
yet a `FIN4_BT_QUESTION` output.  The remaining obstruction is event/sign
alignment: the imported atom's coalition/date are unrelated to the paid
mover and reset recipient, and the independent marginal graft introduces
mixed cross-branch events without the endpoint's loss-free toggle sign.
For a nonsingleton imported atom the available collision gain is only
`O(lambda^8)`, while the universal source-excess toll is `O(lambda)`.

If one additionally demands a construction whose displayed estimates certify
that the grafted source debts converge exactly to `D_*`, rather than merely
remain in its fixed open tube, one may make the optional choice
`lambda_n->0`.  This is only a sufficient minimum-convergence variant.  The
`56 M lambda` upper bound does **not** prove that fixed-weight convergence is
impossible when a particular table has cancellation.

## 2. Data

Fix a Fin4 quitting reward table `reward`, a reward bound `M>0`, and a
terminal-exploitability witness `witness` with

```text
gamma := witness.terminalGap > 0.
```

Let `minimum` be a global terminal-semantic minimum,

```text
D_* := D(minimum) > 0.
```

Let `eta` be any actual behavioral profile with a positive literal stage
atom: for some date `t`, nonempty coalition `S`, and `m>0`,

```text
StageMass(eta,t,S)=m.                               (2.1)
```

For the half-release endpoint, `S={a}` and `m` may be taken to be the
released joint-Never mass at its late release date.  The argument does not
use singleton structure and also applies to a stage selected from a carrier
law by
`exists_jointRealizers_finiteWindow_positiveStage_of_lawMass_pos`.

Choose actual profiles `pi_n` satisfying

```text
D(pi_n) -> D_*.                                     (2.2)
```

When the pure-Never-marginal chronology is desired, take `pi_n` from
`QuittingMinimumLawCausalSuffixPureNeverMarginalLimit`; this additionally
retains its own minimum-law atom behind an inert all-Continue word.  Nothing
below treats weak convergence of those marginal clocks as total-variation
convergence.

## 3. Independent whole-law graft

For `0<lambda<1`, define `rho(pi,eta,lambda)` by replacing, independently for
every player `i`, the complete stopping law of `pi_i` by

```text
(1-lambda) Law(pi_i) + lambda Law(eta_i).            (3.1)
```

Each marginal is realized by
`quittingStoppingLawMixtureBehaviorStrategy`.  The playerwise branch coins
are independent; this is not a public or correlated mixture of the two whole
profiles.

### Lemma 3.1 (uniform semantic perturbation)

For Fin4 and rewards in `[-M,M]`, write `rho=rho(pi,eta,lambda)`.  Then, for
every player `i`,

```text
|U_i(rho)-U_i(pi)| <= 8 M lambda,                   (3.2)
|B_i(rho)-B_i(pi)| <= 6 M lambda,                   (3.3)
|d_i(rho)-d_i(pi)| <= 14 M lambda,                  (3.4)
|D(rho)-D(pi)| <= 56 M lambda.                      (3.5)
```

#### Proof

Couple each mixed marginal to its `pi` marginal by first drawing its branch.
The full prescribed outcome can differ only if at least one of the four
branch coins selects `eta`, an event of probability at most `4 lambda`.
Since every payoff lies in `[-M,M]`, (3.2) follows.

For a fixed deviation of player `i`, only the three opponent laws matter.
The analogous coupling has mismatch probability at most `3 lambda`, uniformly
over the deviating behavioral strategy.  Thus the deviation payoff changes
by at most `6 M lambda`; taking the supremum before or after the estimate
proves (3.3).  Subtracting prescribed payoff from cap gives (3.4), and summing
four coordinates gives (3.5). `QED`

The constants are intentionally elementary rather than optimized.

This coupling lemma and the `lambda^4` mechanism are not new: they are the
four-coordinate specialization of the independently reviewed general
`k`-survivor interpolation in
[`CODEX_EULER__FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR`](CODEX_EULER__FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR.md).
They are restated here only to type the new minimum-fiber composition.

### Lemma 3.2 (literal atom retention)

The same profile satisfies

```text
StageMass(rho,t,S) >= lambda^4 m.                   (3.6)
```

#### Proof

Expand the four independent complete-law mixtures by their latent branch
coins.  On the event that all four coins choose their `eta` branches, whose
probability is `lambda^4`, the complete stopping-time vector has the law of
`eta`.  Its contribution to the nonnegative stage cylinder `(t,S)` is exactly
`lambda^4 m`; every other branch pattern adds nonnegative mass. `QED`

Equivalently, (3.6) follows by applying the affine one-coordinate stage-mass
formula four times and retaining only the `eta` endpoint term.  This is
literal stage provenance, not merely terminal-law mass.

If `pi` itself has a marked stage atom of mass `m_min`, the same expansion
simultaneously gives its retention with mass at least
`(1-lambda)^4 m_min`.

## 4. Fixed-weight return to the unique-all-Continue minimum tube

Let `epsilon_freeze>0` be supplied by

```text
exists_pos_nearMinimum_capNash_eq_allContinue_radius
```

for reference value `D_*`.  Put

```text
delta_0=min(epsilon_freeze,gamma/8)>0.               (4.1)
```

Choose once and for all `lambda in (0,1)` with

```text
56 M lambda < delta_0.                              (4.2)
```

For every sufficiently large `n`, (2.2) gives

```text
D(pi_n)-D_* < delta_0-56 M lambda.                  (4.3)
```

Put `rho_n=rho(pi_n,eta,lambda)` and
`e_n=D(rho_n)-D_*`.  Global minimality and Lemmas 3.1--3.2 give

```text
0 <= e_n < delta_0,                                 (4.4)
StageMass(rho_n,t,S) >= lambda^4 m > 0.             (4.5)
```

Every exact cap--Nash root against `B(rho_n)` is therefore literally all
Continue.  Thus `rho_n` is a near-minimum actual inert source carrying the
imported off-minimum atom.  The unique-root assertion is selector-independent.

At the same literal source, the checked theorem

```text
witness.terminalExploitability.nonempty_actualProfilePaidCapPort
```

supplies a full-`gamma` paid first-disagreement row and its cap-lifted
summable port.  This paid row need not use the atom's owner, coalition, or
date.

No step above requires `e_n->0`.  The cap-freezing theorem uses only the
pointwise open-tube inequality (4.4), and the arbitrary-profile paid-port
producer has no minimum-neighborhood hypothesis.

### Optional exact-minimum convergence variant

If the desired output is instead `D(rho_n)->D_*`, choose positive
`delta_n->0`, then take `lambda_n>0` with

```text
D(pi_n)-D_* <= delta_n/2,
56 M lambda_n <= delta_n/2.
```

This recovers the original convergence statement and atom floor
`lambda_n^4m`.  It is strictly weaker as a fixed-scale source packet and is
retained only as a safe sufficient construction for consumers whose literal
hypothesis is equality with, or convergence to, the minimum fiber.  Nothing
here rules out a table-specific fixed-weight sequence converging to `D_*`.

## 5. Uniform reset transfer while retaining the imported atom

The terminal witness gives a player `w_n` with

```text
gamma <= d_w_n(rho_n).                              (5.1)
```

Apply

```text
exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention
```

to `rho_n`, mover `w_n`, and near-minimum error `e_n`.  It returns an actual
half-reset target `chi_n` and a mover payoff gain `g_n` satisfying

```text
g_n >= d_w_n(rho_n)/4 >= gamma/4,                   (5.2)
d_w_n(chi_n)=d_w_n(rho_n)-g_n,                      (5.3)
g_n <= e_n + sum_(j!=w_n)(d_j(chi_n)-d_j(rho_n)),  (5.4)
StageMass(chi_n,t,S)
  >= (1/2) StageMass(rho_n,t,S)
  >= lambda^4 m/2 > 0.                              (5.5)
```

By (4.1)--(5.4),

```text
sum_(j!=w_n)(d_j(chi_n)-d_j(rho_n)) >= gamma/8.     (5.6)
```

There are three opponents.  After a finite subsequence, both the mover and
one fixed recipient `j!=w` are constant and

```text
d_j(chi_n)-d_j(rho_n) >= gamma/24.                  (5.7)
```

The same actual source `rho_n` therefore co-realizes:

1. a positive literal imported stage atom;
2. only all-Continue exact cap roots;
3. a full-`gamma` paid cap port; and
4. a literal half-reset carrying a fixed `gamma/24` opponent transfer and
   retaining the uniform atom floor `lambda^4m/2`.

This is stronger than separately actualizing the off-minimum carrier point
and the minimum source.  No source, target, law, or deviating strategy is
identified across independently selected profiles.

### Corollary 5.1 (the transfer has a uniform signed endpoint atom)

The positive recipient in (5.7) feeds the checked decoder

```text
hasQuittingEndpointDebtRecipientAtom_of_pos.
```

There are exactly `16` Fin4 terminal outcomes.  Hence, after a further finite
subsequence fixing which decoder branch and which terminal label `T` occur,
one of the following holds at every selected reset edge:

```text
quittingTerminalPayoffDifferenceAtom(reward,rho_n,chi_n,j,some T)
  >= gamma/768,                                    (5.8)
```

or there is a behavioral deviation `zeta_n` of `j` such that

```text
quittingTerminalPayoffDifferenceAtom
  (reward,update chi_n j zeta_n,update rho_n j zeta_n,j,some T)
  >= gamma/1536.                                   (5.9)
```

Indeed, `HasQuittingEndpointDebtRecipientAtom` gives respectively
`charge/2 <= 16 atom` or `charge/4 <= 16 atom`, while (5.7) gives
`charge>=gamma/24`.  This is a genuine named fixed-scale consumer of the
reset transfer.

It does not align the signed terminal `T` with the imported stage coalition
`S`.  Even when `T=S`, (5.8) is an endpoint law/payoff-difference atom, not a
profitable source deviation or an exact punishment-floor Bellman root.  In
the rectangle branch (5.9), the deviations `zeta_n` may also vary.  Thus the
decoder removes neither the event/sign seam nor the checked
endpoint-recipient source-mismatch obstruction.

## 6. Pure-Never marginal compatibility

Suppose `pi_n` comes from the checked pure-Never-marginal minimum chronology,
and retain the endpoint hypothesis that all Continue is an exact cap root at
`Sem(eta)` (uniqueness is stronger than needed here).  Common-delay `eta` by
the length of the inert word before applying (3.1).  The terminal law and
prescribed payoff are unchanged.  Its cap is also unchanged because the only
new deviation dates in the all-Continue prefix pay the singleton row, and
all-Continue cap-Nash gives `r_i({i})<=B_i(eta)` for every `i`.  Thus
`Sem(eta)` is unchanged and its atom mass is merely shifted in time.

Every fixed finite-time marginal mass of both branches then vanishes.  Hence,
after the already selected compact-law subsequence, the marginals of `rho_n`
also converge to pure Never even for the fixed positive `lambda` of (4.2).

This conclusion does not use weak-law continuity of terminal semantics.
Weak compact stopping-law convergence to Never does not control terminal
payoffs, caps, or relative-order outcome laws; the persistent atoms themselves
witness that discontinuity.  The fixed-tube estimate comes instead from the
explicit total-variation branch weight and (3.5).  Taking `lambda` small once
puts every sufficiently late source inside the tube while retaining the
uniform imported atom floor

```text
lambda^4 m at rho_n,   lambda^4 m/2 at chi_n.        (6.1)
```

For the optional stronger demand `D(rho_n)->D_*`, taking `lambda_n->0` is a
safe sufficient choice under the universal `56M lambda_n` estimate.  The
estimate is one-sided and does not make that choice logically necessary.

## 7. Exact conjecture-facing conclusion and nonclaims

The strict off-minimum `q=0` endpoint is not trapped merely because its own
cap chronology is inert.  Its actual stage atom can be returned at **fixed
positive scale** to literal sources inside the minimum all-Continue tube, and
the terminal witness then forces a same-source paid port and a uniform reset
transfer.

It does **not** prove any of the four accepted `FIN4_BT_QUESTION` outputs:

- `chi_n` need not return to the minimum fiber;
- the `gamma/24` recipient may rotate under further resets;
- the paid/reset mover and recipient labels need not align with the atom's
  coalition or toggle orientation;
- the paid-row labels are unrelated to `S,w,j`; and
- no punishment-floor Nash--Bellman edge is produced.

For a nonsingleton imported atom, the fixed scale does activate the checked
macroscopic causal dispatch, but only its already known tail-excursion versus
reached-gain/transfer split.  If

```text
alpha >= lambda^4 m
```

is the stage-mass floor, its universal reached-gain floor is

```text
g_0 >= alpha^2 D_*/8 >= lambda^8 m^2 D_*/8.         (7.1)
```

The graft source's certified excess toll is only

```text
e_n <= 56 M lambda + o(1).                          (7.2)
```

Making (7.1) pay (7.2) from these bounds alone would require

```text
448 M < lambda^7 m^2 D_*.
```

This cannot follow universally: `lambda,m<=1` and bounded Fin4 rewards give
`D_*<=8M`.  A table-specific cancellation can make the true excess much
smaller; the estimate only proves that the present universal bounds do not
supply that cancellation.

The half-reset avoids the eighth-order loss because its gain is
`gamma/4`, independent of the atom.  Precisely for that reason its mover,
recipient, and paid event are not identified with the imported atom.  The
remaining seam is therefore **event/sign alignment**, plus control of the
`2^4-2` cross-branch laws—not atom scale or carrier attainment.  The generic
positive-recipient decoder stops at its prescribed-atom versus
same-deviation-rectangle alternative, and the singleton outsider
regularization still lacks the conditional-mass sign threshold.

## 8. Declaration and source audit

Checked declarations used or targeted in a formal handoff:

- `quittingStoppingLawMixtureBehaviorStrategy` and the affine terminal/stage
  law formulas in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMixture.lean`;
- `exists_pos_nearMinimum_capNash_eq_allContinue_radius` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCapNashNearMinimum.lean`;
- `QuittingTerminalExploitabilityWitness.exists_terminalGap_le_terminalSemanticDebt`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTightness.lean`;
- `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`;
- `exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawGlobalRetention.lean`;
- `hasQuittingEndpointDebtRecipientAtom_of_pos` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionRecipientAtom.lean`;
- `endpointRecipientAtom_exactPrefixes_but_no_sourceMatchedObserverGain` in
  `Research/Quitting/EndpointRecipientAtomSourceMismatchNoGo.lean`, which
  prevents treating Corollary 5.1 alone as a profitable source row even after
  arbitrary-depth exact prefix access;
- `exists_jointRealizers_finiteWindow_positiveStage_of_lawMass_pos` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
  and
- `QuittingMinimumLawCausalSuffixAtom.nonempty_pureNeverMarginalLimit` in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionDispatch.lean`.

The `8M/6M/14M` coupling and `lambda^4` retention are reviewed existing
ordinary mathematics in
`CODEX_EULER__FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR`.  The new claim here
is only their composition with the positive minimum-fiber cap-freezing tube,
the same-source full-gap paid port, and the checked global-retention half
reset, including the `56M` total-debt bookkeeping and `gamma/24` recipient.
No theorem presently named in Lean packages that combined output.

## 9. Independent reviews

Euler's independent review checked the latent-branch construction, all four
coupling constants, literal stage provenance, near-minimum error, reset
constants, and pure-Never qualification.  Its appended fixed-weight delta
explicitly corrects the original vanishing-weight disposition.

Miner then independently falsified the fixed-weight strengthening and
returned **PASS**.  That review additionally checked the named downstream
consumers and the `O(lambda^8)` collision-gain versus `O(lambda)` universal
excess calculation.  Both reviews recommend internal status: fixed scale is
genuine, but no checked theorem aligns the atom event/sign with the paid
mover and reset recipient or regenerates the full source problem.
