# A fixed-charge carrier-source path starts off the minimum fiber or pays fixed aggregate root error

Author: `CODEX_RAMSEY`

Independent review:
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__PAID_RETURN_OFF_MINIMUM_AGGREGATE_ERROR_GATE__BY_CODEX_EULER.md)

Reviewed inputs:

- [`STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md`](STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md);
- [`FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md`](../formalized/FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md); and
- [`FIN4_STATIONARY_PAID_CARRIER_LINEAR_DEBT_MOAT.md`](FIN4_STATIONARY_PAID_CARRIER_LINEAR_DEBT_MOAT.md).

## Exact statement

Let the player type be literally `Fin 4`, let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

be a finite quitting reward table, and assume that its quitting game has no
uniform-equilibrium payoff.  Let

```text
Carrier = quittingTerminalSemanticCarrier reward,
D(X)    = quittingTerminalSemanticDebtSum X,
D_*     = min {D(X) : X in Carrier},
K       = {X.1 : X in Carrier and D(X)=D_*}.
```

Fix any charge threshold `a>0`.  There are constants

```text
eta_a>0,  e_a>0                                      (1)
```

such that the following holds.

Let `X in Carrier`, let `L` be any natural number, and let
`W_0,...,W_L` be payoff vectors with

```text
W_0=X.1.                                             (2)
```

For every `0<=s<L`, let `q_s` be an independent product root which is
`epsilon_s`-Nash against the tail `W_s`, with `epsilon_s>=0`, and suppose

```text
W_(s+1)=quittingRootSuccessorPayoff reward W_s q_s.  (3)
```

Put `E=sum_(s<L)epsilon_s`.  If one row has fixed charge,

```text
exists s<L, a<=quittingRootAbsorptionMass q_s,        (4)
```

then

```text
D(X)>=D_*+eta_a  or  E>=e_a.                         (5)
```

Consequently, every exact path (`epsilon_s=0` for all `s`) beginning at the
prescribed coordinate of an actual carrier pair and containing an edge of
charge at least `a` satisfies

```text
D(X)>=D_*+eta_a.                                     (6)
```

This exact corollary applies in particular to a path in the full punishment-
floor admissible charged relation when its source payoff is literally `X.1`.
An endpoint payoff near-return is an additional condition and is not needed
for (6).

## Conjecture-facing change

The live producer in
[`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md)
asks for exact floor paths containing a uniformly charged edge and having
arbitrarily close endpoint payoffs.  The reviewed local minimum-fiber results
did not by themselves say where the *source* of such a forward charged path
must lie.

This packet gives the source-level alternative.  A fixed-charge exact path
cannot start at, or converge in carrier debt toward, the minimum semantic
fiber.  For approximate Bellman paths, attempting to do so costs one fixed
aggregate root-error amount independent of path length.  Therefore a literal
paid-source near-return must use a fixed off-minimum carrier anchor before any
return construction begins.

The checked paid-row quantifiers already supply exactly one such source-
matched anchor: the full-replacement pairs converge to their strictly off-
minimum endpoint cluster.  Thus the theorem narrows but does not close the
paid branch.  It proves that the minimum plateau cannot be used as a charging
or restart port; it does not create a charged root at the off-minimum cluster
or repay its payoff seam.

## Proof

### 1. Linear minimum tube

The checked Fin4 minimum-fiber theorem supplies compactness and nonemptiness
of the minimum carrier fiber, a common positive singleton gap over it, and
uniqueness of the all-Continue exact product root at every payoff in its
prescribed projection `K`.

Apply the reviewed compact linear absorption-defect theorem and shrink its
neighborhood to a bounded open set `N`.  Choose `C>0` bounding every reward
coordinate and every payoff coordinate in `N`.  There are `c>0` and `rho>0`
such that the `rho`-collar of `K` is contained in `N`, and the reviewed
successor-linked theorem has the following Fin4 specialization in the checked
tail-to-current indexing:

if

```text
V_(t+1)=Succ(V_t,r_t),
dist_infinity(V_0,K)<rho/2,
E=sum_(t<L)epsilon'_t<c*rho/(16C),                   (7)
```

where `r_t` is `epsilon'_t`-Nash against `V_(t+1)`, then

```text
sum_(t<L) absorption(r_t)<=4E/c.                    (8)
```

The constants `16` and `4` are exactly the specialization
`Fintype.card (Fin 4)=4`.

### 2. Compactly price a source outside the inner collar

Set

```text
Far={X in Carrier : rho/2<=dist_infinity(X.1,K)}.    (9)
```

The carrier is compact, the distance map is continuous, and `Far` is closed
in the carrier; hence `Far` is compact.  It is disjoint from the entire
minimum fiber.  If it is nonempty, continuous total debt attains a minimum
`D_far>D_*` there.  Put

```text
eta_a=(D_far-D_*)/2.                                (10)
```

If `Far` is empty, put `eta_a=1`.  In both cases `eta_a>0` and

```text
D(X)<D_*+eta_a
  ==> dist_infinity(X.1,K)<rho/2.                   (11)
```

Define

```text
e_a=min(c*rho/(16C),c*a/4)>0.                       (12)
```

### 3. Apply the outward successor path

Suppose both alternatives in (5) fail.  Use the supplied sequence directly:
the checked successor theorem has exactly (3), with initial node
`W_0=X.1`.  By (11), that node lies within `rho/2` of `K`.  Since `E<e_a`,
(7)--(8) apply and
give

```text
a<=absorption(q_s)
 <=sum_t absorption(r_t)
 <=4E/c<a,
```

a contradiction.  This proves (5), and `E=0` proves (6).

## Paid full-replacement adapter

The source data quantified by
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` consist of a
`QuittingPositiveMinimumDebtTangentFamily frontier`, an active `mover`, a
`FullReplacementCluster endpoint`, and the strict inequality

```text
D(frontier.base)<D(endpoint.cluster).                (14)
```

The field `frontier.base_minimum` makes the left side equal to `D_*`.  Put

```text
g=D(endpoint.cluster)-D_*>0.
```

The field `endpoint.fullReplacement_tendsto` and continuity of total debt
show that the literal carrier pairs

```text
X_r=frontier.fullReplacementPair mover (endpoint.subseq r)
```

eventually satisfy

```text
D(X_r)>=D_*+g/2.                                    (15)
```

By definition, `X_r` is the semantic pair of

```text
frontier.fullReplacementProfile mover (endpoint.subseq r),
```

which is exactly the actual profile on which the eventual paid first-
disagreement rows are supplied.  Hence the checked paid sources already lie
in an off-minimum regime.  The theorem does not assert that `g/2=eta_a`, nor
does it assert that these late pairs satisfy the first arm of (5) for every
chosen `a`; it says that no source-matched producer can evade the general
debt/error gate by moving back toward `D_*`.

This is the only off-minimum anchor supplied by the displayed paid-row data.
It is not a claim that the global carrier has no other off-minimum points.  A
path beginning at an unrelated floor state requires a separate actual-source
adapter.

## Probability and deviation audit

Each row root is a product of private Boolean marginals.  Absorption is the
literal one-row probability `1-product_i(1-q_i)`.  Reversing the finite list
of payoff identities introduces no randomization and no independence across
dates.  Estimate (8) sums deterministic rowwise inequalities and is uniform
in the path length.

The theorem assumes one-stage product-root `epsilon`-Nash conditions.  It does
not relabel them as unrestricted behavioral equilibrium.  In the exact floor-
path corollary, the checked charged-relation decoder supplies precisely these
one-row exact Nash conditions and successor identities.  The downstream
payoff-near-return consumer, if a producer supplies the remaining path, is the
checked all-behavior projective-lasso consumer.

The paid source itself is an actual behavioral profile and its semantic cap
is unrestricted.  This packet uses only its carrier membership, convergence,
and total debt; it does not infer that its paid first-disagreement row is an
exact Bellman root.

## Boundary tests

1. **Off-minimum qualification is necessary.**  A charged exact root may
   exist at a payoff tail outside the all-Continue tube.  The theorem assigns
   it to the debt arm only when that tail is the prescribed coordinate of an
   actual carrier pair; no debt is assigned to arbitrary payoff vectors.
2. **Aggregate error is necessary.**  Errors `epsilon_s->0` rowwise with
   diverging path length need not have `sum_s epsilon_s->0`.  Such paths do not
   contradict (5).
3. **Fixed charge is necessary.**  If the largest row absorption tends to
   zero, (4) fails for every fixed `a`; the theorem gives no obstruction.
4. **Path orientation is load-bearing.**  The checked theorem starts from the
   continuation-tail source `W_0=X.1` and uses
   `W_(s+1)=Succ(W_s,q_s)`.  Reversing this list would constrain the wrong
   endpoint.
5. **Paid cluster does not contradict the theorem.**  Equation (15) shows
   that the accepted paid profiles are deliberately off-minimum.  The result
   therefore cannot manufacture an error toll at those sources without a new
   estimate away from the minimum fiber.

## Source and subsumption audit

The compact all-Continue linear estimate and its successor-linked path
version were proved and reviewed in the first input packet.  The Fin4 minimum
fiber, positive debt, strict gap, and carrier compactness are checked in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`.
The exact paid-source quantifiers are checked in
`UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`,
and the full-replacement convergence field is in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`.

The earlier stationary paid-carrier packet gives a debt alternative at one
literal tail and a path theorem whose near-minimum endpoint is supplied as a
hypothesis.  The new content here is the uniform **carrier-source**
debt/error dichotomy for every finite charged approximate path, obtained by
using the actual tail-to-current relation orientation and compactly pricing
sources outside the inner collar.  It turns the local path estimate into a
direct restriction on any source-matched paid-return producer.

No external literature result is used.

## Checked Lean realization

The result is proved in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourCarrierSourceChargeDebtErrorGate.lean`.
The exact declarations are:

- `exists_pos_carrierDebtMoat_of_infDist_minimumFiber` for the compact debt
  moat;
- `FinFourCarrierSourceChargeDebtErrorGate` and
  `exists_finFour_carrierSourceChargeDebtErrorGate_of_no_uniformPayoff` for
  the fixed constants;
- `FinFourCarrierSourceChargeDebtErrorGate.debt_or_error` for (5);
- `FinFourCarrierSourceChargeDebtErrorGate.debt_of_exactPath` for (6);
- `FinFourCarrierSourceChargeDebtErrorGate.debt_of_punishmentFloorAdmissiblePath`
  and its `_highCharge` form for the checked charged relation; and
- `eventually_base_add_half_clusterDebtExcess_le_fullReplacementDebt` for the
  literal full-replacement source anchor.

The gate has `M` and `L`.  It has source-level `A` and a relation-level `C`
when the path source payoff is explicitly identified with the prescribed
coordinate of an actual carrier pair.  The paid full-replacement theorem
supplies an actual off-minimum profile sequence, but no checked theorem yet
identifies a near-return path source with those profiles; no unconditional
paid-return adapter is claimed.

## Scope and nonclaims

- No exact root, floor-admissible edge, connector, descent, payoff return, or
  uniform-equilibrium payoff is produced.
- The theorem does not bound approximate paths beginning at arbitrary payoff-
  only floor states; source carrier provenance is essential.
- It does not force aggregate error at the already off-minimum paid cluster.
- It does not compare the paid cluster gap `g/2` with the theorem's selected
  `eta_a`.
- It controls total one-row absorption, not a selected marginal, collision
  incidence, observer, atom, or posterior.
- It does not authorize cap replacement, floor clipping, or a semantic seam.
- Endpoint payoff closeness is unused; the result is a necessary source gate,
  not the missing near-return producer.
