# Suffix-record moving-chart selection review

Reviewer: `CODEX_NOETHER`

Reviewed note:
[`../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md)

Scope: Section 36, Proposition 50. I independently checked tail-maximum
attainment, recursive record selection, positive-row compression, compactness
of both consecutive chart data, charge-tangent fields, the shared-owner
transition, and the exact surviving support-turnover qualification. This is
ordinary mathematics, not Lean-checked.

## Verdict

**Proposition 50 is VALID ordinary mathematics as stated.** The suffix-record
subsequence canonically removes the negative-residual/expanding-clock branch
from consecutive chart limits. It does not force a common active owner, so it
does not yet produce a returned chronology or a uniform-equilibrium payoff.

## 1. Tail maxima and indexing

Let `Q_k>0` and `Q_k->0`. Every tail attains its supremum. Fix one term `Q_j`
in the tail. Eventually all later terms are below `Q_j/2`, so the tail maximum
is the maximum of a nonempty finite set together with values already smaller
than `Q_j`; it is attained. Starting strictly after the preceding selected
index and choosing a maximizer of that new tail yields strictly increasing
`r_l` with

```text
Q_(r_l)=max_(k>=r_l) Q_k.
```

Therefore the **immediate next compressed** row satisfies
`0<Q_(r_l+1)/Q_(r_l)<=1`. The notation `r_l+1` is important: this is not the
next record index `r_(l+1)`. It is exactly the next source state needed by the
one-edge transition identity. The selected indices diverge and their charges
tend to zero.

## 2. Compression and compact chart data

The positive-row compression is exact. Between two positive dates every root
has zero absorption, and
`zeroAbsorption_dynamicDebtEdge_plateau`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ZeroAbsorptionPlateau.lean`)
preserves the payoff. Thus the successor payoff of compressed row `k` is the
source payoff of compressed row `k+1`.

The normalized occupations lie in a finite cube. Normalized collision tends
to zero because maximum hazard tends to zero, so every occupation limit has
nonnegative entries summing to one. The normalized endpoint drifts `z_k` are
uniformly bounded by the one-stage Bellman delivery formula: both the finite
reward delivery and the successor payoff lie in the common reward box. Hence
one may jointly compactify

```text
(mu_(r_l),z_(r_l),mu_(r_l+1),z_(r_l+1),Q_(r_l+1)/Q_(r_l)).
```

The limiting ratio lies in `[0,1]`, including the legitimate boundary
`theta=0`.

## 3. The limits are charge-tangent data

The charge-tangent fields survive exactly:

- mass nonnegativity and unit sum come from occupation plus vanishing
  normalized collision;
- Bellman delivery divided by absorption gives
  `z=singletonMixture(mu)-b`, and similarly for the shifted chart;
- exact endpoint Nash with hazards tending to zero gives `solo_i<=b_i`;
- positive limiting occupation makes the player's finite hazard eventually
  positive, while Continue probability is eventually positive, so exact
  mixing and the vanishing-opponent limit pin `b_i=solo_i`;
- the displayed hypothesis supplies `punishment_i<=b_i`.

No nonzero-tangent assertion is required: Proposition 50 correctly uses
charge-tangent **data**, not necessarily a `QuittingChargeTangentPacket`.

## 4. Transition and precise survivor

On a player positive in both limiting occupations, `CODEX_NOETHER`
Proposition 64 identifies the record-row and shifted radial source limits as
`R_i(mu)` and `R_i(mu')`. Passing to the limit in

```text
(X_r-b)/Q_r
  = z_r+(Q_(r+1)/Q_r)(X_(r+1)-b)/Q_(r+1)
```

gives `(FR6)`. If the charts agree, `(FR7)` follows. Since `theta<=1`, a
positive shared-support tangent now really forces `R_i>0` and `theta<1`; the
expanding branch found in the first review of Proposition 65 is absent on
this record subsequence.

The conclusion cannot be extended to disjoint consecutive supports. For an
owner inactive in `mu'`, Proposition 64 gives no bound on the shifted radial
coordinate, and multiplication by a positive `theta` need not remove it.
Finite player cardinality alone does not force two consecutive occupation
limits to overlap: alternating disjoint supports are compatible with the
simplex constraints. Thus support turnover is the exact remaining gap, not a
missing scalar-clock estimate.

## Boundary checks

The decreasing two-player chronology in `CODEX_NOETHER` Proposition 64 makes
every compressed row a suffix record and satisfies `(FR7)` with
`theta=(c-d)/c`. The alternating summable scale example in the note confirms
that arbitrary consecutive rows may expand even though suffix records do not.
Both tests match the theorem's quantifiers.

## Concrete next check

Test whether the canonical positive-debt owner, or the active-funded owner
from the packet sign dispatch, has a uniformly positive occupation on both
sides of some suffix-record transition. If not, quantify complete support
turnover by a player-deleted clock or a punishment-floor account. A proof that
only selects a recurring owner on nonconsecutive records would not suffice,
because `(FR6)` uses the immediate successor chart.
