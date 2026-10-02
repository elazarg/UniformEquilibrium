# Review of unique-debtor floor entrance and solo recycling

**Reviewer:** CODEX_EULER  
**Verdict:** `PASS`, with four explicit proof-writing handoffs before reuse.

## Claim checked

Starting from the reviewed Fin4 carrier `R` with one possible debtor `e`,
positive debt, and the full-normal/full-collider reward-table data, the note
claims:

1. every exact root at an underfloor tail has a quantitative opponent hazard;
2. recursive exact prefixing either reaches the punishment floor in finitely
   many steps or converges along a subsequence to a punishment-tight,
   floor-safe, unique-debtor carrier with a solo-face exact root; and
3. adaptive exact solo prefixing from a floor-safe carrier gives a strict
   floor-preserving debt descent, a uniform payoff through nonsummable charge,
   or a positive-debt all-Continue carrier stall.

I checked the result against
`TerminalSemanticFinFourSoloWallDispatch.lean`,
`PunishmentFloorForward.lean`, and
`PunishmentFloorInfiniteOrbitChargeDichotomy.lean`.

## 1. Lemma 2.1 and its constants: PASS

Let `f=chi_e-U_e>0`.  Punishment normality gives

```text
solo_e-U_e >= f.
```

If `A_{-e}(q)<min(f,gamma)/(12M)`, the three opponent marginals are each at
most `A_{-e}`.  The checked `4M` endpoint-difference stability estimate moves
the owner endpoint by strictly less than

```text
12M*A_{-e} < min(f,gamma) <= f.
```

Thus `q_e=1`.  In the collider comparison the owner marginal agrees exactly;
only the two remaining opponent marginals move, so the error is strictly less
than `8M*kappa <= 2gamma/3`.  The full-gap collider must also Quit surely,
contradicting `A_{-e}<kappa<1`.  The use of `|U_i|<=M` is legitimate for a
terminal-semantic carrier point.  Also `gamma>0` and `gamma<=2M` imply `M>0`
and `kappa<=1/6`.

The unique-debtor contraction is then exactly
`quittingTerminalSemanticDebtSum_prefix_le_one_sub_opponentAbsorption_mul`.
The zero coordinates remain zero by the checked coordinatewise prefix debt
bound plus carrier nonnegativity.

## 2. Floor entrance and tight limit: PASS

For every fixed `delta>0`, an index with `f_n>=delta` multiplies total debt by
at most

```text
1-min(delta,gamma)/(12M) < 1.
```

All intervening exact prefixes weakly decrease total debt, while every carrier
point has total debt at least `D_*>0`.  Hence there are only finitely many such
indices and `f_n->0` on an infinite recursion.  If
`solo_e-chi_e=zeta_e>0`, the all-Continue owner endpoint gap is at least
`zeta_e` at every underfloor state, so the same argument supplies one fixed
contraction at every step.  This proves finite entrance in the strict-normal
case and `solo_e=chi_e` in the infinite case.

The compact carrier limit is sound.  Every nonowner debt is identically zero,
the owner coordinate tends to `chi_e`, and every pair remains above the
positive global minimum.  For a nonowner, zero semantic debt gives `U_i=B_i`,
and the unrestricted cap dominates the behavioral punishment value; hence
all nonowners are floor-safe.  This is a carrier statement and does not need
attainment by one behavior profile.

The product estimate

```text
D_* <= D(X_N) <= D(X_0) product_{n<N}(1-A_n)
```

is correctly oriented.  It forces the finite products to stay above the
positive number `D_*/D(X_0)`.  Therefore no `A_n` equals one and
`sum A_n<infinity`, for example from
`1-x<=exp(-x)`.  Thus `A_n->0`.  Refining the already selected carrier
subsequence jointly in the compact root simplex gives an exact limiting root
against `Y.1`; all opponents of `e` Continue in that root.  Closedness of the
exact-root graph is the correct limit input.

## 3. Adaptive solo recycle: PASS

At a floor-safe carrier `X` with the same one-debtor vector:

- if all Continue is exact, arm 3 is immediate;
- if no solo-face exact root exists, compact separation gives a positive
  opponent-absorption floor and
  `exists_strictCarrierDebtDescent_of_opponentAbsorptionFloor` gives exactly
  the floor-safe strict-debt arm; and
- otherwise a non-all-Continue solo root has owner probability `0<p<1`.

The lower bound `p>0` follows because `p=0` is all Continue.  If `p=1`, the
full-gap collider has positive endpoint difference at the exact pure-solo
row, contradicting its prescribed Continue action.  Mixed owner
complementarity gives `X.1_e=solo_e`.

The checked theorem
`quittingTerminalSemanticDebt_prefix_solo_eq_of_uniqueDebtor` then preserves
the complete debt vector.  The floor-forward theorem preserves every floor,
and the successor identity preserves owner singleton tightness.  Hence
dependent choice yields a correctly oriented orbit

```text
X_(n+1).1 = Succ(X_n.1,q_n),
```

which matches the `policy` field of
`QuittingPunishmentFloorInfiniteOrbit`; there is no chronology reversal.
Carrier payoffs lie in the canonical reward box, so the orbit's `value_mem`
field is also available.  Literal profile attainment is not required by this
checked orbit consumer.

For solo roots, total absorption is exactly `p_n`.  Nonsummability therefore
feeds
`QuittingPunishmentFloorInfiniteOrbit.exists_uniformEquilibriumPayoff_of_not_summable_absorption`.
In the summable case, `p_n->0` and the exact successor formula gives the
coordinate movement bound `2M p_n`; prescribed payoffs are Cauchy.  Since the
debt vector is constant, cap coordinates converge to the same carrier-pair
limit.  The roots converge to all Continue, and the closed exact-root graph
gives the asserted all-Continue root at the floor-safe limit.  The positive
debt vector is retained, so this is correctly stated as an unresolved stall.

## 4. Required proof-writing handoffs

These are not mathematical objections, but they should be made explicit in a
formal statement or export packet.

1. Rewrite an arbitrary solo-face root `q` as
   `quittingSoloStationaryRoot e (q e)` before invoking
   `quittingTerminalSemanticDebt_prefix_solo_eq_of_uniqueDebtor` and before
   identifying its absorption with `p`.
2. In the infinite-product step, cite or prove
   `product(1-A_n)` bounded below by a positive constant implies
   `Summable A`; the one-line exponential comparison above suffices.
3. Explicitly package the adaptive sequence into
   `QuittingPunishmentFloorInfiniteOrbit`, including `value_mem`,
   `anchor_floor`, the forward `policy`, and `exactNash`, before applying the
   nonsummable-charge theorem.
4. In the summable limit, say that pair convergence follows from
   `B_n=U_n+d(Y)` coordinatewise; prescribed-payoff convergence alone would
   not establish convergence of an arbitrary semantic cap annotation.

## 5. Novelty and scope

The note does not duplicate
`exists_minimum_allContinueNash_of_soloSemanticSpine_survival_lower`.  That
theorem starts from a fixed minimum semantic spine and a survival lower bound,
whereas the present composition begins at the off-minimum Section 10 carrier,
uses the current floor deficit to enter the floor, and adaptively reselects a
solo root after each prefix.

The nonclaims are accurate.  The strict debt drop is real-valued and
source-specific, not a well-founded finite rank; the punishment-tight/allC
stall is not consumed; and no attained-profile chronology is inferred from
carrier prefixing.

