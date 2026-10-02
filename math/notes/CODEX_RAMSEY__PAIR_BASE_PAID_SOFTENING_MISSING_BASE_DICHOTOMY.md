# Pair-base paid softening exposes an uncontrolled missing-base face

Author: `CODEX_RAMSEY`

## Status

Ordinary mathematics, proved below and awaiting independent review.  This
note applies the cross-mass calculation in
[`CODEX_RAMSEY__STRICT_TOGGLE_SOFT_BELLMAN_CROSS_MASS_BARRIER.md`](CODEX_RAMSEY__STRICT_TOGGLE_SOFT_BELLMAN_CROSS_MASS_BARRIER.md)
to the actual `Fin 4` same-source paid/reset target.  It finds one genuine
same-source average toggle inequality, but also proves that a live exact
softening must either delete the paid debtor from the root or put fixed mass
on a face to which neither the target law nor the full-support singleton
packet assigns the needed signed reward information.

This is a precise residual obstruction, not a paid-port consumer or a
well-founded descent theorem.

## 1. The actual source and its extra datum

Let

```text
target : FinFourPairBasePaidResetTarget reward witness owner b c             (1.1)
```

be the checked target inside a
`FinFourSameSourcePaidResetCapPort`.  Put `B={b,c}` and let `F` be its
two-player complement.  The target root has:

- both `b` and `c` Quit surely;
- the two free marginals equal to the selected induced-Nash point;
- one debtor `d in B` with unrestricted terminal debt at least
  `Gamma=witness.terminalGap`; and
- the other base player `e`, uniquely determined by `B={d,e}`.

Write `nu(A)` for the product probability that exactly the free coalition
`A subset F` Quits in the target row.  The first useful fact is stronger than
a bare paid-time label.

### Proposition 1.1 (same-source averaged leave gap)

The actual target data imply

```text
L_d := sum_(A subset F) nu(A)
  [ r(A union {e})_d - r(A union {d,e})_d ] >= Gamma.    (1.2)
```

### Proof

Player `d` Quits surely in the target root, so its prescribed payoff is its
pure-Quit endpoint `Q_d`.  Since the distinct opponent `e` also Quits surely,
the opponents' Continue mass is zero.  The stationary unrestricted cap is
therefore exactly `max(Q_d,C_d)`, by
`quittingStationaryUnilateralCap_eq_max_div`; `C_d` is the payoff from
Continuing at the row.  The field `target.debtor_gap` says

```text
max(Q_d,C_d)-Q_d >= Gamma,
```

and hence `C_d-Q_d>=Gamma`.  Conditioning on the two free marginals gives
exactly (1.2).  No limiting paid-row argument or reselection is used.  QED.

Thus the same-source target really controls a nonlocal average of four
membership-toggle comparisons, all on rows containing the other sure base
player `e`.

## 2. Base-softening dichotomy

Assume `|reward(S)_i|<=M`, and let `x` be any continuation vector with
`|x_i|<=M`.  Consider the most literal two-base softening of the target:

- retain the target's two free marginals exactly;
- let `p` be the Quit probability of the paid debtor `d`;
- let `z` be the Quit probability of the other base player `e`.

Call the resulting product root `q(p,z)`.  The target itself is `p=z=1`.

### Theorem 2.1 (debtor deletion or missing-base mass)

If `q(p,z)` is exact endpoint Nash against `x`, then

```text
p=0
```

or

```text
z <= 2M/(Gamma+2M),
1-z >= Gamma/(Gamma+2M).                               (2.1)
```

In the second branch, the product action law assigns total mass at least
`Gamma/(Gamma+2M)` to cells whose quitting coalition omits `e`.  Since there
are only eight such cells on `Fin 4`, one cell, possibly the all-Continue
cell, has mass at least

```text
Gamma/[8(Gamma+2M)].                                  (2.2)
```

More generally, if the row is `epsilon` endpoint Nash and `p>=theta>0`, then

```text
1-z >= (Gamma-epsilon/theta)/(Gamma+2M).               (2.3)
```

In particular `epsilon<=theta Gamma/2` gives the positive lower bound
`Gamma/[2(Gamma+2M)]` on the missing-`e` face.

### Proof

Let `G` be the expected payoff advantage of Continue over Quit for `d` at
`q(p,z)`.  Conditional on `e` quitting, the retained free law makes this
advantage exactly `L_d`, which is at least `Gamma` by Proposition 1.1.
Conditional on `e` continuing, it is a difference of two reward/tail
coordinates and is at least `-2M`.  Hence

```text
G >= z Gamma -(1-z)2M
  = (Gamma+2M)z-2M.                                   (2.4)
```

The regret from the prescribed marginal to pure Continue is exactly `pG`.
For an exact endpoint-Nash root it is nonpositive.  If `p>0`, (2.4) forces
`z<=2M/(Gamma+2M)`, proving (2.1).  Formula (2.2) is pigeonhole on the eight
configurations of the remaining three players when `e` continues.

For an `epsilon` root with `p>=theta`, endpoint Nash gives `pG<=epsilon`,
so `G<=epsilon/theta`; combine with (2.4) and rearrange to obtain (2.3).
QED.

The first branch is an exact action-support loss relative to the paid target:
the selected full-gap debtor disappears from the root.  It is not, by itself,
a decrease of terminal-semantic debt support, because the new successor need
not be an attained paid/reset carrier source.  The second branch is a fixed
departure from the two-sure-base face.

## 3. Exact cancellation required by an interior converter

Suppose now that `0<p<1` and `0<z<1`, and that `q(p,z)` is exact endpoint
Nash.  Let

```text
H_d(x) := sum_(A subset F) nu(A) h_A(x),               (3.1)
```

where

```text
h_A(x) = r(A)_d-r(A union {d})_d       if A is nonempty,
h_empty(x) = x_d-r({d})_d.                             (3.2)
```

This is Continue-minus-Quit conditional on the other base player `e`
continuing.  Exact mixing of `d` gives

```text
0 = z L_d +(1-z)H_d(x),
H_d(x) <= - z Gamma/(1-z).                             (3.3)
```

Thus an interior exact converter requires a quantitatively opposite-signed
average on the missing-base face.  Equivalently, at least one `A subset F`
must satisfy a Quit-over-Continue comparison of size at least
`z Gamma/(1-z)` (with `A=empty` interpreted as the solo-versus-tail
comparison).

This is the exact cross-row inequality missing from the current producer.
It is not enough to know that *some player* has a terminal-gap toggle at each
of those coalitions: (3.3) requires the paid debtor `d`, the displayed
orientation, and the same free-law weights `nu`.

## 4. Why the full-support hard residual does not supply (3.3)

The same table also has the checked
`FinFourQuantitativeFullSupportHardResidual`.  Its extra fields do not fill
the missing average:

1. `QuittingNormalizedSingletonSourcePacket` and
   `normalizedSoloMatrix` use singleton rewards.  The terms in (3.2) compare
   `A` with `A union {d}`; for singleton `A` they already require a pair row,
   and for the two-free-player `A` they require a triple row.
2. `hardPrincipalDispatch` supplies harmful singleton columns, singleton
   helpers, or a three-by-three singleton determinant.  None is a membership
   comparison on the pair/triple rows in (3.2).
3. Full packet support is support of an auxiliary singleton mixture.  It is
   not a statement that the target's free marginals, or a later cap-Nash
   root, put positive mass on the corresponding singleton event.
4. All-player punishment normality says `P_d<=r({d})_d`; it does not choose
   the sign of any fixed pair/triple term in `H_d(x)`.

There is also no hidden information in the same-source terminal law.  Since
`e` Quits surely at the target, that law gives zero probability to every row
appearing in (3.2).  The fixed-law reset retains this same law, so its joint,
incidence, transfer, and supported-toggle fields remain blind to the entire
missing-`e` face.

At the level of the target/cap-port structure, one may change player `d`'s
payoffs on nonsingleton coalitions omitting `e` without changing the target
profile, its terminal law, its prescribed payoff, any player's own payoff
except `d`'s off-law counterfactuals, the base-debtor gap, or the paid row.
The singleton hard matrix is unchanged as well.  This observation is a field
independence audit, not a claim that an arbitrary such perturbation preserves
the ambient terminal witness or punishment normality.

## 5. Consequence for actual cap roots

Theorem 2.1 is an actual-data theorem only for roots on the two-base softening
face, i.e. roots retaining the selected free induced-Nash marginals.  The cap
roots in `QuittingPaidCapLiftedSource.SummablePort` are not asserted to stay
on this face.  They may change all four marginals, and the checked exact
trichotomy permits the literal all-Continue inert stall.

Therefore the exact remaining alternatives are:

- prove a new selector theorem keeping the cap root on the target free face
  and then consume either debtor deletion or the missing-base mass;
- prove (3.3), or an equivalent source-matched cross-row cancellation, from
  additional nonsingleton data; or
- use a genuinely nonlocal Bellman block which does not pass through this
  softening face.

Merely combining the same-source port with the full-support hard principal
does none of these things.  The labels are same-table but the required law,
orientation, and nonsingleton row are not aligned.

The checked strict-minimum all-Continue tube strengthens the obstruction near
the global minimum: there no positively absorbing exact root exists at all.
Theorem 2.1 concerns tails outside that tube and should not be presented as a
replacement for its linear-defect or debt-moat conclusions.

## 6. Sources and exact scope

Checked declarations inspected:

- `FinFourPairBasePaidResetTarget`, `debtor_gap`, and
  `exists_finFour_pairBasePaidResetDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetAlignment.lean`;
- `FinFourSameSourcePaidResetCapPort` and
  `nonempty_finFourSameSourcePaidResetCapPort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourSameSourcePaidResetCapPort.lean`;
- `quittingStationaryUnilateralCap_eq_max_div` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`;
- `FinFourQuantitativeFullSupportHardResidual` and `hardPrincipalDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
  and `FullSupportHardPrincipalDispatch.lean`;
- `QuittingFixedLawResetDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`.

No claim is made that debtor deletion regenerates a source, that the selected
missing-base cell is terminal rather than all Continue, that its reward has a
useful sign, or that an arbitrary cap-port root retains the target free law.
In particular this note does not close the descent or double-inert arms of
`sourceDescent_or_repairedDescent_or_doubleInert`.

Independent review is requested for Proposition 1.1, constants and
orientation in Theorem 2.1, the exact cancellation identity (3.3), and the
source-field audit in Section 4.
