# Positive-Never off-minimum corner: retained charge or all-Continue cap face

Author: `CODEX_EULER`

Status: **proved ordinary mathematics; internal pending independent review.**
This note consumes the strict singleton-over-cap arm of the fixed off-minimum
corner produced in
[`CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION`](CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION.md).
It does not consume the remaining all-Continue cap-face arm and is not an
export candidate before review.

## 1. Question and exact answer

Work in one finite quitting game with reward table `r`, terminal
exploitability gap `gamma>0`, and a global terminal-semantic debt minimum

```text
m,                 D_* = D(m) > 0.
```

Let `sigma_n` be actual behavioral profiles and suppose

```text
Sem(sigma_n) = (U_n,B_n) -> X=(U,B).                 (1.1)
```

The intended application is the fixed actual off-minimum corner selected by
the reviewed maximum-support positive-Never rectangle theorem.  At every
`sigma_n`, the terminal gap supplies an actual full-gap paid cap port.

There is an exact dichotomy at the limiting cap:

1. `r_i({i}) <= B_i` for every player `i`; equivalently all Continue is an
   exact cap root at `B`.
2. Some fixed player has a strict singleton-over-cap gap.  Then every
   sufficiently late actual paid cap port retains a uniform positive amount
   of total absorption, hence pays a uniform positive terminal-semantic debt
   drop.  In particular it is neither inert nor an unquantified excursion.

Thus the reviewed off-minimum corner reduces to the single named scalar
obstruction

```text
forall i, r_i({i}) <= B_i,                            (AC)
```

the **all-Continue cap face**.  Positive joint-Never mass and the three-label
rectangle are used upstream to produce the fixed corner; they are not
silently claimed to survive the cap-prefix port.

## 2. Uniform retained-charge theorem

Fix a reward bound `M>=0`:

```text
|r_i(S)| <= M
```

for every nonempty coalition `S` and player `i`.

### Theorem 2.1 (strict limiting cap gap has a uniform charge price)

In addition to (1.1), suppose that for some player `i` and `kappa>0`,

```text
B_i <= r_i({i}) - kappa.                              (2.1)
```

For each `n`, choose any object

```text
actual_n : QuittingActualProfileTerminalGapPaidCapPort
             r m sigma_n gamma.
```

Then, eventually in `n`,

```text
a_kappa <= actual_n.source.totalAbsorption,            (2.2)

a_kappa := kappa/(kappa+4M) > 0,                       (2.3)
```

and, writing `L_n` for the semantic cap-port limit,

```text
D_* a_kappa <= D(Sem(sigma_n)) - D(L_n).               (2.4)
```

Consequently every late port has a strict quantitative debt descent.  Under
the terminal gap it cannot lie in the charged-return arm either (that arm has
the checked uniform-payoff consumer), so the actual exact trichotomy selects
`QuantitativeDebtDescent`.

### Proof

By (1.1), eventually

```text
B_{n,i} <= r_i({i}) - kappa/2.                         (2.5)
```

Let `q_n` be the time-zero root of the literal cap-prefix orbit.  The checked
declaration
`quittingCapLiftedPrefixRoot_exactNash` says that it is exact root Nash
against `B_n`.  Passing through
`isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash`, apply

```text
gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
```

with `eta=kappa/2`.  This gives

```text
kappa/(kappa+4M) <= quittingRootAbsorptionMass(q_n).   (2.6)
```

The complete absorption is the sum of the nonnegative absorption masses of
all cap-prefix roots, so its time-zero summand is no larger than the total.
This proves (2.2).

The checked cap-port budget

```text
QuittingPaidCapLiftedSource.minimum_mul_totalAbsorption_le_debtDrop
```

says

```text
D_* actual_n.source.totalAbsorption
  <= D(Sem(sigma_n)) - D(L_n).
```

Together with (2.2), this is (2.4).  Since `D_*>0` and `a_kappa>0`, the drop
is strict.  Positive total absorption excludes `InertStall`.  Finally,
`QuittingActualProfileTerminalGapPaidCapPort.quantitativeDebtDescent_or_inertStall`
uses the unrestricted terminal gap to exclude the checked charged-return
uniform-payoff consumer, leaving quantitative descent. `QED`

## 3. A scalar compatibility inequality at the corner

Continuity of total semantic debt and global minimality of `m` let (2.4) pass
to the limit without selecting a limit of the ports:

### Corollary 3.1

Under Theorem 2.1,

\[
 D(X)-D_*\ \ge\ D_*\frac{\kappa}{\kappa+4M}.          \tag{3.1}
\]

Indeed `D(L_n)>=D_*`, so (2.4) already gives
`D(Sem(sigma_n))-D_* >= D_* a_kappa`; now take the limit.

Thus a strict cap gap is impossible when the off-minimum excursion is too
shallow for its compulsory absorption price.  This is stronger than merely
saying that a selected root has positive charge: it gives a fixed same-source
charge and a fixed carrier-debt drop.

For a fixed finite player set define

\[
 \kappa(X)=\max_i\bigl(r_i(\{i\})-B_i\bigr)_+.
\]

If `kappa(X)>0`, choose a maximizing player and apply the theorem with any
smaller positive gap (or directly with the attained finite maximum).  If
`kappa(X)=0`, exactly (AC) holds, by
`isZeroQuittingRootNash_allContinue_iff_singleton_le`.

## 4. Application to the positive-Never rectangle

The reviewed theorem
`CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION` produces, after
one common subsequence, a fixed corner type among `Q,Y,Z` whose actual
semantic pairs converge to an off-minimum carrier point `X`.
Apply Sections 2--3 to that actual corner sequence.  The terminal-gap adapter
is source-native at each corner; no paid row is transported from another
rectangle corner.

Therefore:

```text
fixed off-minimum rectangle corner
  -> all-Continue cap face at its limit
     OR uniform retained cap charge + fixed semantic-debt descent. (4.1)
```

For the `Z` corner, the same boundary is also visible in the checked
`resetExcursion_absorbingReturn_or_allContinue_capFace`.  The present argument
does not require `Z`-specific reset provenance and therefore also applies when
the fixed off-minimum corner is `Q` or `Y`.

## 5. Probability and agency audit

- `sigma_n` are literal behavioral profiles in the original game.
- The full-gap paid row at each `sigma_n` comes from
  `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort`; it is not
  selected at a different source.
- Behavioral caps `B_n` optimize over unrestricted behavioral deviations.
- The cap-prefix root Nash condition is a one-stage product-root condition,
  but its continuation coordinate is the unrestricted behavioral cap.
- The absorption lower bound is valid for every exact endpoint-Nash product
  root against `B_n`, including pure and boundary roots.
- The uniform-payoff contradiction used to remove the charged-return arm is
  the unrestricted uniform-payoff conclusion of the checked near-return
  compiler.

## 6. Source audit

Declarations inspected:

- `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` and
  `QuittingActualProfileTerminalGapPaidCapPort.quantitativeDebtDescent_or_inertStall`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`;
- `quittingCapLiftedPrefixRoot_exactNash` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
- `gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash` in
  `UniformEquilibrium/Quitting/Boundary/Repair/FixedTailUniformAbsorption.lean`;
- `minimum_mul_totalAbsorption_le_debtDrop` and the exact trichotomy in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
- `isZeroQuittingRootNash_allContinue_iff_singleton_le` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`; and
- `resetExcursion_absorbingReturn_or_allContinue_capFace` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetExcursionReturn.lean`.

No declaration inspected already packages Theorem 2.1 for a varying actual
off-minimum source sequence.  The argument is a short composition of checked
pieces plus the elementary time-zero-summand bound.

## 7. Strict nonclaims and next question

This note does **not** prove that the rectangle forces `kappa(X)>0`.  It does
not preserve positive-Never law mass through the cap port, regenerate the
maximum-support rectangle at `L_n`, or orient a natural-valued rank.  It also
does not consume the scalar all-Continue cap face (AC).

The exact remaining question is now narrower:

> Can a fixed off-minimum corner produced from a maximum-support
> positive-Never minimum rectangle satisfy all singleton cap inequalities
> `r_i({i})<=B_i`, or does the late-release/reset provenance force one strict
> violation?

An independent falsification review should check especially the time-zero
absorption-to-total step, source-native use of the terminal-gap adapter at
`Q/Y/Z`, and whether (2.4) is correctly interpreted as carrier debt descent
rather than regenerated rectangle provenance.
