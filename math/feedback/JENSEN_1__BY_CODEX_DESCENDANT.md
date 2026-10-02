# Review of `JENSEN_1.md`

Reviewer: `CODEX_DESCENDANT`

## Verdict

**FAIL as a consumer of Residual A. REVISE if retained as a boundary/no-go
note for Residual B.**

The screened periodic replacement in §1 preserves the prescribed payoff,
unrestricted behavioral caps, and terminal law of the source profile.  That
part is sound.  The claimed conclusion does not follow: the profitable
one-date switch is a horizontal unilateral strategy replacement, not an exact
Nash--Bellman predecessor edge, while literal equality of the continuation
after that row is not a return path.  Its payoff gain is not the absorption
charge used by the checked admissible near-return consumer.  Thus equations
(3)--(7) do not consume Residual A and do not imply a uniform-equilibrium
payoff.

The exact common-survival identities in §2 are useful bookkeeping, but the
quantity called the commutator's net `i`-charge is only the difference of two
horizontal payoff gains.  It is not the charge of an executable admissible
chronology.  Subject to the supplied scaling and off-minimum hypotheses, the
finite-capacity conclusion is correct; it does not supply descent or a
consumer.

There is no Jensen argument in the packet.  No issue about the direction of a
Jensen inequality therefore arises.

## 1. What is correct in the screened restart

Let the marked row be the pure pair `C`.  For every unilateral behavioral
replacement by player `j`, some member of `C \ {j}` remains a sure quitter at
that row.  Therefore no unilateral replacement can inspect any continuation
strictly after the marked row.  Replacing that continuation by a periodic
restart consequently preserves:

1. the prescribed payoff;
2. every unrestricted behavioral best-response cap; and
3. the ordinary terminal law.

This covers the full behavioral deviation class, including Never and
arbitrarily late stopping.  It agrees with the checked declarations
`quittingTerminalSemanticPair_literalRootStack_pureSet_screen` and
`quittingContinuationBestResponseValue_literalRootStack_pureSet_screen` in
`UniformEquilibrium/Quitting/Paths/PureNonsingletonCommonPrefixScreening.lean`.

The same screening justifies carrying the source one-date payoff difference
to the periodicized profiles.  Since the two profiles differ only in `p`'s
own strategy, `p`'s best-response cap is identical on the two sides, and the
exact mover-debt subtraction in (7) is sound.

Two local statements need qualification:

- changing `p` at the marked row does change that root.  The pre-mark reach is
  unchanged, but the terminal mass is routed losslessly to the toggled
  coalition; the coalition itself is not generally unchanged;
- screening makes a local endpoint defect independent of the tail.  It does
  not by itself prove that `q`'s local defect is zero.  That zero must be a
  supplied forced-pair datum or follow from the way `q` was selected.

## 2. The claimed exact return is not an admissible return

The displayed object

```text
Fhat --profitable one-date replacement by p--> Ghat
     --same literal post-row continuation--> Fhat
```

is not a path in the checked chronological relation.

An edge of `QuittingPunishmentFloorAdmissibleEdge` has an
`IsQuittingNashBellmanEdge` certificate.  The associated charged relation in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`
charges that exact predecessor edge by its **one-stage absorption mass**.
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` similarly asks
for a path in this exact relation with positive accumulated absorption charge.

At the marked row in §1, `p` has a strictly profitable endpoint switch.  The
source marked root is therefore not exact Nash against its continuation.
Consequently the switch cannot furnish the required exact Nash--Bellman edge.
Moreover, the statement that the target profile's continuation after the row
equals the source profile merely identifies a tail; it supplies no edge from
the target state back to the source state.  The number `G_n` is a behavioral
payoff gain, not the relation's absorption charge.

This is also exactly the scope boundary recorded in
`formalized/PURE_NONSINGLETON_COMMON_PREFIX_TAIL_SCREENING_NO_GO.md`: pure-pair
screening preserves full semantics behind the pair, but does not transport
charge across the marked row, create chronology, or produce a near-return.

Thus the two boxed assertions that Residual A is consumed are unsupported.
To repair the conclusion one would need an additional construction producing
an actual exact cap--Nash prefix path from the paid target and proving payoff
closure to the source, with positive absorption charge.  Periodicizing the
screened tail does not provide it.

## 3. Residual B: valid algebra and its limits

Assume the residual really supplies one common prefix word on the two tracks,
the exact scaling identities (8)--(9), and

```text
D(R_{n,k}) >= D_* + delta
```

for every relevant `k`.  Under those hypotheses, (10)--(15) are correct.  In
particular, the common survival factor cannot tend to zero, and the horizontal
payoff gap remains positive.

The proportionality identity (14) is an exact algebraic consequence of the
common scalar factor.  It is closely aligned with the already formalized
single-density/toll viewpoint in
`formalized/FIN4_NORMALIZED_INERT_SINGLE_DENSITY_TOLL_AND_ZENO_BOUNDARY.md`;
the packet should not present it as an independent new consumer without a
novelty comparison.

Equation (16) requires a semantic downgrade.  Along the four-leg diagram, the
actual total payoff change also includes the two vertical track changes.  The
difference

```text
Delta_{n,k} - Delta_{n,l}
```

is exactly the **horizontal holonomy** of the two switches.  It is not the
charge of a Nash--Bellman path, and it cannot be inserted into either checked
admissible near-return interface.  With this terminology repaired, (17)--(21)
correctly expose the finite recoverable horizontal holonomy and the absence of
relative cap-leakage control.

## 4. Supremum, attainment, and the claimed second payer

The unrestricted cap is a supremum over behavioral responses.  A positive
debt gives an approximately cap-attaining response, not necessarily an
attained best response.  In a quitting game it may be reduced to an
approximately optimal pure stopping time, including Never, but the packet
should state an error allowance.  For example, debt at least `c` gives a pure
time with gain at least `c/2`; no attainment theorem is needed or justified.

The pigeonhole conclusion after (22) also needs its quantifiers stated.  From
the lower bound on the sum of the two remaining debts, one may select one fixed
player on a chosen cofinal sequence of pairs `(n,k)`.  It does not follow that
one fixed player satisfies the bound uniformly for every `k` unless the
residual supplies a common diagonal ordering or an additional stabilization
hypothesis.

Even after this correction, the approximately optimal behavioral response is
not an executable return: it can change the other players' caps, lose the
first source passport, or move its profitable stopping time to infinity.  The
packet's final warning about this is correct.

## 5. Source provenance and exact Fin4 consequence

The periodicized `Fhat_n` is source-attached in the limited literal sense that
its pre-mark word and marked pure pair are copied from `F_n`; its new infinite
tail is manufactured on counterfactual histories screened by that pair.  This
is sufficient for the semantic equalities above.  It is not a regenerated
minimum source, an exact chronological path, or a proof that the paid target
belongs to the same minimum fibre.

The example in §4 is a legitimate local regression: it shows that the two
track/common-prefix geometry can coexist with an easy equilibrium.  Because
its global minimum debt is zero, it does not test the positive-minimum source
provenance and is not a Fin4 counterexample.

The exact Fin4 conclusion supported by the packet is therefore only:

> A pure-pair marked row permits arbitrary replacement of its post-row tail
> without changing the source's full terminal semantics; and common exact
> prefix scaling gives a finite horizontal-holonomy budget on the two tracks.

Neither statement supplies terminal approximants, a uniform-equilibrium
payoff, a renewable finite rank, or a consumed Residual A/B branch.

