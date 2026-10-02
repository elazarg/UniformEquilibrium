# The repaired singleton atom has the wrong sign for pair-base cancellation

Author: `CODEX_RAMSEY`

## Status

Ordinary mathematics, proved below and awaiting independent review.  This
note synthesizes the exact singleton source/repaired-law bridge in
[`CODEX_MINER__FIN4_MINIMAL_PASSPORT_DOUBLE_INERT_LAW_BRIDGE.md`](CODEX_MINER__FIN4_MINIMAL_PASSPORT_DOUBLE_INERT_LAW_BRIDGE.md)
with the actual pair-base softening obstruction in
[`CODEX_RAMSEY__PAIR_BASE_PAID_SOFTENING_MISSING_BASE_DICHOTOMY.md`](CODEX_RAMSEY__PAIR_BASE_PAID_SOFTENING_MISSING_BASE_DICHOTOMY.md).

The conclusion is negative but sharp: the repaired atom never supplies the
opposite-signed average required by an interior pair-base Bellman softening.
In its leave-toggle arm it has exactly the wrong sign; in its solo arm it does
not mention the needed joined row.  A rational four-player table co-realizes
the two laws and labels and makes the sign conflict literal.

This is an interface separation, not a counterexample to the conjecture.

## 1. The two inequalities to be aligned

Use four labels

```text
o, c, a, f.                                             (1.1)
```

In the singleton producer, `o` is the sure owner and
`F={c,a,f}` is the free set.  The repaired law `mu_rep` is supported on
nonempty subsets `A subset F`.  The reviewed affine bridge gives a selected
atom of mass

```text
mu_rep(A) >= Gamma/(28M)                               (1.2)
```

and at least one of

```text
r_o(A)-r_o({o})       >= Gamma/2,                     (S)
r_o(A)-r_o(A union {o}) >= Gamma/2.                   (L)
```

For comparison, try to use `o` as the paid debtor in a pair-base source with
other sure base player `c`.  Its free set is `{a,f}`.  If the pair-base free
law is `nu`, the missing-base average required by an interior exact softening
is

```text
H_missing = sum_(D subset {a,f}) nu(D)
  [r_o(D)-r_o(D union {o})]                            (1.3)
```

with the empty term interpreted using the continuation tail.  If the debtor
mixes and the Quit probability `z` of `c` satisfies `0<z<1`, exact mixing
requires

```text
H_missing <= - z Gamma/(1-z) < 0.                     (1.4)
```

This sign comes from cancellation of the positive leave advantage conditional
on `c` quitting.

## 2. Exhaustive label/sign comparison

### Proposition 2.1 (the repaired atom does not pay the cancellation)

Even if the singleton owner is identified with the pair-base paid debtor,
the selected repaired atom does not imply (1.4).

### Proof

There are two incidence cases and two atom alternatives.

1. Suppose `c in A`.  Then the leave comparison (L) is conditional on the
   other base player quitting.  It belongs to the already-positive `L_o`
   side of the pair-base decomposition, not to `H_missing`.  It can increase
   the positive term that must later be cancelled.
2. Suppose `c notin A`.  Then `A subset {a,f}`, so (L) is literally one term
   of `H_missing`.  But it says that term is at least `Gamma/2`, whereas
   (1.4) requires the weighted average to be strictly negative.  It has the
   opposite sign.
3. Alternative (S) compares the missing-base continuation row `r_o(A)` with
   the solo row `r_o({o})`.  The needed term compares `r_o(A)` with
   `r_o(A union {o})`.  No inequality between the latter two follows.

These cases are exhaustive.  QED.

There are two additional source-alignment losses before this sign audit can
even be invoked:

- the pair-base theorem does not force its emergent base debtor to equal the
  prescribed singleton owner `o`; and
- its selected two-free-player Nash law `nu` is not asserted to be a
  marginal, conditional law, or continuation of `mu_rep`.

Thus label and weight alignment are missing as well as the sign.

## 3. Quantitative burden if every alignment is granted

Suppose, beyond the checked interfaces, that `c notin A`, that the pair-base
debtor is `o`, and that the pair-base law assigns the same atom weight

```text
w=nu(A)=mu_rep(A) >= Gamma/(28M).                      (3.1)
```

If the repaired atom is in leave arm (L), write

```text
H_missing = w h_A +(1-w)H_rest,
h_A >= Gamma/2.                                       (3.2)
```

Then the exact cancellation requirement (1.4) forces, for `w<1`,

```text
H_rest <=
  [-z Gamma/(1-z)-w Gamma/2]/(1-w).                   (3.3)
```

If `w=1` and `z>0`, an interior exact softening is impossible.  Hence the
positive repaired atom does not pay the cross seam even under perfect
co-realization; it demands a still more negative comparison on another
missing-base atom.

## 4. A co-realized four-player separation table

The sign issue is realizable on one reward table, one singleton source law,
and one pair-base law.  This example deliberately omits the ambient positive
minimum/terminal witness and therefore is not a conjecture counterexample.

Let all unspecified reward coordinates be zero and set

```text
r_o({a})       =  1/2,
r_o({o,a})     = -1/2,
r_o({c,a})     =  1/2,
r_o({o,c,a})   = -1/2,
r_f({a,f})     =  1.                                  (4.1)
```

All rewards have magnitude at most `M=1`; put `Gamma=1`.

### Proposition 4.1 (same atom, wrong sign)

This table has all of the following exact properties.

1. With singleton base owner `o`, choose the free product point at which `a`
   Quits surely and `c,f` Continue surely.  It is an induced Nash point for
   the rows containing `o`.
2. The original profile terminates at `{o,a}` and its literal owner-Continue
   repair terminates at `{a}`.  Hence

   ```text
   mu_src=delta_{ {o,a} },
   mu_rep=delta_{ {a} },
   a_abs=1,                                            (4.2)
   ```

   exactly satisfying the affine law bridge.
3. Owner `o` gains one under the repair:

   ```text
   r_o({a})-r_o({o,a})=1.                              (4.3)
   ```

   Thus the repaired atom `{a}` has mass one and lies in the half-gap leave
   arm, with room to spare.
4. The repaired restriction is not terminal Nash: free player `f` gains one
   by joining `{a}`, because `r_f({a,f})-r_f({a})=1`.
5. With pair base `{o,c}`, choose the free point at which `a` Quits surely and
   `f` Continues surely.  It is again an induced Nash point.  Player `o` is a
   full-gap base debtor, since

   ```text
   r_o({c,a})-r_o({o,c,a})=1.                          (4.4)
   ```

   Player `f` has zero debt and unit incidence from either sure base player,
   so it meets the local zero-debt/incidence hypotheses imposed on a reset
   owner at the displayed target.  This local table does not supply the
   positive global minimum needed to invoke the reset dispatcher itself.
6. The singleton repaired law and the pair-base free law are both the same
   point mass on `{a}`.  Nevertheless the two conditional leave advantages
   for the pair-base debtor are

   ```text
   L_o = r_o({c,a})-r_o({o,c,a}) = 1,
   H_missing = r_o({a})-r_o({o,a}) = 1.                (4.5)
   ```

   Thus for every `z in [0,1]`, Continue beats Quit for `o` by exactly one.
   Any exact root preserving this free law and softening `o,c` must set the
   debtor's Quit probability to zero.  There is no interior cancellation.

### Proof

Every induced-Nash assertion is immediate because all relevant free-player
Quit and Continue endpoint payoffs are zero.  Equations (4.2)--(4.5) follow
directly from the displayed rows.  At the repaired profile the only changed
free payoff is player `f`'s profitable join, which proves item 4.  The
pair-base endpoint comparison for `o` is (4.4); all other selected free
comparisons remain zero.  Finally the conditional decomposition is the
convex combination `z L_o+(1-z)H_missing=1`.  Exact endpoint Nash therefore
forces `o` to Continue purely.  QED.

This is stronger than a labels-only objection: the owner/debtor, repaired
atom, free law, and pair-base law have all been aligned, yet the repaired atom
still reinforces the wrong side.

## 5. What extra theorem would suffice

The repaired-atom producer would feed the pair-base converter only after a
new disjunction of the following form:

```text
there exist c notin A and a pair-base target with debtor o
whose free law gives A fixed mass,
and
r_o(A union {o})-r_o(A) >= kappa>0;                   (5.1)
```

or a weighted version directly asserting

```text
H_missing <= -kappa.                                  (5.2)
```

Neither (S) nor (L) gives (5.1).  In fact (L) negates it by at least
`Gamma/2`.  A different possibility is to consume the positive leave atom
without trying to mix the owner: setting the owner to Continue purely is the
literal repair already present in the double port.  The checked repaired
port may itself be inert, so this is not a new chronological exit.

The singleton affine bridge is therefore valuable law provenance, but it
does not pay the pair-base cross-row seam.  The missing producer must select
an oppositely oriented atom, or use a nonlocal block in which the positive
leave gain is repaid elsewhere.

## 6. Sources, novelty, and nonclaims

The exact source inputs are Propositions 3.1--3.2 of Miner's note above and
the checked singleton chain declarations it cites.  The pair-base
cancellation formula and constants are from the Ramsey missing-base note
linked above.  Relevant checked structures are:

- `FinFourSingletonBaseResetRepairPaidChain` and
  `sourceDescent_or_repairedDescent_or_doubleInert`;
- `FinFourPairBasePaidResetTarget` and
  `FinFourSameSourcePaidResetCapPort`.

A narrow comparison found no theorem identifying the singleton repaired law
with a pair-base free law, prescribing the pair-base debtor, or reversing the
sign of the gain-aligned repaired atom.

The table in Section 4 is an exact reward-table regression for the displayed
interfaces, but it is not asserted to carry a terminal exploitability witness,
a positive global minimum, the full-support hard residual, or a checked
double-inert cap-port pair.  It does not rule out other Bellman roots or a
nonlocal converter.  The only theorem-level conclusion is that the repaired
atom and affine law bridge do not, by themselves or after perfect label/law
alignment, imply the opposite-signed `H_missing` cancellation.

Independent review is requested for the incidence/sign table in Proposition
2.1, inequality (3.3), every induced-Nash/debt/incidence assertion in the
four-player separation table, and the strict interface scope.
