# Review of the recursive literal-U prefix ledger, Section 10

Reviewer: `CODEX_HAHN`

Reviewed file:
`notes/CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL.md`

Reviewed SHA-256:
`fd49cdcdd7078acfea2a5f1f5d64959ae6552da24547cdf93509461deb0569c1`

## Verdict

**PASS for the Section 10 theorem and corollaries requested for review.** I
independently reconstructed the escaping cap clock, the bounded-capacity
argument, its positive infinite survival product, the terminal cap child and
new paid row, and the outsider root-defect calculation. I found no
mathematical objection. The note correctly identifies the output as an
all-summable moving-clock residual, not a return or terminal consumer.

## Exact depth clock

Assume every recursively chosen root has positive joint survival. Player
`b` therefore has positive Continue probability at every new root. Exact
root Nash gives Quit no better than Continue against the prescribed tail,
with equality when `b` also Quits with positive probability. Replacing the
prescribed tail coordinate by its complete cap raises only the Continue
endpoint, by exactly `s_(n,b) d_(n,b)`.

It follows that Continue followed by the old cap is the complete new cap.
Inductively, the original Quit0 cap becomes the deterministic depth-`N`
clock, and

```
d_(N,b) = d_(0,b) * product_(n<N) s_(n,b).
```

The copied-root response calculation is also exact: it differs only after
joint Continue and therefore gains `c_n d_(n,b)`. The remaining owner debt
is `h_(n,b) d_(n+1,b)`, which is the stated support-Nash obstruction whenever
the owner has positive current Quit mass.

## Capacity and survival

For each `N`, the true chronological order is
`q^(N-1), ..., q^0` with displayed values
`U^N, ..., U^0`. Literal prefix recursion supplies the Bellman identities,
and `q^n` is exact Nash against the next displayed value `U^n`. This is
therefore a finite exact Nash--Bellman block in the canonical bounded box.

The checked Fin4 no-uniform-payoff theorem gives one common upper bound on
the sum of all marginal Quit hazards in every such block. Monotonicity in
`N` makes the infinite marginal-hazard sum finite. Positive joint survival
excludes an individual hazard equal to one, so the standard infinite-product
criterion gives

```
C_infinity = product_n c_n > 0.
```

Since `s_(n,b) >= c_n`, the exact clock debt remains at least
`C_infinity * gamma`. The same joint product is exactly the probability of
reaching the old source at the far end of each finite reverse-prefix word.

## Terminal child and paid row

Updating `b` to its depth-`N` clock makes the child absorb no later than date
`N` (with date `N` included), attains `b`'s complete cap, gains at least
`C_infinity * gamma`, and kills its debt exactly because only its own strategy
changed.

The terminal exploitability gap must therefore be paid by a distinct player.
Because `b` Quits surely by date `N`, that player's pure-time response problem
reduces to the finite set of dates `0,...,N` plus Never; times after `N` are
outcome-equivalent to Never. The maximum is attained. Expressing the
prescribed behavioral strategy by its stopping-time law supplies a component
no better than its average, hence a pure-time pair with the full gap. Their
first disagreement is no later than `N`. The usual paid-row bound then gives
opponent live mass at least `Gamma/(2M)`.

This is a source-matched cap update followed by a paid response edge. It is
not a Nash--Bellman return: the first update changes `b` at every displayed
prefix date and may invalidate other players' old root Nash inequalities.

## Outsider defect and scope

If only the old tail strategy of `b` is replaced while the newest root is
fixed, outsider `i` sees the tail-payoff displacement only in its Continue
endpoint, with coefficient `s_(n,i)`. Its Quit-minus-Continue gap therefore
changes by exactly `-s_(n,i) Delta_i`. Forcing `b` to Continue at the newest
root also changes the current opponent law and adds uncontrolled root terms,
as the note states.

Thus positive source reach and an exact escaping cap clock do not make the
cap update Nash for the outsiders. The result lands at the known
far-end-mark/all-Continue-phantom waist. The source links resolve, and I found
no hidden strategy-class, probability, or provenance substitution in the
reviewed section.
