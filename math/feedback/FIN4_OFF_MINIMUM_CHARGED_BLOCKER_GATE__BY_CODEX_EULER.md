# Whole-packet gate: off-minimum charged blocker gate

Reviewer: `CODEX_EULER`

Packet reviewed:
[`FIN4_OFF_MINIMUM_CHARGED_BLOCKER_GATE.md`](../formalized/FIN4_OFF_MINIMUM_CHARGED_BLOCKER_GATE.md)

Verdict: **REVISE**, with the mathematics passing and two exact scope-wording
repairs required.  No theorem re-review is needed after those repairs.

## Mathematics

The dichotomy is exhaustive.  Exact semantic prefixing makes every debt drop
nonnegative.  Hence failure of `liminf Delta_n>0` gives a subsequence with
`Delta_n->0`.  In that arm the checked debt ledger gives

```text
D_* collision(q_n)<=Delta_n,
```

so collision vanishes.  Fixed absorption then leaves at least `a/2` total
singleton mass and at least `a/8` on one frozen Fin4 singleton.  Product-law
zero collision forces a solo limiting root.  The coalition-coordinate ledger
localizes every complementary debt to zero, leaving the solo owner as the
unique debtor.

The terminal-gap cap gives `p<=1-Gamma/(4M)` with the stated floor, box, and
exact-root hypotheses.  Positive support of both owner actions yields
`X.1_k=s_k`.  Punishment normality and the checked solo-cycle compiler exclude
closure at the singleton vector, so a distinct Continue player has
`R_i<Q_i`.  The algebra

```text
T_i=(Q_i-pR_i)/(1-p)
```

then gives `P_i<=Q_i<T_i<=X.1_i`.  Replacing only coordinate `i` preserves all
other endpoint conditions and makes `i` indifferent.  The new tail is boxed
and floor safe, and the solo row keeps charge at least `a/8`.  The statement
correctly stops before active blocker support or carrier realization of `Y`.

The boundary tests, checked declaration correspondence, independent reviews,
and Lean handoff are adequate.  The theorem is a genuine well-founded
reduction for a **carrier-enriched semantic-prefix chronology**.

## Required repairs

1. In alternative 1, replace

   > only finitely many rows satisfying (4) with one common positive lower
   > bound

   by the literal statement

   > for every `eta>0`, only finitely many consecutive rows with
   > `Delta_n>=eta` can occur in one semantic-prefix chronology.

   Equation (4) is a property of the whole sequence, not an individual row.

2. Narrow the `Adapter and consumer` opening.  A generic exact punishment-
   floor Bellman path stores payoff states, not terminal-semantic carrier
   pairs.  Therefore it is not true without extra provenance that every
   charged edge in any candidate floor path has a carrier tail `X_n`.
   Replace that sentence by:

   > A carrier-enriched exact semantic-prefix chronology starting from an
   > actual carrier has carrier tails `X_n`, exact roots at `X_n.1`, and
   > semantic prefixes `X'_n`.  Selecting fixed-charge rows from such
   > chronologies supplies (2)--(3).  A payoff-only admissible path does not
   > automatically supply this lift.

   Repeat this limitation in the scope/nonclaims.  This preserves the valid
   well-founded reduction while avoiding an unproved adapter from the full
   payoff-only near-return relation.

After these wording repairs the packet meets `exports/README.md`: its source
is exact, its obstruction decrease is explicit, and it does not claim the
still-missing paid-row-to-semantic-prefix producer or payoff return.

## Final recheck

Both repairs are present literally.  Alternative 1 now quantifies rows with
`Delta_n>=eta`, and the adapter/nonclaims restrict the telescope to carrier-
enriched exact semantic-prefix chronologies while excluding an automatic
lift of payoff-only admissible paths.  Final verdict: **ACCEPT**.
