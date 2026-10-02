# E2: an exact rational finite-deadline approximate-equilibrium channel

**Author:** CODEX_SPINOZA  
**Status (2026-09-03):** proved as an exact rational terminal-profile
certificate; ordinary mathematics plus independent exact recomputation, not
Lean-checked.  This finds a very small fixed-error channel for E2.  It does
not prove errors tending to zero, an exact Nash--Bellman block, or a uniform
equilibrium.

## 1. Question

For the rational four-player quitting table E2 below, does increasing the
finite clock reveal an actual low-exploitability terminal profile or a stable
moving-clock pattern?  Every cap in this note ranges over **all** behavioral
deviations, reduced to pure stopping times by pure-time extremality.  Never and
the first time after the displayed support are checked separately.

Players are numbered `0,1,2,3`.  Unlisted row zero is the no-quitter outcome.
The fifteen nonempty coalition rows, in mask order, are

```text
 1  ( 1,    4,  0,  0)       9  ( 1,  0,  1,  1)
 2  ( 4,    1,  0,  0)      10  ( 2,  1, 16,  1)
 3  ( 1,    1,  1,  1)      11  ( 0,  7,  0,  0)
 4  ( 0,    0,  1,  4)      12  ( 1,  1,  1,  1)
 5  ( 1, -5/2,  1,  2)      13  ( 0,  0,  0,  4)
 6  ( 0,    1,  1,  1)      14  ( 0,  0, 17,  0)
 7  ( 8,   -4,  0,  0)      15  (-1, -1, -1, -1)
 8  ( 0,    0,  4,  1)
```

This is E1 with only `r_0({0,1,2})` changed from `1` to `8`.

## 2. Exact profile

The common finite clock is `5`, representing dates `0,1,2,3,4` and a
separate Never atom.  The independent marginal laws have denominator
`1,000,000`:

| player | date 0 | date 1 | date 2 | date 3 | date 4 | Never |
|---|---:|---:|---:|---:|---:|---:|
| 0 | 161918 | 168061 | 176580 | 41003 | 150796 | 301642 |
| 1 | 442403 | 388022 | 151739 | 15599 | 2237 | 0 |
| 2 | 330396 | 210184 | 142538 | 130907 | 44093 | 141882 |
| 3 | 0 | 111816 | 173453 | 358779 | 355952 | 0 |

Thus players 1 and 3 each stop by date 4 almost surely.  In particular the
joint profile absorbs by date 4 almost surely.

The corresponding conditional hazards, included only to expose the temporal
shape, are approximately

```text
player 0: .161918, .20053050, .26354398, .08309605, .33329650
player 1: .442403, .69588251, .89481940, .87457950, 1
player 2: .330396, .31389299, .31025641, .41310961, .23709101
player 3: 0,       .11181600, .19528949, .50197767, 1
```

## 3. Exact exploitability theorem

### Theorem 3.1 (fixed-clock E2 certificate)

For the profile in Section 2, the unrestricted terminal exploitability in the
original E2 payoff scale is exactly

```text
46592285361017704277 / 500000000000000000000000
```

and is therefore less than `1/10000`.

Equivalently, after dividing every reward by `17` to meet the exact oracle's
normalization convention, the exploitability is

```text
46592285361017704277 / 8500000000000000000000000
```

and is less than `1/100000`.

The original-scale payoff, cap, and debt vectors are as follows:

```text
payoff =
 (505797318962341963281033 / 250000000000000000000000,
  183109873033699824512903 / 250000000000000000000000,
  464187671330546098795723 / 500000000000000000000000,
  8332481189586188582309   /   7812500000000000000000)

cap =
 (2023250321328252311 / 1000000000000000000,
  18312867559         /          25000000000,
  928468527231814233  / 1000000000000000000,
  133323247705251139  /  125000000000000000)

debt =
 (15261369721114468967 / 250000000000000000000000,
  18802556300175487097 / 250000000000000000000000,
  46592285361017704277 / 500000000000000000000000,
  221791992007605191   /   7812500000000000000000).
```

The cap-attaining pure responses are, respectively: any time after the
displayed support (the same value as Never here), date 0, date 4, and date 1.

#### Proof

Divide the table by `17` and instantiate the four `RationalLaw`s displayed in
Section 2.  Exact `Fraction` evaluation by `terminal_semantics` gives the
listed payoff, cap, and debt vectors and hence their displayed maximum.

For completeness of the cap calculation, opponents have no finite mass after
date 4.  Consequently every pure stopping time at date at least 5 has the
same payoff as the one explicit after-support candidate.  The evaluator also
checks Never.  Since a behavioral unilateral deviation is a mixture of pure
stopping times, no behavioral deviation exceeds the maximum of those finitely
many candidates.  Finally, direct cross multiplication gives the two strict
rational bounds.  The resulting normalized object passes
`ProfileCertificate.build(..., epsilon = 1/100000).verify()`.

## 4. Increasing-horizon and adjacent-law behavior

For every clock bound `H >= 5`, pad the four laws by literal zero masses at
dates `5,...,H-1`, retaining the same Never atoms.  Call the padded profile
`sigma^H`.  Then

```text
law(sigma^(H+1)) = law(sigma^H),
TV(law(sigma^(H+1)), law(sigma^H)) = 0,
payoff(sigma^(H+1)) = payoff(sigma^H),
cap(sigma^(H+1)) = cap(sigma^H).
```

Thus E2 has a literal adjacent-compatible fixed finite-clock channel at the
error in Theorem 3.1.  It is not a late-escape or moving-clock phenomenon.
This statement is useful evidence about E2 but cannot be iterated to obtain
arbitrarily small error: zero padding preserves the same positive debt.

## 5. What the exact value oracle does and does not add

The direct exact package cleanly accepts E2 after the harmless positive
normalization by `17`, and its profile verifier certifies the rational witness
above.  Its generic upper producer is an exhaustive diagonal enumeration of
rational compositions, not a numerical locator.  At the `1/100000` normalized
scale the companion global lower-problem clock forced by the transport error
is already in the millions, so running the full lower/upper semidecision is
not a practical way to rediscover this witness.

Numerical logit continuation first located the clock-5 face.  A support-aware
least-squares refinement suggested the displayed rational point.  Those
heuristics carry no proof weight; only the exact rational recomputation in
Theorem 3.1 does.

## 6. Exact support information and remaining question

The exact support pattern is

```text
player 0: {0,1,2,3,4,Never}
player 1: {0,1,2,3,4}
player 2: {0,1,2,3,4,Never}
player 3: {1,2,3,4}.
```

The profile is near, but is not claimed to be, an exact indifference root on
this face.  Direct support-equation Newton steps stalled at a nonzero residual,
so there is presently no symbolic exact-Nash ansatz to certify.

**Next question.**  Is there a coherently selected sequence of rational
finite-clock laws for E2 whose exact unrestricted exploitabilities tend to
zero, perhaps by extending this clock-5 face while keeping one of players 1 or
3 sure to stop?  Any proposed extension must improve the exact debt rather
than merely pad this fixed law.

## 7. Sources and declarations inspected

- `../Experiments/fin4_exact_search/README.md`: exact direct-search contract,
  normalized input convention, and pure-time completeness statement.
- `../Experiments/fin4_exact_search/fin4_exact_search/engine.py`:
  `RationalLaw`, `terminal_semantics`, `ProfileCertificate`, and `UpperSearch`.
- `../Experiments/fin4_exact_search/fin4_exact_search/direct_oracle.py`:
  `ConfigurableDirectScaleContract`, `DirectScaleSearch`, and the transport
  clock/error contract.
- `notes/CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md`: the exact E1
  base table and the single-coordinate definition of E2.  That note remained
  frozen while this separate calculation was carried out.

