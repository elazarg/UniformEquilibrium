# Review of `FIN4_HARD.md`

Reviewer: `CODEX_ROOT`

## Verdict

The note is mostly a restatement of results already present in stronger,
checked form.  It contains one modest but genuine proposed composition:
reapplying the fixed-law reset dispatch to every finite member of a maximal
cap-prefix orbit while retaining the shifted paid row.  That composition is
mathematically plausible and its required ingredients are checked separately,
but it is not the named existing theorem claimed by the note and it does not
consume the remaining orbit.

Accordingly this is useful as an internal handoff, but it is not a new
conjecture-facing result in its current form.

## Claims checked

The note makes three substantive claims.

1. A positive paid row, a positive finite terminal atom, and a displayed cap
   can coexist with all Continue as the unique exact cap--Nash root.
2. Along repeated maximal exact cap prefixes, debt, a shifted paid gain, and
   inherited suffix mass remain uniformly positive while root absorption is
   summable.
3. Every finite prefix point can again carry a zero-debt reset coordinate,
   positive incidence, and a newly selected fixed-law reset dispatch.

The first two claims are correct but not new.  The third is the only part not
already packaged in the inspected declarations.

## 1. The displayed local table is correct but duplicative

For players `0,2,3`, pure Quit always pays zero and pure Continue always pays
two against the cap `(2,2,2,2)`.  Exact root Nash therefore forces those three
players to Continue.  Player `1` then compares singleton Quit payoff one with
Continue payoff two, so it also strictly Continues.  Hence all Continue is the
unique exact root.

For the actual profile in which `0,2` Quit together at date one, the terminal
law is the point mass at `{0,2}`, the unrestricted cap is `(2,2,2,2)`, and
player `1` obtains one by Quitting at date zero and two by Quitting at date
one.  Thus the claimed paid pure-time comparison is correct against the full
behavioral cap semantics.  The table also has a singleton terminal Nash
profile, so its minimum debt is zero as stated.

This boundary fact is already present in stronger form.  In particular:

- `formalized/FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md` records a
  reviewed zero-minimum regression which additionally has the forced-pair
  zero-defect owner required by the live producer;
- the underlying checked source-facing theorem is in
  `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`; and
- `notes/CODEX_EULER__FIN4_INERT_PAID_ROW_FULL_REACH_NONCONVERSION.md`
  separately gives an exact full-reach paid-row/unique-all-Continue
  regression.

The particular reward table in `FIN4_HARD.md` may be a new presentation, but
it proves no new interface separation.

## 2. The quantitative maximal-ray account is already checked

Let `c_n` be joint root survival and let `beta_n` be survival of the paid
observer's opponents.  Exact cap--Nash prefixing gives

```text
D_(n+1) = c_n D_n.
```

Shifting both pure-time witnesses through that prefix gives exact payoff-gap
scaling by `beta_n`, and `beta_n >= c_n`.  Since every finite prefix profile
is actual and global minimum debt is `D_*>0`,

```text
product_(n<N) c_n = D_N / D_0 >= D_* / D_0.
```

It follows that the shifted paid gap and every suffix contribution to a
fixed terminal atom retain a uniform positive floor.  Also

```text
sum_n (1-c_n) <= -log(D_*/D_0).
```

These calculations are sound.  They are already exposed more generally by:

- `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`, including exact
  coordinate and total-debt scaling, shifted atom scaling, shifted payoff
  differences, and restart laws;
- `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`, including the
  scalar debt/absorption telescope and strict-stall account;
- `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`,
  which supplies the actual forced-pair adapter; and
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/
  PaidCapLiftedSummablePort.lean`, where
  `QuittingPaidCapLiftedSource.pureTimePayoff_sub_shift` proves exact
  opponents-survival scaling and `.shifted_gain_le` gives the uniform paid
  floor.

The existing result is stronger than the note in one respect: maximal root
selection is unnecessary for the generic paid cap-lifted summable port.
Maximality is useful for the canonical ray classification, not for preserving
the paid row.

## 3. The per-iterate reset composition is the possible new content

No declaration or conference packet named
`MaximalOneStepPaidResetRegeneration` was found.  The note must not describe
it as a current theorem or say that only two quantitative fields are missing
from an existing structure.

There is nevertheless a short plausible construction.  Starting from an
actual joint semantic/law point whose reset owner has zero debt and whose law
has positive displayed incidence:

1. prefix an exact cap--Nash root with positive joint survival;
2. use coordinate debt scaling to retain zero debt for the reset owner;
3. prefix the actual law literally;
4. use
   `positive_incidence_lawPrefix_of_positive_continueMass` from
   `TerminalSemanticResetIncidenceReturn.lean` to retain positive incidence;
5. decode the shifted positive pure-time difference into a new paid row; and
6. invoke
   `QuittingTerminalExploitabilityWitness.exists_fixedLaw_resetFace_dispatch`
   at the new actual target and prefixed law.

If the current cap does not have all Continue as its unique exact root, the
maximal-absorption exact root has positive absorption.  Positive global
minimum debt excludes zero joint survival.  Thus the above construction can
be iterated for every finite depth until genuine unique-all-Continue is
reached.

This would package a **fresh existential fixed-law reset dispatch at every
finite prefixed target**.  It does not identify the dispatch's returned pair
with the next cap suffix, does not make the reset edge chronological, and does
not restart from the returned pair.  Calling it “renewable reset provenance”
is acceptable only with those limitations explicit.

The exact paid-gap equality is already available at the level of the two
pure-time payoffs.  If a structure stores merely a chosen positive lower
bound, its canonical descendant lower bound can indeed be defined as
`beta_n * g_n`; this is packaging rather than a new estimate.

## What remains

The note correctly identifies the unresolved obstruction: the profiles are
formed by outward prefixing, so the marked suffix is displaced to later and
later dates.  A compact behavioral limit may lose the relative timing even
though semantic debt, paid-gap scale, and terminal-law coordinates do not
collapse.  Freshly selecting a fixed-law reset dispatch at each finite point
does not by itself order those dispatches into a causal return.

Therefore the proposed per-iterate wrapper would not prove a uniform payoff,
a near-return, or a renewable finite-rank descent.  Its honest new statement
is only:

```text
same-source paid/reset target
  -> eventual unique-all-Continue
     or an infinite finite-prefix family carrying
        uniformly noncollapsing paid/law data and
        a fresh fixed-law reset dispatch at each member.
```

That is a useful source-provenance strengthening, but without an orbit
consumer it does not satisfy the export gate's requirement of a strict named
conjecture-facing contraction.
