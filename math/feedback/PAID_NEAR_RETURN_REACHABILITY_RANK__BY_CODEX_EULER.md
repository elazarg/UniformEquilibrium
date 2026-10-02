# Independent review of the paid near-return reachability-rank patch

Reviewer: `CODEX_EULER`

Status: **REVISE; abstract finite-rank theorem PASS, paid/source interface not yet a producer**

## Claim audited

I audited `../paid_near_return_reachability_rank.patch`, especially the added
reachable-label rank wrapper, the regenerative marked-state package, the
failure-to-return implication, and the behavioral-profile cap-state embedding.
The two baseline files modified by the patch are not present in this checkout,
so this is a source-level mathematical/type audit rather than a successful
build of the patch.

Sources checked:

- `MathUE/ChargedPathBudget.lean`;
- `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`;
- `UniformEquilibrium/Quitting/Root/FirstBranch.lean`;
- `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `UniformEquilibrium/Quitting/Stationary/MinMax.lean`; and
- `notes/CHATGPT_EXTERNAL__PAID_BLOCK_HAZARD_PACKING_REDUCTION.md`.

## 1. Abstract relation and orientation: PASS

For a finite label map `ell`, let `Lambda(s)` be the labels reachable from
`s`, allowing the empty path.  Along an edge `s -> t`, every label reachable
from `t` is reachable from `s`.  If the edge has charge at least `c` and no
high-charge equal-label return exists, then `ell(s)` is not reachable from
`t`: otherwise prepend the edge to the witnessing path and obtain such a
return.  Since the empty path puts `ell(s)` in `Lambda(s)`, the inclusion is
strict.  Thus

```text
highChargeCount_c(path) + |Lambda(target)| <= |Lambda(source)|,
```

and in particular the high-edge count is at most the number of labels (the
slightly sharper bound subtracts the nonempty target rank).

The quitting relation direction in the patch is correct.  For
`QuittingPunishmentFloorAdmissibleEdge`, the relation source is `edge.tail`
and target is `edge.current`.  Hence the regeneration field
`edge.tail = state` and marked `edge.current` is a forward relation edge.
The zero-count induction case is correctly the empty path, with no alleged
positive charge.

The new theorem saying a serial marked high-edge successor rule contradicts
absence of an equal-label charged return is therefore correct.  Iterating for
`card Label + 1` high edges is more than enough.

## 2. Cells and failure direction: PASS with a required wording discipline

A finite cover is not itself a label map.  One must choose a deterministic
assignment, for example the first member of an ordered finite cover.  Pulling
that assignment back along payoff projection gives a genuine partition whose
fibres have the cover-set diameter.  The patch's cell-labelling structure is
the right type of supplied object, but any producer of it bears this
determinization obligation.

Only the following implication is valid and used:

```text
same cell + charged path  -> endpoint payoff error <= eta,
failure of eta-near-return -> no same-cell charged return.
```

The converse fails near cell boundaries.  The patch's proof uses the correct
one-way implication.  Any prose describing failure as *equivalent* to
same-label prohibition must be changed.

## 3. Strict descent and regeneration quantifiers: mathematical PASS,
## producer claim overstated

The rank strictly decreases at every high edge under failure, and its
telescoping high-edge bound is sound.  The marked regeneration package,
however, assumes

```text
for every marked state, there exists an exact c-charged successor
which is marked again,
```

at every requested endpoint scale, with one global positive `c`.  This is a
serial closure property on the entire marked class, not merely “one local
successor” at the initial paid row.  Finite rank removes the separate
compact-recurrence step once that strong closure is supplied; it does not
construct the closure.

Moreover `marked` is an arbitrary predicate and the structure contains no
field tying its source or successors to a paid row, observer, atom, frontier,
or full-replacement profile.  The final consumer can ignore all eventual
paid-row hypotheses and return any regenerative family.  Consequently the
theorem is a valid sufficient conditional factorization, but its type does
not certify “source-matched paid provenance”.  Either:

1. weaken the names/docstrings to say that provenance *may* be encoded by the
   supplied predicate; or
2. add explicit source/provenance fields and preservation equations.

Without one of these repairs, the semantic interpretation is stronger than
the formal statement.

## 4. Behavioral cap state: valid state idea, mandatory literal repair

For an actual behavior profile `sigma`, its unrestricted behavioral
best-response vector is bounded and lies above the punishment floor.  Pairing
that vector with the stored all-Continue simplex root therefore gives a valid
floor-admissible boxed state.  The simplex root is only auxiliary annotation.

The patch's bound proof is not literally type-correct as written.  The checked
theorem

```text
abs_quittingContinuationBestResponseValue_le reward profile who hreward
```

requires the terminal reward-bound argument.  Both calls in
`quittingProfileCapAdmissibleState` omit

```text
(abs_reward_le_quittingRewardBound reward).
```

That argument must be supplied.  The floor proof also relies on unfolding the
`iSup` best-reply value into the `sSup (range ...)` continuation value; it is
mathematically exact, though a build should confirm the proposed `simpa` under
the baseline imports.

More importantly, this cap state stores `B(sigma)`, not the prescribed payoff
`U(sigma)`.  It is not automatically the source/current state of the paid
row, an exact Bellman successor, or a state with positive outgoing charge.
The new regeneration/consumer definitions do not use `admissibleCapState`.
Thus it is a correct canonical **cap-state embedding attached to a profile**,
not yet a paid-source adapter.

## 5. Novelty and exact surviving result

The earlier finite-packing note already establishes that more than the number
of payoff cells' worth of high edges on one supplied path forces a close
charged return.  The reachable-label construction is the useful local,
well-founded presentation of the same pigeonhole obstruction: it permits a
producer proof to be organized as repeated marked blocks and exposes a
natural-number descent.  It is not a stronger packing theorem and is not a
new paid producer.

The exact surviving contribution is:

> A supplied deterministic finite payoff labelling plus a globally serial,
> fixed-threshold, marked exact-edge regeneration rule forces an admissible
> payoff near-return after finitely many regenerations.

The outstanding conjecture-facing task remains constructing that rule from
the paid behavioral source while preserving floors, exact Bellman roots,
charge, and source provenance.

## Verdict

**REVISE.**  The relation orientation, empty-path convention, finite rank,
strict decrease, high-edge bound, and conditional near-return theorem pass.
Before the patch can be accepted, add the missing reward-bound arguments and
repair the provenance/“one local successor” claims.  No export is warranted:
the main paid exactification producer is still assumed rather than proved.
