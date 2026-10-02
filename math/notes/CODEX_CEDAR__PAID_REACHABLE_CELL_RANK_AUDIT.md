# CODEX_CEDAR — audit of the paid reachable-cell rank argument

## Status

**Abstract finite-relation lemma: PASS after an explicit label-selection and
orientation clarification.  Claimed paid-source adapter: FAIL / missing the
entire regenerative-successor producer.  Novelty: none at the abstract level.**

This audit checks the following proposed route.  Fix a charge threshold
`c>0` and endpoint tolerance `eta>0`; finitely label the payoff box by cells
of `l_infinity` diameter at most `eta`; define `Lambda(s)` to be the set of
labels reachable from `s`; and use `rho(s)=|Lambda(s)|` as a rank.  A charged
edge allegedly lowers the rank strictly.  If every marked paid state has
another marked edge of charge at least `c`, iteration should therefore force
the payoff near-return required by
`questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`.

The exact project relation checked here is
`quittingPunishmentFloorAdmissibleChargedRelation` from
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`.
Its edges are oriented

```text
tail  --->  current,
```

even though `IsQuittingNashBellmanEdge` lists `current` before `tail`.
Behavioral execution reads a Bellman prefix in the reverse direction.

## 1. The exact abstract lemma

Let `R` be a directed relation on states, let `pay(s)` be the payoff
projection, and let `L` be finite.  Assume a **function**

```text
ell : State -> L
```

such that

```text
ell(s)=ell(t)  ==>  ||pay(s)-pay(t)||_infinity <= eta.       (1.1)
```

Assume there is no finite `R`-path whose endpoint payoffs satisfy the right
side of `(1.1)` and which contains an edge of charge at least `c`.  Define

```text
Lambda(s) = {ell(t) : there is an R-path s ->* t}.
rho(s)    = |Lambda(s)|.
```

For an edge `s -> s'`, prepending that edge to every path from `s'` gives

```text
Lambda(s') subseteq Lambda(s).                              (1.2)
```

If the edge has charge at least `c`, this inclusion is strict.  Indeed,
`ell(s)` belongs to `Lambda(s)` by the empty path.  If it also belonged to
`Lambda(s')`, choose `s' ->* t` with `ell(t)=ell(s)` and prepend `s -> s'`.
The resulting path contains the charged edge and has `eta`-close endpoint
payoffs, contrary to the hypothesis.  Therefore

```text
rho(s') < rho(s)                                             (1.3)
```

on every high-charge edge, while arbitrary edges only weakly decrease the
rank.  In particular a path has at most `|L|-1` high-charge edges unless it
already contains the requested near-return.

This proof is correct in the project's relation orientation: `s` is the
edge's `tail` and `s'` its `current`.  The reverse behavioral-prefix reading
must not be substituted into `(1.2)`.

### Cover versus partition

A finite cover is enough, but it is not itself a label function and its
members need not be disjoint.  One must choose, for each payoff point, one
cover member containing it and define `ell` by that choice.  Each fibre of
`ell` is then contained in one cover member, so `(1.1)` follows.  No
equivalence relation or partition claim is justified by an overlapping
cover.  Conversely, once the single-valued `ell` and `(1.1)` are stated, no
partition theorem is needed.

The weak/strict endpoint convention must also match the cell diameter.  The
maintained question accepts coordinate errors `<=eta`, so diameter
`<=eta` is adequate.  A consumer demanding `<eta` would require strictly
smaller cells (for example an `eta/3` cover), not merely diameter `<=eta`.

## 2. The regenerative quantifier that would make it work

The precise sufficient hypothesis is much stronger than existence of paid
rows.  For one fixed marked subset `M` of one fixed charged state relation it
must say

```text
for every s in M, there is an edge e with
src(e)=s, charge(e)>=c, and tgt(e) in M.                     (2.1)
```

The same `c`, relation, payoff projection, and marking must be used after
every step.  Finite choice iterates `(2.1)` for `|L|` steps.  Then either the
rank drops below zero, or, equivalently by direct pigeonhole on the visited
labels, an ordered subpath has `eta`-close payoffs and contains a high-charge
edge.

The following weaker statements do **not** imply `(2.1)`:

1. for every accuracy there exists some paid row;
2. every paid profile has a behavioral deviation or a row with positive
   first-disagreement gain;
3. every marked source has a high exact edge whose target is not proved
   marked;
4. the target can be annotated by unrelated paid data after forgetting the
   source law; or
5. the reverse behavioral chronology reaches another profile.

In particular, “marked” cannot merely mean that some paid datum exists
somewhere on the same reward table.  It must be a provenance property that is
preserved by the selected exact edge.  No checked paid-source theorem
inspected here supplies that closure.

There is also a useful severity check.  Under a terminal exploitability
witness, every exact floor-admissible path has the common finite charge bound
from `QuittingTerminalExploitabilityWitness.prefixCharge_le`.  Thus `(2.1)`
would by itself build prefixes of charge `Nc` for arbitrary `N` and
contradict the witness, even before payoff cells are introduced.  The missing
marked-successor closure is therefore essentially a conjecture-closing
producer, not a small consequence of the rank notation.

## 3. The cap/all-Continue attachment does not supply regeneration

For a behavioral profile `sigma`, let `(U,B)` be its terminal-semantic pair.
There is a valid but limited finite-dimensional observation:

- `B` is bounded by the reward box;
- `B` dominates the behavioral punishment floor;
- Quit-now shows `r_i({i})<=B_i` for every player; hence
- the all-Continue product root is exact Nash at tail `B`, and its Bellman
  successor is again `B`.

So `(B, allContinue)` can be installed as an abstract floor-admissible boxed
state after spelling out those inequalities.  This does **not** prove that
`B` is the simultaneous terminal payoff of one behavior profile; the cap
coordinates are playerwise best-response suprema.  More importantly for the
present argument, the installed edge is the zero-charge identity edge.  It
provides neither the high-charge edge nor preservation of paid provenance in
`(2.1)`.

A paid first-disagreement row is a behavioral unilateral-gain witness, not a
simultaneous exact product-Nash root at `B`.  Attaching the all-Continue root
does not convert that row into an admissible Bellman edge.  Nor does the
floor-admissible state type remember the source stopping law, endpoint atom,
observer, or first-disagreement witness needed to call its successor paid.

The failure is not merely a missing formal wrapper.  Section 32 of
`notes/CODEX_CEDAR__PAID_ROW_REENTRY.md` gives one exact four-player reward
table and an actual semantic pair `(U,B)` for which `U` has a charge-one exact
floor-admissible self-loop, while `B` has all-Continue as its **unique** exact
product-Nash root.  Thus cap diagonalization literally erases charge one.
The independent review is
`feedback/CODEX_CEDAR__PAID_ROW_REENTRY__BY_CODEX_EULER__SECTION_32.md`.
Proposition 61 of the same note further records the fixed semantic-to-cap
Bellman seam under a terminal gap.  These checked boundaries rule out treating
the cap attachment as provenance-preserving regeneration.

## 4. Duplication audit

The finite-rank proof is a reformulation of existing generic charged-return
pigeonhole machinery:

- `MathUE/FiniteChargedReturn.lean` proves
  `exists_same_label_with_large_charge_gap` and
  `exists_close_pair_with_large_charge_gap_of_finite_labels`;
- `MathUE/CompactFiniteChargedReturn.lean` turns a compact payoff cover into a
  close charged return and gives the finite-prefix producer quantifiers; and
- `MathUE/ChargedPathBudget.lean` defines `highChargeCount` and proves its
  charge-sum lower bound.

For a path all of whose selected edges have charge at least `c`, the proposed
claim is even the elementary repeated-label special case: among `|L|+1`
visited sources two have the same label, and the segment between them contains
the earlier high edge.  The reachable-label rank is a correct alternate
proof, but supplies no new producer.

The quitting-specific budget facts are already packaged by
`QuittingTerminalExploitabilityWitness.reachablePath_chargeSum_le_prefixChargeBound`
and `highChargeCount_mul_threshold_le_prefixChargeBound` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean` and
`UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitConsequences.lean`.

## Verdict

The `Lambda/rho` lemma is valid after making the label map single-valued and
using the exact `tail -> current` relation orientation.  Conditional on the
uniform regenerative hypothesis `(2.1)`, it does force the maintained payoff
near-return.

It does **not** currently advance the paid producer.  The only new substantive
hypothesis is `(2.1)`, which is neither implied by paid first-disagreement data
nor preserved by attaching the cap/all-Continue state.  That attachment yields
a zero-charge synthetic fixed point and can erase an existing charged root.
Since the abstract closing step already exists in stronger generic form, this
route becomes conjecture-facing only if one proves a source-matched marked
high-charge successor theorem.  No such theorem is present in the proposed
argument.

