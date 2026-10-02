# Review of the alternating-seam forcing lemma

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md`,
Section 11, Proposition 6.

## Verdict

**Valid ordinary mathematics.**  The arbitrary calendar-start and finite-
horizon quantifiers check.  There is one harmless proof-writing omission:
for the weighted alternating sum one needs both sides of the elementary
pairing estimate, not only the lower bounds displayed in the note.  The
missing upper bounds are immediate and give the claimed constant exactly.

The proposition is an analytic ledger only.  It shows that an already
supplied exact alternating Bellman shuttle would meet the prescribed and
adverse-forcing budgets.  It does not construct a reached-tail shuttle,
retain frozen semantic sources, make all initial debts small, or supply
literal clocks.

## Prescribed calendar intervals

An arbitrary finite calendar interval intersects a consecutive finite segment
of the seam list; internal dates contribute zero.  Every consecutive finite
sum of

```text
+p,-p,+p,-p,...
```

is one of `-p,0,p`, independently of whether the interval begins or ends
inside a block.  Thus its absolute prescribed sum is at most `p<=eta`.

## Survival-weighted direct forcing

Fix a calendar start and enumerate only the seams reached before the chosen
finite horizon.  The generated weight at a later seam is the earlier weight
multiplied by additional secants in `[0,1]`; hence

```text
1>=w_0>=w_1>=...>=0.
```

Since `E_k=-P_k`, the adverse sum is `sum_k w_k P_k`.  For every finite
nonincreasing nonnegative sequence,

```text
0 <= w_0-w_1+w_2-... <= w_0,
-w_0 <= -w_0+w_1-w_2+... <= 0,                         (R4.1)
```

with the terminal sign handled by leaving one unpaired term.  The note states
the relevant lower bound in each case but omits the complementary upper
bound.  Equation `(R4.1)` supplies it and yields

```text
sum_k w_k P_k <= p w_0 <= p <= eta.
```

This holds for every start and every finite horizon, so it is stronger than
the eventual `eta+slack` clause.

## Scope of the shuttle application

Proposition 5 gives `E=-P` for one own-strategy replacement seam, and reversing
the same pair through the same bridge root gives the opposite amplitude.  A
partial own-strategy mixture can make that amplitude at most `eta` because
the prescribed terminal payoff is affine in the mixture while the mover cap
is invariant.  Those facts justify the proposed analytic alternation.

They do not imply that the successor reached after one literal block is the
semantic pair donated to the next orientation.  Concatenating independently
selected source and replacement profiles changes their continuation semantics;
the exact Bellman seams, bounded candidate chain, all-player small initial
debt, and clocks remain genuine additional hypotheses.  Thus Proposition 6
does not by itself interact nontrivially with the return/source producer.  It
only removes a false signed-ledger objection once such a shuttle is built.

