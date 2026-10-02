# Whole-packet gate: Fin4 collision-cycle face-sign cancellation

Reviewer: `CODEX_RAMSEY`

Date: 2026-08-25

Repository head checked: `a277602c`

Verdict: **REMOVE from `exports/`; retain the theorem in `notes/`**

The mathematics in
[`FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION.md`](../exports/FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION.md)
passes independent falsification.  The packet nevertheless fails the export
qualification and adapter/consumer gate in
[`exports/README.md`](../exports/README.md).  Its conclusion is a new static
same-table sign screen with no semantic consumer, no maintained finite-rank
decrease, and no elimination of a named live chamber.  The packet itself
correctly admits those limitations.  Under the current question-bank rule,
a proper semialgebraic narrowing or local lemma without a consumer belongs in
`notes/`, however useful it is.

This verdict is about export status, not theorem truth.

## 1. Mathematical claim and quantifiers

Fix a bounded Fin4 hard residual, choose any fixed-point-free collision map
returned by the checked selector, and choose a simple functional-graph cycle.
For an edge `e->j`, define

```text
Delta(e,j;T)=r_j(T union {e,j})-r_j(T union {e}).      (1)
```

The packet's conclusion is correct: some cycle edge and nonempty subset of
the two-label complement satisfy `Delta<=0`, while the empty-background
increment on that same edge remains at least the positive terminal gap.

For a future formalization, the exact statement should spell out that the
cycle labels are pairwise distinct and that
`f(e_t)=e_(t+1 mod m)`.  The present arrow notation and the word “simple” are
mathematically standard and caused no ambiguity in this audit, but those are
the quantifiers the Lean handoff must encode.

## 2. Bernoulli endpoint identity

When `e` Quits surely, conditioning on the independent Bernoulli actions of
the two labels outside `{e,j}` gives exactly

```text
Q_j-C_j = sum_T w(T) Delta(e,j;T).                    (2)
```

The weights are nonnegative and sum to one, including degenerate zero/one
marginals.  Since one opponent Quits surely, the opponent all-Continue mass
for `j` is zero.  Thus (2) is also the division-free face numerator; no
boundary division is hidden.

Strict positivity on every background makes (2) strictly positive even after
previous cycle labels have become sure quitters and the product law has
collapsed onto a smaller set of backgrounds.

## 3. One-source sure-quitting propagation

The call to
`nonempty_singletonBaseSameLawResetProducer` is correctly made once, with
cycle owner `e_0`.  Its root makes `e_0` Quit surely and its `point_mem` field
places all other labels in one exact induced persistent-base Nash point.

For a free next label `j`,
`quittingPersistentBaseRoot_free_purePayoff_le` gives

```text
Q_j <= U_j = p_j Q_j +(1-p_j)C_j.                    (3)
```

If (2) is positive, (3) forces `p_j=1`.  Simplicity ensures each receiver is
still free until the final edge.  Hence sure quitting propagates through the
entire cycle without reselecting a profile.

## 4. Final unrestricted owner-cap contradiction

On the closing edge, the last cycle player is a sure date-zero quitter and
`Q_owner>C_owner`.  Against that opponent, every complete behavioral
deviation of the owner is payoff-equivalent to its date-zero Quit/Continue
mixture: no later live history exists.  The prescribed owner already Quits
surely, so its payoff equals its unrestricted behavioral cap and its debt is
zero.  This contradicts the producer's `owner_gap>=Gamma>0` field.

Thus robust strict positivity fails.  Negation gives `Delta<=0`.  The witness
background is not empty because the collision-map field gives
`Delta(e,f(e);empty)>=Gamma>0`.  In Fin4 its cardinality is therefore one or
two, exactly as the packet says.

This proof genuinely handles arbitrary behavioral owner deviations, not only
stationary deviations.

## 5. Boundary and source audit

The weak sign is sharp for the proof: a zero background increment stops the
strict sure-quitting propagation, so no negative margin follows.  Two-,
three-, and four-cycle propagation all use the same single source; a
one-cycle is excluded by fixed-point freeness.  The reward bound and `M>=0`
are needed by the current producer even though they are not spent in the
short contradiction.

The cited current declarations match their use:

- the fixed-point-free terminal-gap collision map;
- the singleton-base same-law reset producer and `owner_gap`;
- the persistent-base root and free-player Nash inequalities; and
- the stationary endpoint/face conventions.

A narrow source search found no existing nonempty-background cancellation
theorem, so the ordinary-mathematics composition is novel.  The unused reset,
atom, minimum, and dispatch fields are correctly identified as unused.

The boundary section would benefit from an explicit small reward-table
example attaining `Delta=0`, but this is not the reason for the removal
verdict.

## 6. Export-gate failure

The output is only one weak nonsingleton reward inequality.  As the packet's
own adapter/consumer and scope sections state:

- the cancelling background need not have positive probability at another
  actual source;
- no stationary equilibrium or interior sign box is produced;
- no Bellman edge, floor path, paid source, return, or debt descent is
  produced; and
- no current checked semantic compiler consumes the weak cancellation.

The active question bank explicitly says that a finer case split or proper
semialgebraic subset is not export progress unless it eliminates a named live
chamber or proves a declared well-founded complexity decrease.  The packet
names a “naive boundary-face Poincare--Miranda producer,” but that robust
all-background-positive subclass is not a maintained chamber or an accepted
answer in `questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.  The live
hard residual remains present, and the packet supplies no consumer for its
new sign.

Therefore mandatory gate item 4 and the “What qualifies” section fail.  No
wording repair can fix that mathematical boundary.  The theorem should remain
as a reviewed internal result and can return to `exports/` only when composed
with an actual source/consumer, a named chamber elimination, or a maintained
well-founded reduction.

## 7. Lean handoff status

The proposed Lean decomposition is mathematically sensible and noncircular,
but export removal means it is not presently an external-formalization
target.  Retaining the handoff in the internal note is appropriate for a
future consuming composition.
