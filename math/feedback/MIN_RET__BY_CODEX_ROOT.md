# Review of `MIN_RET.md`

Reviewer: `CODEX_ROOT`

## Verdict

The bounded-payoff argument is correct under the additional recursive
compatibility hypothesis invented in Section 1.  That hypothesis is not part
of `FinFourOwnerCompressedMinimumReturnForcedPairPacket` or of
`questions/FIN4_MINIMUM_RETURN_CAPSTONE.md`.  In fact it is incompatible with
the packet's sure nonsingleton pair rows: after installing the first pair row
in one chronology, play absorbs there whenever it is reached, so no later
stored row can retain positive reached mass in that same updated chronology.

Thus the note does not consume the minimum-return packet.  It proves only the
elementary conditional no-go that one player cannot receive a fixed positive
payoff increment infinitely often along one genuinely composable sequence of
behavioral profiles.

## Claim being reviewed

The note reads the question's pointwise statement

```text
every endpoint update preserves its own complete post-date tail and routes
its own marked mass without loss
```

as the much stronger recursive statement

```text
after updating frame n, the stored frame n+1 occurs literally inside the
updated profile with its original positive live mass and gain.
```

It then composes all updates on one profile, obtains a fixed payoff increase
for the same payer at every step, and contradicts bounded terminal rewards.

The implication from the first statement to the second is the missing step.

## What the checked packet actually provides

In
`Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`, a
`FinFourOwnerCompressedMinimumReturnForcedPairPacket` contains:

- one strict subsequence of separately constructed source frames;
- a fixed payer label on that subsequence;
- for each index, one forced-pair source profile and one paid endpoint target;
- pointwise exact own-debt subtraction and a fixed gain floor;
- pointwise equality of the forced and paid targets' post-date spine with that
  index's selected reference profile; and
- pointwise equality of routed stage mass with the source frame's live mass.

The declarations include `payerTargetDebt_eq_sourceDebt_sub_gain`,
`payerRoutedStageMass_eq_forcedPairStageMass`,
`forcedPair_postDateSpine_eq_reference`, and
`payerTarget_postDateSpine_eq_reference`.

There is no declaration identifying the paid target at index `n` with the
forced-pair source at index `n+1`, no update operation on the packet itself,
and no theorem that later marked roots or their reached masses survive an
earlier endpoint update.  The packet's `movingProfiles` are a sequence of
separately realized profiles, not successive states of one behavioral
chronology.

This is also explicit in the maintained question: it rejects “a horizontal
endpoint cycle called a chronology” and identifies cross-coordinate cap
circulation and renewable source reconstruction as the missing work.

## The immediate sure-absorption obstruction

At every forced-pair source frame, the marked root is a pure coalition of
cardinality two.  Conditional on reaching that row, absorption is certain.
This is the semantic reason the post-date tail can be retained literally
without being behaviorally reached.

Suppose the first local forced-pair update were installed at date `t_0` in a
single current profile.  Then the live mass at every later date is zero on
that profile.  Therefore a later frame at `t_1>t_0` cannot simultaneously be
the packet's next actual frame with marked stage mass at least
`lambda>0`.

So item 3 of Section 1 in `MIN_RET.md`—that routing identifies the next stored
frame inside the updated chronology—is not merely absent.  For the displayed
pure-pair construction it is precisely the chronological realization theorem
that fails.  “Routes marked mass without loss” means that one Boolean update
at a fixed date routes that date's cylinder mass.  It does not transport the
mass to a later source rank.

The same distinction is recorded by the pure-nonsingleton tail-screening
results: two sure quitters make the entire counterfactual continuation
semantically invisible under prescribed play and every unilateral deviation.

## Conditional headroom argument

If one separately assumes actual profiles `sigma^n` satisfying

```text
U_p(sigma^(n+1)) - U_p(sigma^n) >= c > 0
```

for one fixed player `p`, then the contradiction is valid.  Since the reward
table is finite and Never pays zero, `U_p` has a finite upper bound.  Hence

```text
U_p(sigma^N) >= U_p(sigma^0) + N*c
```

is impossible for large `N`.  A ceiling of normalized payoff headroom can be
used as a natural-valued rank.

The local identity behind one step is also correct: changing only player
`p`'s prescribed strategy leaves `p`'s unrestricted best-response cap
unchanged, so exact debt subtraction by the endpoint gain is exactly an
increase of `p`'s prescribed payoff.

But these facts apply only after the local paid comparisons have been
composed into successive whole profiles.  Constructing precisely that
composition is the open chronological producer; assuming it solves the hard
part of the question.

## Novelty and disposition

The note is useful as a concise falsification test for any future claim of an
iterated same-payer update stream: such a stream must terminate after finitely
many fixed-gain steps.  It also clarifies that a truly composable positive
gain stream would be stronger than a debt potential because bounded payoff
alone consumes it.

It does not add a new result about the actual minimum-return packet.  The
horizontal-versus-chronological distinction and the sure-pair screening
obstruction are already central maintained limitations.  The note should be
retained only as an internal conditional observation, not exported and not
reported as an inconsistency of
`FinFourOwnerCompressedMinimumReturnForcedPairPacket`.

## Exact remaining target

To turn this idea into an answer, one would have to produce from the existing
packet either:

1. a finite composable chain on which the same player's net prescribed payoff
   gains telescope before a sure-absorption barrier; or
2. an admissible multi-player return whose signed edge account survives the
   switches between the separately realized frames.

Neither follows from pointwise post-tail preservation or pointwise no-loss
stage routing.
