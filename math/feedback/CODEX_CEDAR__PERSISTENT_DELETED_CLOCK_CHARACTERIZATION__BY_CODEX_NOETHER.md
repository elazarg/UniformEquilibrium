# Feedback on Persistent Deleted-Clock Characterization

Reviewer: `CODEX_NOETHER`

Reviewed note:
[`../notes/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md`](../notes/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md)

Scope: Propositions 1--2 only.  I independently checked the exact individual,
opponent-deleted, and joint clock labels; suffix quantifiers; isolated sure-
Quit factors; one- and two-player boundaries; the summable-error and fixed-
fraction adapters; and the pointwise-error falsifier.  This is ordinary
mathematics, not a Lean check.

## Verdict

**Propositions 1--2 are VALID ordinary mathematics.**  The characterization
is exact: every one-player-deleted survival dies on every suffix if and only
if at least two distinct individual marginal hazard series diverge.  The
joint-survival field then follows and is redundant.  The robust two-anchor
adapter has the stated summable-error and fixed-fraction quantifiers.  I found
no counterexample or label mismatch.

## 1. Additive clock equivalence

For fixed deleted player `i`, let

```text
c_(t,-i)=1-product_(j ne i)(1-p_(t,j)).
```

For every `j ne i`, event inclusion and the finite union bound give

```text
p_(t,j)<=c_(t,-i)<=sum_(j ne i)p_(t,j).
```

All terms are nonnegative and the player set is finite.  Therefore
`sum_t c_(t,-i)<infinity` exactly when every individual series with label
`j ne i` is summable.  Thus every deleted charge is nonsummable exactly when
deleting any one label leaves a persistent label.  On a finite set this is
equivalent to the existence of at least two distinct persistent players.

This includes `|I|=2`: both individual hazard series must diverge, because
each deleted clock is literally the other player's clock.  For `|I|=1`, the
deleted factor is the empty product one, so the opponent survival never dies;
the note correctly excludes this case from the equivalence and records it as
a boundary.

## 2. Multiplicative survival and isolated sure exits

A nonsummable nonnegative opponent-charge series remains nonsummable after
deleting any finite prefix, so
`tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge`
(`UniformEquilibrium/Quitting/Paths/OpponentClockDichotomy.lean`)
applies at every suffix.

Conversely, if the charge is summable, it can contain only finitely many
terms equal to one.  After their last occurrence one may choose a suffix with
small total remaining charge; the checked
`exists_suffix_half_le_quittingOpponentSurvivalWeight_of_summable` then gives
a suffix whose every finite survival is at least one half.  Hence a single
sure-Quit factor can kill an earlier product but cannot fake the required
every-suffix conclusion.  This checks the difficult zero-factor boundary in
the printed `2 iff 3` argument.

The one-row joint Continue factor is no larger than the corresponding factor
after deleting any player.  Once every deleted survival tends to zero, the
joint product does as well.  The converse fails exactly as printed: one
persistent owner and every other hazard zero kills joint survival, but the
clock obtained by deleting that owner is identically one.

## 3. Robust reprojection adapter

For either anchor `j` and every finite collection of blocks,

```text
sum_actual p_(t,j)
  >=sum_nominal bar_p_(t,j)-sum |p_(t,j)-bar_p_(t,j)|.
```

If the nominal partial sums diverge while the total absolute error is finite,
the actual partial sums diverge.  Applying this independently to the two
distinct labels `a,b` supplies Proposition 1.  No simultaneous activity is
used, so alternating anchor packets are allowed.  Under
`p_(t,j)>=theta*bar_p_(t,j)` with one fixed `theta>0`, the same conclusion is
immediate without an error budget.

The pointwise-error warning is sharp.  The printed one-anchor example already
shows that `|p-bar_p|->0` does not preserve a divergent label.  If a literal
two-anchor version is desired, use the same `1/(t+2)` nominal hazards for two
distinct anchors and set both actual hazards to zero; both pointwise errors
vanish while both required persistent labels disappear.  This is only a
presentational strengthening, not an objection.

## Exact scope

The result completely answers the abstract clock question in
`questions/PERSISTENT_DELETED_CLOCKS.md`, but it does not produce two labels
from the actual moving-source packets.  The remaining conjecture-facing datum
is exactly as stated in the note: retain divergent nominal incidence for two
distinct owners while making the total marginal reprojection loss summable,
or preserve a fixed fraction.  Prescribed/direct forcing, source matching,
and small initial debt remain separate consumer fields.

