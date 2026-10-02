# Review of persistent two-label amplification from finite packet words

Reviewer: `CODEX_NOETHER`

Reviewed note:
`notes/CHATGPT_EXTERNAL__PERSISTENT_LABEL_AMPLIFICATION.md`.

## Verdict

**The theorem is valid as a survival-only statement after adding the usual
nonempty-player hypothesis (equivalently, state `|I|>=2`).**  Its application
to the frozen radial exposure words is valid.  Literal repetition is a legal
root chronology and preserves the roots and their clocks, but it preserves no
frozen semantic source, atom orientation, debt, or forcing datum.

The result does not remove a live producer obligation.  Its mathematics is
already present in Cedar's persistent-clock Proposition 1 and Proposition 6,
and the frozen-radial application is already the exposure-over-restart
amplification in Section 3 of
`notes/CODEX_CEDAR__RADIAL_PACKET_AMPLIFICATION.md`.  It is a concise
repackaging, not a new source adapter.

## 1. Strict deleted survival really gives two labels

For a finite word `W`, let `A(W)` be the players with positive total marginal
Quit hazard in the word.  If `A(W)=empty`, every deleted survival equals one.
If `A(W)={c}`, deleting `c` leaves only zero-hazard players, so
`S_(-c)(W)=1`.  Hence the strict inequality for every deletion implies
`|A(W)|>=2`.

There is one boundary omission.  If `I` is empty, the deletion hypothesis is
vacuous but the conclusion demanding two distinct labels is false.  For one
player the hypothesis is impossible because the sole deleted survival is the
empty product one.  Thus `Nonempty I` suffices logically, and the clean
statement is `|I|>=2`, which the hypothesis then proves automatically.

Because only finitely many unordered pairs exist, infinitely many available
late words have a subsequence with one fixed pair `{a,b}`.  Any eventual
rank condition survives this subsequence.  No quantitative lower bound on the
two hazards is needed.

## 2. Repetition and every-suffix divergence

For selected word `W_k`, put

```text
h_k=min(H_k(a),H_k(b))>0
```

and choose the integer `R_k=ceil(1/h_k)`.  Repeating `W_k` exactly `R_k`
times contributes at least one unit of marginal hazard to each fixed label.
Concatenating the repeated epochs makes both marginal series divergent.
Removing any finite prefix preserves divergence.

For every deleted player, at least one of `a,b` remains, and the corresponding
survival product is bounded above by that label's product of `(1-q_t)`.  A
divergent nonnegative hazard series makes this product vanish; an isolated
factor `q_t=1` makes it vanish immediately.  Therefore all player-deleted and
joint survivals vanish from every suffix.  The proof covers arbitrarily tiny
positive hazards because the repetition count is allowed to grow.

## 3. Literal chronology versus semantic provenance

Any countable sequence of product roots is a literal behavioral chronology.
Replacing a selected word's old continuation by the later concatenated words
does not change any root or marginal hazard in that word.  Thus nominal and
actual clocks agree pointwise, giving zero clock reprojection error and
retention fraction one.

The reached prescribed payoff and unrestricted cap do change with the new
continuation.  They obey the exact actual-tail prefix recursion, but they need
not equal the frozen radial semantic annotations.  Repeating a word may also
destroy its terminal atom label, reset comparison, low-debt estimate, or
one-sided forcing sign.  Calling this clock fact “literal source matching” is
therefore potentially misleading: it is literal **root** matching only.  The
note's explicit nonclaims correctly preserve this distinction.

## 4. Frozen radial applicability

The frozen radial exposure statement recorded in Cedar's radial note gives,
for every sufficiently large rank `n`, one common finite cutoff with

```text
1-S_(n,i) >= kappa*lambda_n >0
```

simultaneously for every deleted player.  Hence every such finite word
satisfies the external theorem's strict hypothesis.  In fact that source
already fixes two positive radial labels once and for all, so the subsequence
pigeonhole is unnecessary there.  Cedar Section 3 repeats each exposing block
enough times to obtain a uniform clock contraction per epoch, a quantitatively
stronger version of the same construction.

## 5. Novelty and exact remaining gap

- The finite-word “at least two positive labels” argument is the finite
  specialization of Cedar Persistent-Clock Proposition 1.
- Fixed-pair selection, literal concatenation, actual reached-tail recursion,
  zero local defects for the actual semantic datum, and the surviving small-
  initial-debt gap are already Cedar Persistent-Clock Proposition 6.
- Repeating frozen radial exposure blocks is already Cedar Radial Packet
  Amplification Section 3.
- Cedar Conditioned-Reprojection Proposition 3 explains why adding bounded
  artificial annotations and vanishing clocks would already reconstruct
  actual small terminal exploitability.  Proposition 5 separately shows why
  the mover's own source/replacement toggle does not transport that debt for
  free.  The external theorem supplies neither missing semantic step.

Thus the exact surviving obligation is unchanged: attach small actual initial
debt, or a valid one-sided candidate forcing construction, to the literal
clock chronology on the same reached continuation.  The theorem answers only
the already-separated clock subproblem.

