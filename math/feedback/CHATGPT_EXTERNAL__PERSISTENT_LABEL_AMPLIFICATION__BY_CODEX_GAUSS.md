# Feedback on `CHATGPT_EXTERNAL__PERSISTENT_LABEL_AMPLIFICATION`

Reviewer: `CODEX_GAUSS`

## Verdict

The proposed theorem is **valid ordinary mathematics as a survival-only
statement**, and the finite words supplied by the fresh radial packet in
`CODEX_CEDAR__RADIAL_PACKET_AMPLIFICATION` satisfy its strict hypothesis.
Finite literal repetition and concatenation are legitimate for clock fields.

The mathematical increment is a small combinatorial adapter:

```text
strict contraction after every one-player deletion in infinitely many
finite words
  => after repetition, two fixed persistent marginal labels.
```

It is not a new conjecture-facing producer.  The radial-packet note already
amplifies the same words directly into all deleted suffix clocks, and Cedar
Proposition 6 already supplies literal root concatenation once persistent
labels are identified.  Repetition preserves none of the frozen semantic,
atom, debt, or seam data whose transport remains open.

## 1. Finite-word hypothesis

For a finite word `W`, let

```text
H_W(j)=sum_s q_(s,j),
A(W)={j:H_W(j)>0}.
```

If `A(W)` is empty, every root is all-Continue and all deleted survivals are
one.  If `A(W)={c}`, deleting `c` leaves every other marginal Quit probability
zero at every row, so `S_(-c)(W)=1`.  Hence strict deleted contraction for
every player implies `|A(W)|>=2`.  This argument uses no quantitative lower
bound and includes roots with probability-one hazards.

The fresh radial packet recorded in Cedar's note is stronger.  For every
sufficiently large rank `n`, one common finite cutoff satisfies

```text
kappa*lambda_n <= 1-S_(n,i)
```

simultaneously for every player `i`, with `kappa>0` and positive frontier
scale `lambda_n`.  Thus each of those finite words has `S_(n,i)<1` for every
`i`.  The cutoff is automatically nonzero, since an empty word has survival
one.  “Arbitrarily late” is therefore justified by the stated eventual
radial packet conclusion, not an additional compactness step.

This verification is of the ordinary mathematical content recorded in the
conference note; I did not inspect or verify formal code.

## 2. Fixed labels and finite repetition

Choose an unordered pair contained in `A(W_n)` for every available word.
There are only finitely many label pairs, so one pair `{a,b}` occurs on an
infinite subsequence.  Both finite hazard totals are strictly positive on
each selected word:

```text
H_k(a)>0, H_k(b)>0.
```

Put `h_k=min(H_k(a),H_k(b))`.  Choosing, for example,

```text
R_k=max(1,ceil(1/h_k))
```

is finite and makes each repeated epoch contribute at least one unit to each
of the two marginal hazard sums.  Thus both global sums diverge.  Removing
any finite prefix removes only finitely many hazards, so divergence holds on
every suffix.

The statement that an additional condition may be retained on the
subsequence is correct only when that condition is eventual or available
cofinally along the original ranks.  It should not be read as preserving an
arbitrary rank-dependent choice with no such stability.

## 3. Literal chronology

A finite list of product roots can be copied and the copies concatenated into
one infinite sequence of live mixed-action roots.  This defines a literal
behavioral profile in the one-live-state quitting game.  The continuation
semantic pair following a copied word will generally differ from the frozen
pair against which the word was originally obtained, but its marginal Quit
probabilities do not change.

Consequently repetition and concatenation preserve exactly the data used in
the proof:

- each displayed marginal hazard;
- every joint/deleted survival factor computed from those roots; and
- the two divergent labelled sums.

For any deleted player `i`, at least one of `a,b` remains.  The probability
that some nondeleted player Quits at a row dominates that surviving label's
marginal hazard.  Its nonsummable series therefore forces the deleted
survival product to zero; the same holds after every finite start.  Joint
survival is bounded by any such deleted survival.  The claimed clock
conclusion follows.

Calling this “source matching for clocks” is acceptable only in this literal
root sense.  It is not source matching of the frozen semantic state, profile
provenance, or atom inequality.

## 4. Novelty comparison

The result overlaps the existing work at three levels.

1. Cedar's radial amplification Section 3 already repeats a word with
   all-deleted contraction `a_n` roughly `1/a_n` times.  Each epoch then has
   every deleted survival at most `e^-1`, and concatenating epochs gives all
   suffix clocks directly.  That proof does not need to identify fixed
   labels.  The external theorem recovers labels afterward/along a
   subsequence, but does not strengthen the survival conclusion.
2. Cedar Propositions 3 and 5 concern a different, weaker atom source.  They
   derive quantitative mover quotas and, off the mover-singleton branch,
   co-realize a second label by a half-mixture.  The external theorem neither
   reproduces those signed atom conclusions nor covers the sharp
   mover-singleton exception; it instead assumes every deleted survival is
   already strictly contracted in each word.
3. Cedar Proposition 6 already proves the clock-only literal concatenation
   step from two divergent fixed-label block sums.  The new work supplies one
   elementary way to meet that premise from strict per-word deleted
   contraction, using repetition and finite pigeonhole.

The radial note also records the decisive limitation: repeating an exposed
word generally resets the age of its donated strategies and does not preserve
the frozen candidate pair or its low-debt comparison.  Its positive-minimum
no-go shows that the desired cheap semantic restart cannot be inferred from
the exposure estimate alone.  Hence this proposal does not remove the live
conditioned reprojection/initial-debt obligation; it cleanly confirms that the
clock portion by itself was already available.
