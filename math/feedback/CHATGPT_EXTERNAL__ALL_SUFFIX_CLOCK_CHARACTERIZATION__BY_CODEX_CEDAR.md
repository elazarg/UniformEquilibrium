# Incremental review of all-suffix clock characterizations by `CODEX_CEDAR`

Reviewed note:
[`CHATGPT_EXTERNAL__ALL_SUFFIX_CLOCK_CHARACTERIZATION.md`](../notes/CHATGPT_EXTERNAL__ALL_SUFFIX_CLOCK_CHARACTERIZATION.md).

## Verdict

The arbitrary-deleted-set rule, the four-player calculation, and the actual
packet-boundary charge criterion are valid ordinary mathematics with the
qualifications below.

Only the packet-boundary criterion is a materially new interface beyond the
existing formalized two-label packet.  The one-player-deleted all-suffix
equivalence and joint-survival consequence proposed in Section 5 are already
proved by
`all_opponentClocks_iff_all_suffix_survival_zero` and
`tendsto_jointSurvival_zero_of_opponentSurvival_zero`
(`UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`).
The literal four-player regression is already proved, including its
pair-deleted failure, in
`QuittingHarmonicGreenRegression`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPointwiseDefectGreenRegression.lean`).

The packet-boundary criterion is a useful independent formalization target:
it lets an actual block producer verify the chronological consumer's deleted
clocks from block absorption probabilities without first extracting two fixed
labels.  It does not solve conditioned moving-source construction, small
initial debt, or the other chronological certificate fields.  I therefore do
not recommend reopening or extending the read-only formalized packet solely
for these additions.

I did not run Lean and claim no new checked declaration.

## 1. Arbitrary deleted sets

Let `A` be any subset of the finite player set and put

```text
h(-A,t)=1-product_(j notin A)(1-p(t,j)).
```

For every `j notin A`, event inclusion and the finite union bound give

```text
p(t,j) <= h(-A,t) <= sum_(k notin A) p(t,k).          (1.1)
```

Consequently the nonnegative series `sum_t h(-A,t)` diverges exactly when at
least one nondeleted marginal series diverges.  Applying the scalar
all-suffix product dichotomy gives

```text
forall m, J(-A,m,N) -> 0
  iff
P \ A is nonempty.                                   (1.2)
```

This includes the empty complement: if `A` is the whole player set, the
stage charge is zero and survival is identically one.  For deletion of every
set of cardinality at most `d`, the finite-set reformulation is that no such
deleted set contains all persistent labels; when such `d`-sets exist, a
sufficient and sharp cardinal form is `|P|>=d+1`.

For singleton `A={i}`, requiring (1.2) for every `i` is exactly the already
formalized two-persistent-label theorem.  Larger deleted sets are not fields
of `QuittingChronologicalDebtShadowingCertificate`, so the generalization is
correct but does not strengthen that named consumer.

## 2. Four-player regression

For `a_t=1/(t+2)`, telescoping gives

```text
product_(t=m)^(m+N-1) (1-a_t)
  = product_(t=m)^(m+N-1) (t+1)/(t+2)
  = (m+1)/(m+N+1).
```

With active players `0,1` and inactive players `2,3`, joint survival is the
square of this expression.  Deleting one active player leaves one factor;
deleting one inactive player leaves two factors; deleting both active players
leaves the empty active product one.  Every displayed formula and limit in
Section 3 is therefore correct.

This exact example is already checked through
`activeOpponentSurvivalWeight`, `inactiveOpponentSurvivalWeight`,
`tendsto_opponentSurvivalWeight_zero`,
`tendsto_jointSurvivalWeight_zero`, and
`pairDeletedActiveSurvivalWeight` in the regression file named above.  The
literal shifted tail also has the tautological all-Continue residual shift and
exact semantic Prefix recursion.  That self-matching fact does not identify
the shifted tail with an independently donated atom/reset source.

## 3. Actual packet-boundary criterion

Assume strict finite boundaries

```text
0=N_0<N_1<N_2<...
```

and define the actual player-`i`-deleted packet charge `delta(k,-i)` as in the
note.  At a packet boundary `N_l`, deleted survival through packets
`l,...,l+K-1` is exactly

```text
product_(k=l)^(l+K-1) (1-delta(k,-i)).                (3.1)
```

The scalar every-suffix criterion applied to the sequence
`delta(k,-i) in [0,1]` shows that (3.1) tends to zero for every `l` exactly
when `sum_k delta(k,-i)=infinity`.  This includes isolated probability-one
packets correctly: one such packet kills earlier starts, but a finite number
of them does not kill suffixes starting after the last one and does not make
the series divergent.

For a calendar start lying strictly inside packet `l`, split its survival
into the remaining finite part of that packet and the product of all later
complete packets.  The first factor lies in `[0,1]`, so vanishing of the later
packet product proves vanishing from the interior start.  The reverse
implication follows by testing the boundary starts themselves.  No uniform
bound on packet widths is needed; strict integer boundaries already imply
that they tend to infinity.  Thus (4.1) is valid.

The displayed sufficient condition

```text
delta(k,-i) >= kappa*lambda_k
```

is valid provided `kappa>0`, `lambda_k>=0`, and `sum_k lambda_k=infinity`.
These nonnegativity hypotheses should be stated explicitly.  Most
importantly, `delta` must be computed from the roots actually concatenated,
as the note says; nominal packet charges do not transport automatically.

## 4. Relation to Cedar Proposition 6

Proposition 6 of
[`CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md`](../notes/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md)
concatenates literal finite root lists.  Once those actual roots are fixed,
the packet charges above are literal probabilities of opponent absorption in
each concatenated block.  Hence divergence of every actual deleted packet-
charge series verifies exactly the every-suffix opponent-survival fields of
the resulting chronology.  Any one such deleted survival also dominates and
therefore supplies joint survival.

This is an alternative verification route to Proposition 6's two-labelled
marginal-hazard hypothesis, not a consequence of independently selected
source packets.  It can be strictly more convenient when a construction
controls total block absorption but the active labels vary across blocks.
It still leaves Proposition 6's decisive residual unchanged: for the
`exactOfRoots` construction, one must bound the actual initial terminal debt;
for the nonexact candidate construction, one must additionally produce the
candidate Bellman/seam/forcing data.  Packet-charge divergence supplies none
of those estimates.

## 5. Export and formalization recommendation

- Do not duplicate Section 5's proposed one-player equivalence or joint
  implication; the named declarations already check them.
- Do not present the four-player example as new; the exact regression and its
  pair-deleted boundary are already checked.
- The arbitrary-set rule is a clean general lemma, but it is outside the
  current consumer's one-player-deleted scope.
- Preserve the actual packet-boundary equivalence as a separate narrow Lean
  handoff if a block producer needs it.  Its theorem should quantify strict
  finite boundaries, actual roots, arbitrary calendar starts, and the
  probability-one boundary explicitly.

These additions are not enough to revise the existing formalized reduction:
they improve how a supplied actual chronology can verify its clock fields,
but do not change the live conditioned-packet producer obstruction.
