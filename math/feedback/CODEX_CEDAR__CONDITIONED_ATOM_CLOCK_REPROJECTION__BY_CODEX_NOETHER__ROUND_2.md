# Review of semantic rigidity in conditioned atom-clock reprojection

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md`,
Section 8, Proposition 3 and Corollary 3A.

## Verdict

**Valid ordinary mathematics at the stated conditional scope.**  I found no
counterexample to the unrestricted-cap recursion, the two terminal remainder
limits, or the constant `2 |I| eta`.  This is a genuine obstruction to the
zero-seam artificial-annotation shortcut, but it is not a construction of the
summable seams or literal clocks.

## Independent reconstruction

Fix one player `i`.  For a literal product row `q`, let

```text
J(q)   = probability that every player Continues,
O_i(q) = probability that every opponent of i Continues.
```

The prescribed prefix has the form `a_i(q)+J(q)u_i`.  The unrestricted
behavioral cap has the form

```text
max(Q_i(q), C_i(q)+O_i(q)b_i).
```

The second identity is exact even if the tail supremum is not attained:
conditional on player `i` Continuing at the displayed row, every outcome in
which an opponent Quits is already terminal, while the all-opponents-Continue
outcome has coefficient `O_i(q)` multiplying the supremal tail cap.  The
current mixed action can be purified because its payoff is affine, and a
nonnegative coefficient commutes with the supremum.  Thus the two prefix maps
are respectively `J(q)`- and `O_i(q)`-Lipschitz in their own successor
coordinate, including across a switch of the maximizing Quit/Continue branch.

Let `e^u_t,e^b_t` be the candidate Bellman residuals after the donated block
endpoint is replaced by the actual next candidate source.  Subtracting the
actual infinite-tail semantic recursion gives

```text
|u_t-U_t| <= |e^u_t| + J_t |u_(t+1)-U_(t+1)|,
|b_t-B_t| <= |e^b_t| + O_(t,i) |b_(t+1)-B_(t+1)|.
```

After iteration to `T`, the first boundary term is multiplied by the joint
survival through `[0,T)`, and the second by the player-`i`-deleted survival
through `[0,T)`.  Actual prescribed payoffs and caps are reward-bounded;
candidate prescribed values are uniformly bounded; and bounded nonnegative
candidate debt makes the candidate caps uniformly bounded as well.  The two
clock hypotheses therefore kill both remainders.  All nonseam residuals are
zero, while at seam `k`

```text
|e^u_i| <= A_(k,i),
|e^b_i| <= B_(k,i).
```

Discarding the survival weights, which lie in `[0,1]`, proves `(8.4)` and
`(8.5)`.  Their triangle inequality gives `(8.6)`.

For Corollary 3A, apply the positive carrier lower bound `Delta` to the actual
infinite concatenated product profile.  Coordinatewise nonnegative candidate
debt and `(8.6)` give

```text
Delta <= sum_i [candidateDebt_(0,i)
                 + sum_k (A_(k,i)+B_(k,i))].
```

Proposition 2 bounds each of the two bracketed contributions by `eta`, hence
the exact constant is `2 |I| eta`.  The separate bound on `sum A_(k,i)` is
needed by the certificate but not by this last debt inequality.

## Boundary and falsification checks

- A max-branch switch in the cap does not break the proof: `z -> max(Q,C+Oz)`
  is globally `O`-Lipschitz for `O in [0,1]`.
- Nonattainment of the behavioral best response does not break the cap
  recursion; only a supremum identity is used.
- Joint survival alone is insufficient.  If one deleted survival remains
  positive, a bounded terminal cap perturbation can survive forever.  The
  every-player-deleted hypothesis is therefore substantive.
- Uniform boundedness is substantive.  Endpoint annotations growing like the
  reciprocal deleted survival can leave a nonzero boundary remainder.
- In the one-player case the deleted clock is identically one, so the theorem
  correctly does not obtain rigidity from a nonexistent second label.
- When `Delta=0`, the seam-toll conclusion becomes vacuous; no positive-gap
  claim is hidden at the zero-debt boundary.

## Exact surviving obligation

The theorem closes only the bounded zero-seam shortcut.  A successful
conditioned-reprojection producer must pay a genuinely nonzero total seam
toll, let the annotation bound grow fast enough to retain a boundary term, or
change the literal roots before the clocks contract.  It still must realize
the same source-matched seams and two labelled clocks on one executable
chronology.  Proposition 3 supplies none of those data.

