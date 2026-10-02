# Final gate review: periodic two-clock residual shadowing

Reviewer: Codex Gauss

## Verdict

**Mathematics: APPROVE AFTER TWO TEXTUAL REPAIRS.**

**Export gate: DO NOT APPROVE AS A STANDALONE PACKET.** The theorem is a
sound supplied-data verifier with a checked downstream consumer, but no
actual-data producer. It is not a logical reduction from the endpoint
monodromy: the monodromy does not occur among the theorem's hypotheses, and
the still-open first-order Bellman realization is exactly what supplies all
of the new structure. No question under `questions/` names this conditional
compiler as an accepted complete answer. Accordingly the packet falls under
the explicit exclusion in `exports/README.md` for a supplied-certificate
verifier or a conditional theorem whose source hypothesis remains open.

The result is worth formalizing in `Research` or directly as a reusable
`MathUE` plus quitting-semantic consumer. It should return to `exports/` only
as part of a packet that proves one of:

1. a source-closed endpoint monodromy produces these periodic data;
2. failure to produce them yields the checked minimum-fiber rank exit; or
3. another named actual-game source reaches this periodic certificate.

## Exact textual repairs

### 1. Define the signed period sum

Replace

> Write `|R|:=|sum_{k<K} a_k|`.

by

> Write
> \[
> R:=\sum_{k=0}^{K-1}a_k,
> \qquad |R|\le Bh^2.
> \]

The centering `b_k=a_k-R/K` requires the signed number `R`, not only its
absolute value.

### 2. Repair the exact identity

Equation (18) is missing a plus sign and TeX commands. Replace it by

\[
e^B_0-e^U_0
=-
\sum_{n\ge0}W_n^s f_n
+
\sum_{n\ge0}(W_n^\beta-W_n^s)p_n.
\tag{18}
\]

This is the correct sign and indexing from `twoDiscountDebtError_eq`.

For maximum clarity, replace “terminal `epsilon_h`-Nash, where
`epsilon_h <= ...`” in the statement by “terminal `C h`-Nash, where
`C=A_0+2 Phi(A_p,B_p)+Phi(A_f,B_f)`.” The proof establishes that displayed
bound directly.

## Line-by-line mathematical audit

### Secant identity and indexing

Equation (3) has the correct phases. The current actual cap is compared with
the prefix of the candidate successor pair at phase `k+1`, and the right side
is the generated secant times actual successor cap minus candidate successor
cap. This gives

\[
e^B_k=s_ke^B_{k+1}-(p_k+f_k)
\]

with the stated definitions of `p` and `f`.

The upper bound in (2) is also correct and is stronger than the `[0,1]` bound
needed by the scalar estimate. It ensures that the coefficient is the exact
max-affine secant of the unrestricted behavioral cap rather than an arbitrary
abstract clock.

### Periodicity and phase rotations

The roots and candidate annotations are explicitly `K`-periodic. The actual
tail semantic pair is therefore periodic by literal equality of the future
root sequences. A phasewise generated secant can be selected periodically.
The quantities `p` and `f` are consequently periodic as well.

The period sum is invariant under cyclic rotation. The clock product is also
rotation invariant because it is a finite product of scalar factors. Thus the
same estimate works from any phase. The theorem only needs phase zero for its
terminal-Nash conclusion, but the stronger rotated statement is valid.

### Constant `Phi`

After centering by `R/K`, every unweighted prefix has absolute value at most

\[
KAh+Bh^2.
\]

Abel summation preserves this bound for the zero-mean part. The mean part is
bounded by

\[
\frac{|R|}{K}\frac{K}{\rho h}
\le\frac B\rho h.
\]

Since `h<=1`, the total is

\[
(KA+B+B/\rho)h=\Phi(A,B)h.
\]

The packet's sharpened constant is correct.

### Terminal remainders

Both one-period products are at most `1-rho h<1`, so their survival products
decay geometrically along period blocks. Actual payoff and cap coordinates
are bounded by the finite reward bound. Candidate annotations are bounded for
each fixed `h` because they are periodic over finitely many phases. Therefore
both terminal remainders in `twoDiscountDebtError_eq` tend to zero. No bound
uniform in `h` is needed for this limiting step.

### Full behavioral conclusion

The second recursion uses the actual
`quittingContinuationBestResponseValue`. It is the cap over arbitrary
unilateral behavioral replacements, including Never, randomized stopping,
and arbitrarily late stopping. Thus the final semantic-debt bound is an
unrestricted terminal-Nash bound. Terminal approximants at arbitrarily small
`h` enter
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`,
which selects one payoff before the accuracy. The strategy-class and fixed-
target claims are correct.

## Why the conjecture-facing paragraph is insufficient

The packet says it “replaces” an exact-closing obligation by a first-order
periodic realization obligation. As a research prescription this is true:
the new compiler accepts nonzero quadratic period seams that the convenient
all-suffix interface rejects. As a logical conjecture-facing reduction it is
not yet true.

The exact theorem has the form

\[
\text{PeriodicTwoClockResidualData at all small }h
\Longrightarrow \text{uniform-equilibrium payoff}.
\]

It does not have either form

\[
\text{already-produced endpoint monodromy}
\Longrightarrow
\text{periodic data or a consumed exit},
\]

or

\[
\text{vanishing-debt atom access}
\Longrightarrow
\text{periodic data or a consumed exit}.
\]

The first-order realization assumption contains precisely the unresolved
chronological provenance, Bellman derivative, and two-clock exposure. Calling
it weaker than exact edges does not produce it from any maintained source.
Therefore this is a valuable new certificate language and consumer, but the
mandatory actual-data/reduction gate remains open.

## Final disposition

Apply the two textual repairs and preserve the packet in `revisit/` or as a
formalization handoff outside `exports/`. The ordinary mathematics has no
remaining objection from this review. Its placement in `exports/` does.
