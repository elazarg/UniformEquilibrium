# Independent review of zero-Never singleton literal-tail renewal

Reviewer: `PAIRED_HULL_REVIEW`

## Verdict

**REVISE**, with a sound scalar/tail core and two source-typing
clarifications.  The persistent minimum-tail branch is a genuine literal
reached-suffix renewal.  It does not supply the source-coherent finite-deadline
Nash family needed by the full-debt projective route.

## Exact claims checked

### Marked-row factorization

The identity

\[
 N_n=L_nc_ne_n
\]

is correct with the note's definitions.  To realize Never, prescribed play
must reach the marked row with every opponent Continuing, player \(j\)'s old
coin must Continue, and the literal post-row tail must realize Never.
Behavioral independence at the unique live history multiplies these three
probabilities.  Since \(L_n>\lambda\) and \(N_n\to0\), the conclusion
\(c_ne_n\to0\) follows.  After first taking a convergent subsequence of
\(c_n\in[0,1]\), the stated split \(c_n\to0\) or
\(c_n\geq\varepsilon>0\)
is exhaustive.

### Invisible-compression arm

The total-variation, payoff, and cap bounds are correct.  Under an arbitrary
replacement by \(i\ne j\), the probability of reaching the row can change,
but the unchanged \(j\)-coin still disagrees with the sure-Quit target only
when its old outcome is Continue, with conditional probability \(c_n\).
For \(i=j\), the opponents are identical, so the cap is exactly identical.
Taking suprema over unrestricted responses preserves the \(2Mc_n\) bound.
Thus source and target have the same joint semantic/law limit.

### Reached-tail arm

If \(c_n\geq\varepsilon\), then \(e_n\to0\) and the literal transition into
the actual suffix \(T_n\) has probability at least
\(\lambda\varepsilon\).  Joint compactification of the exact suffixes is
legitimate; every cluster is in the joint carrier and has debt at least
\(D_*\).  Never mass is zero at every minimum cluster.  The strict/minimum
tail split is exhaustive after taking a cluster subsequence.

### Positive-singleton child

In the minimum-tail branch with a positive singleton atom,
`nonempty_sourceFaithfulMinimumCausalChronology` really does retain the
supplied profile sequence \(T_n\) and reselect only finite-window marks and
exact cap--Nash prefix words.  Together with the stated hard-residual and
finite-atom constructors, this supports a complete child producer based on
the literal suffix sequence.  The incoming transition's fixed reach floor is
an external fact about \(\Sigma_n\to T_n\); the fresh child prefix is not a
temporal continuation of the parent.  The note states that distinction.

## Required source-typing repairs

1. **Strict-tail port.**  The actual off-minimum port may be packaged with
   the suffix sequence \(T_n\) as its `original` sequence (identity ancestry
   to a selected strict suffix, followed by the actual-reach paid-row
   theorem).  The fixed-probability transition from \(\Sigma_n\) to \(T_n\)
   is a reached-suffix relation, not
   `IsQuittingBehaviorReplacementAncestry`.  The text should state these two
   provenance types separately rather than letting “ancestry from the
   original source” suggest the latter.

2. **Zero-singleton product-base exit.**  The closed-law theorem constructs a
   new finite product profile attaining the same semantic pair and law.  It
   does not make that profile the literal suffix \(T_n\), nor does it provide
   replacement ancestry from \(T_n\).  Applying finite-clock descent to the
   new profile gives a valid off-minimum paid port based at that new realizer,
   but not a source-faithful exit from the incoming literal-tail chain.  The
   boxed dispatch and Sections 5/7 must either record this provenance loss or
   supply a new bridge.  Equality of semantic pair and time-forgetting law is
   not such a bridge.

These are bounded statement repairs; they do not affect the factorization or
the positive-singleton literal-tail renewal.

## Relation to the full-debt projective route

The persistent branch does **not** produce coherent finite-deadline Nash
laws.  Each \(T_n\) is an arbitrary actual minimum-law suffix.  The
source-faithful causalization chooses exact cap--Nash prefix stacks separately
for each suffix/rank; it neither solves the hard finite timing game on
\(\{0,\ldots,H,\mathsf{Never}\}\) nor makes the next child an adjacent
calendar extension of the previous child.  Its newly selected mark may also
move.

Therefore this theorem supplies exactly what it claims at its sound core—a
renewable reached-suffix source—but it does not fill the finite-deadline
equilibrium-selection entrance isolated in
`notes/PAIRED_HULL_REVIEW__FULL_DEBT_ORTHOGONAL_PRODUCT_AND_PROJECTIVE_ATTACK.md`.
