# Review of recentered-tail anchored ray or cap-cross rectangle

Reviewer: CODEX_SPINOZA

Reviewed artifact:
`notes/CODEX_HAHN__RECENTERED_TAIL_ANCHORED_RAY_OR_CAP_CROSS_RECTANGLE.md`,
exact SHA256
`57773aacb4f2b66b37dfd72eea92d9e033c1c4d589a771845b4a9661bca59125`.

## Verdict

**PASS.**  The theorem is a real contraction of the recentered paid-tail
branch.  It is not merely a relabeling of the generic shifted-ray/rectangle
dichotomy: the maintained old finite-clock anchor is what makes the target
debtor's unrestricted cap attainable and what excludes the anchor as the
unique-sure debtor throughout the exact-prefix genealogy.  The rectangle arm
retains one literal source and commuting two-player updates with the stated
sign.  It remains a reduction, not a terminal consumer.

## Reconstruction

At the source \(X_n\), the paid \(k\)-edge gives
\(d_k(X_n)\ge g_0>0\), while the finite-clock owner \(a\) has
\(d_a(X_n)=0\).  Hence \(a\ne k\), and changing only \(k\) leaves \(a\)'s
prescribed finite stopping clock literally unchanged at \(Z_n\).

In the subcritical branch, exact-prefix debt monotonicity has the correct
orientation:

\[
 d_a(q::P)\le d_a(P)<\Gamma/2.
\]

The uniform Fin4 exact-block capacity applied to every finite initial segment
of the recursively constructed literal ray makes the entire marginal-hazard
series finite.  Thus only finitely many roots have zero joint survival.  If a
zero-survival root has two sure quitters, a unilateral deviator still leaves
one sure opponent at the current row; exact product-root Nash then covers the
remaining current Boolean comparison and gives unrestricted terminal Nash.

If a zero-survival root has a unique sure quitter \(\ell\), all other child
debts vanish.  The terminal gap forces \(d_\ell\ge\Gamma\), whereas the
displayed anchor bound is below \(\Gamma/2\); therefore \(\ell\ne a\).  The
unchanged prescribed finite clock of \(a\) forces absorption under every
deviation of \(\ell\), so pure-time extremality reduces \(\ell\)'s cap to a
finite menu (with Never represented separately or by a later equivalent
finite time).  At the unique-sure child the current Quit endpoint is the
prescribed payoff, so positive debt forces the cap onto Continue followed by
the attained tail cap.  This validates the backprojection and clock shift.

If no zero-survival root exists, the gap debtor at \(Z_n\) is again distinct
from \(a\), because \(d_a(Z_n)<\Gamma/2<\Gamma\), and the same finite anchor
attains its cap.  Beyond the last zero root, positive joint survival gives
positive Continue support for the debtor.  Exact root Nash plus the positive
tail debt makes Continue-then-cap the strict cap branch, yielding

\[
 d_\ell(P^{m+1})=s_{m,\ell}d_\ell(P^m).
\]

Finite total marginal hazard makes the product of the opponent-Continue
factors strictly positive, so the debt floor persists along that one ray.
The note correctly allows every constant and selected label here to depend on
the outer index \(n\).

In the supercritical branch, a pure-time/Never response within \(\Gamma/4\)
of the target cap has gain strictly above \(\Gamma/4\).  Zero source debt for
\(a\) makes the same response's source gain nonpositive.  Since \(a\ne k\),
the updates commute literally, and target gain minus source gain is the
positive cross-difference in (9).  The signs are correct and no cap
attainment at \(Z_n\) is assumed.

## Counterexample attempts and boundaries

- Changing \(k\) can make \(a\)'s debt positive and can destroy its old cap
  optimality, but it cannot alter \(a\)'s prescribed stopping law.  The proof
  uses only that surviving clock for cap attainment, so this does not break
  Alternative A.
- If the anchor were the debtor itself, replacing it could expose an
  unbounded tail and cap attainment could fail.  The strict
  \(d_a<\Gamma/2\) bound excludes precisely that case both initially and at a
  unique-sure child.
- The finite-hazard argument is applied to a literal nested exact-prefix ray,
  not to the horizontal rectangle.  It therefore has the required canonical
  Nash--Bellman orientation.
- Alternative B is not chronological and supplies no accepted block.  The
  note says this explicitly; generic cap-switch regressions prevent promoting
  it to a return without extra structure.

## Conjecture-facing assessment

Alternative A genuinely renews an exact shifted-cap source at the actual
recentered target and eliminates cap nonattainment/source-provenance there.
Alternative B narrows failure to a fixed source-matched two-label cap cross
rectangle attached to the original paid \(k\)-edge.  The remaining work is
therefore the rectangle consumer, not reconstruction of the tail source.

## Exact-hash source-path delta

The repaired note has exact SHA256
`3a513e6d5894af703ac7dd156217634fc906e92cb41f1ea37b87b8238f0fe0b1`.
The sole repair replaces the nonexistent capacity source with the actual
generic `UnboundedExactBlockHazardCapacity.lean` path and its Fin4 wrapper
`FinFourUnboundedExactBlockHazardCapacity.lean`.  The theorem and proof are
unchanged; links, documentation checks, and control-byte scan are clean.
**PASS** for this exact hash.
