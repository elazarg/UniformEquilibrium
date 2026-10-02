# Review of the pre-mark absorption floor

## Claim checked

For a bounded quitting game, an actual profile \(\pi\), a player \(i\), and
a mark \(m\), suppose the whole-profile cap is within \(\sigma\) of the
singleton payoff while the cap of the post-mark all-Continue spine exceeds
that singleton payoff by \(\gamma>0\). If \(P^{-i}\) is the product, through
the mark, of the opponents-of-\(i\) all-Continue probabilities, then

\[
P^{-i}\le \frac{2M+\sigma}{2M+\gamma}.
\]

## Verdict

The theorem and its proof are sound. The one-step Continue-arm lower bound is
valid for unrestricted behavioral caps, the affine maps telescope exactly,
and the final use of \(|r_i(\{i\})|\le M\) gives the stated constant. The
scratch Lean theorem states this actual-profile result directly and does not
hide a stationary-response restriction.

This is useful new quantitative localization: approximate tightness at the
whole profile and a strict post-mark cap margin force a fixed amount of
opponent absorption before the mark. It rules out hiding the entire cap rise
behind an almost surely surviving pre-mark word.

## Necessary scope correction

The last consequence in the note currently calls this “exactly the
uniform-absorption currency that capacity compilers consume.” That is not yet
justified for the strict-inert normalized-return source.

The actualizers approaching the normalized point are obtained from the
closure of an arbitrary prefix orbit. Their stored prefix words are arbitrary
product roots. The actualizer records convergence, marked mass, and paid gain,
but it does not record that these roots are exact Nash--Bellman edges. The
post-mark spine is literal, but exactness of the pre-mark word does not follow
from that equality.

By contrast, finite exact-block hazard capacity ranges only over words whose
every displayed root is an exact one-stage Nash root against its displayed
successor and whose payoffs satisfy the Bellman recursion. Therefore the new
floor cannot presently be inserted into the bounded-capacity contradiction.

The correct current conclusion is:

> the strict-inert approximants carry a fixed pre-mark opponent-absorption
> floor in their actual, possibly non-Nash, prefix words.

## Concrete follow-up

Prove one of the following bridges.

1. Replace or exactify the arbitrary pre-mark word by an exact Nash--Bellman
   word while preserving a fixed fraction of the opponent-absorption floor,
   the marked pair, and the post-mark source passport.
2. Give a chronological consumer that uses the actual-profile absorption
   floor directly, without passing through exact-block capacity.
3. Show that the failure of such an exactification has a normalized defect
   bounded below and route that defect to an existing paid-return, support,
   or persistent-clock consumer.

Until one of these is proved, the result is a genuine local theorem and a
promising source-side constraint, but not a strict-inert branch consumer.
