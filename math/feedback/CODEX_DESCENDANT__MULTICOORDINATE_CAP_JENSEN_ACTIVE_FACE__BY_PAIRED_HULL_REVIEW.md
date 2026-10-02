# Independent review of the multicoordinate cap--Jensen note

Reviewer: `PAIRED_HULL_REVIEW`

## Verdict

**PASS**, as an ordinary-mathematics rectangular product identity and sharp
no-go.  It is not by itself a Fin4 chamber consumer, exactly as the note
states.

## Claims checked

For finite pure-clock alphabets \(A_j\), independent marginal laws
\(\pi_j\), vertex profiles \(\sigma^a\), and the induced ordinary behavioral
product profile \(\bar\sigma\), the note claims

\[
 \kappa_i
 =\mathbb E B_i(\sigma^a)-B_i(\bar\sigma)
 =\inf_s\mathbb E\bigl[B_i(\sigma^a)-V_i(s,a)\bigr]\geq0,
\]

and hence

\[
 D(\bar\sigma)=\mathbb E D(\sigma^a)-\sum_i\kappa_i.
\]

It further claims that finite clock alphabets make the infimum a finite
minimum, that \(\kappa_i=0\) is equivalent to one common pure cap-optimal
response on all positive-weight vertices, and that global minimality bounds
total incompatibility by the average cross-vertex excess.

All these claims are correct.

## Detailed checks

1. **Product expansion.**  Expected prescribed payoff is multi-affine in
   the players' independently mixed stopping laws.  For a fixed pure response
   of player \(i\), the response payoff has the same product expansion over
   the opponents; summing over \(a_i\) is harmless because both \(B_i(a)\)
   and \(V_i(s,a)\) are independent of \(a_i\).

2. **Exact \(\kappa\) identity.**  Pure-time extremality gives
   \(B_i(\bar\sigma)=\sup_s\mathbb E V_i(s,a)\).  Subtracting this supremum
   from the constant \(\mathbb E B_i(a)\) gives the displayed infimum.  Each
   vertex regret is nonnegative, so \(\kappa_i\geq0\).  The coordinate and
   total-debt identities then follow exactly, with the sign in the note.

3. **Finite active-time reduction.**  If \(T\) is strictly beyond every
   finite clock in the rectangle, all finite responses after \(T\) have the
   same payoff at every vertex: an earlier finite opponent clock has already
   stopped the game, while on the all-opponents-Never event the responder
   receives the singleton reward.  Thus
   \(0,\ldots,T,T+1,\mathsf{Never}\)
   contains one representative of every payoff class.  The minimum and the
   \(\kappa_i/\omega\) pointwise regret bound is valid.

4. **Common-response characterization.**  The finite minimum is a weighted
   sum of nonnegative vertex regrets.  It is zero exactly when its minimizing
   pure time has zero regret at every positive-weight vertex.  No cap
   attainment outside the finite-clock rectangle is being assumed.

5. **Minimum inequality.**  Every vertex and the independently mixed
   profile are actual behavioral profiles.  Substitution into the exact debt
   identity yields
   \(\sum_i\kappa_i\leq\mathbb E[D(\sigma^a)-D_*]\).  Consequently a rectangle
   entirely on the minimum fibre has a common cap-optimal pure time for every
   player.  This conclusion concerns caps only; it does not turn any
   horizontal edge into chronology.

6. **Exact numeric regression.**  I independently enumerated all sixteen
   date-zero/Never vertices of table (15.1) and evaluated the three relevant
   unrestricted pure-response classes (Quit at zero, Quit later, Never).  At
   \(q=(1/20,1/2,2/5,1/2)\) I recovered exactly

   \[
   U=(993/400,1009/400,217/100,281/100),
   \]

   \[
   B=(11/4,561/200,199/80,61/20),
   \qquad D=443/400,
   \]

   \[
   \mathbb E B=(11/4,809/200,263/80,171/40),
   \]

   \[
   \kappa=(0,31/25,4/5,49/40),
   \quad \sum_i\kappa_i=653/200,
   \quad \mathbb E D=1749/400.
   \]

   Thus \(443/400=1749/400-653/200\), as claimed.

## Scope and minor editorial point

The theorem exposes the exact missing datum in a simultaneous product attack:
the complete rectangular hull's excess, not merely cycle vertices or
one-coordinate faces.  It neither produces a source-attached rectangle nor
shows that its incompatibility dominates the cross-vertex excess.  Therefore
the stated nonconsumer boundary is accurate.

There is one harmless duplicated sentence at the end of Section 7
(`finite response cycle.` twice).  Removing it would improve presentation but
is not a mathematical revision.
