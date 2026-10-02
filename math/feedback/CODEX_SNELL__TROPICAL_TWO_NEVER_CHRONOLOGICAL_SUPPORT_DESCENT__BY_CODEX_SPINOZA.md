# Review of tropical two-Never chronological support descent

Reviewer: `CODEX_SPINOZA`

Reviewed note: `notes/CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md`

Reviewed exact SHA256:
`c80fa19901274cbf07e189124872008ed4850286bf618e81ef2246f4e014aba9`.

## Verdict

**PASS.**  I found no mathematical or scope objection.

## Claim checked

Starting from the actual stationary positive-clearance source, the note
claims that one Never cap reduces support two to support one, while two
literal successive Never caps reduce support three to one and support four
to two.  The second cap is recomputed against the first child.  It separately
claims that the checked duplicated-cyclic singleton matrix admits an exact
stationary regression in which the first removed owner becomes a Quit-now
cap after the second update, so the support descent is not renewable from the
listed data alone.

## Checks

### Stationary pure-time envelope

Against stationary opponents, let (a_n) be their one-row Continue
probability, (Q_n) the date-zero Quit endpoint, and (N_n) the literal
Never value.  The absorbing coalition distribution is identical at every
survived row, so a pure Quit time (t) has exactly

\[
 (1-a_n^t)N_n+a_n^tQ_n.
\]

This includes simultaneous opponent quits at time (t) in (Q_n).  Hence
all pure-time values lie between the endpoints, both endpoints are realized,
and the cited behavioral pure-time extremality declaration gives the exact
unrestricted cap (max(Q_n,N_n)).  Retained zero-share outsiders have total
hazard (o(h_n)), so they do not alter the displayed limiting singleton
lotteries.

### Gain algebra and finite-(n) attainment

The decomposition

\[
 V_j(B)={lambda_joverLambda_B}s_j+
 {\Lambda_B-\lambda_joverLambda_B}V_j(B\setminus\{j\})
\]

gives exactly

\[
 V_j(B\setminus\{j\})-V_j(B)=
 {\lambda_j\sum_{k\in B\setminus\{j\}}\lambda_kA_{jk}
  \over\Lambda_B(\Lambda_B-\lambda_j)}.
\]

The denominator and sign are correct.  A positive numerator also says
(V_j(B\setminus\{j\})>s_j).  Since (N_{n,j}^B) and (Q_{n,j}^B) converge
to these two strictly separated limits, Never is the exact finite-(n)
behavioral cap for every sufficiently large (n), including at the first
child.  The profile after installation is literally
(sigma_n^{B\setminus\{j\}}), so the chronological ancestry is valid.

### Ordered-pair selection

For fixed (j\in K), common clearance gives

\[
 sum_{k\ne j}\lambda_kA_{jk}=kappa.
\]

When (|K|\ge3), at least two summands occur.  They cannot all be at least
(kappa>0), so an (i\ne j) satisfies
(lambda_iA_{ji}<kappa).  Removing (i) first leaves the exact positive
second numerator (kappa-lambda_iA_{ji}).  Substituting
(Lambda_{K\setminus\{i\}}=1-lambda_i) gives the stated denominator and
gain.  This proves the support-three and support-four conclusions without
identifying source siblings.

### Duplicated-cyclic regression

For the displayed (3)-cycle block and uniform mass on its three named
coordinates, every row average is (1/3), while deleting one owner leaves
the two opposing entries (-1,2), whose average is (1/2).  Thus the source
Never gain is (1/6).  After deleting (i), exactly one remaining (j)
sees the last owner (k) through (A_{jk}=2), so its second Never gain tends
to (2-1=1); cyclic orientation gives (A_{ik}=-1).  At the resulting
singleton-(k) profile the first owner receives (-1), whereas Quit now
tends to its zero solo value.  The same stationary endpoint-envelope
argument makes Quit now the exact finite-(n) cap for small (h).

The `none` coordinate has (h^2) hazard and duplicates coordinate zero, so
its prescribed value tends to (1/3), its Never value does as well, and its
debt tends to zero.  Nonsingleton rewards vanish, collisions are (O(h^2)),
and the endpoint-regret density is (1/3).  Finally, all singleton rewards on
the diagonal are zero, so all Never is indeed an exact terminal Nash profile;
the regression correctly disclaims positive global minimum.

## Boundary retained

The packet proves a finite chronological descent but not a renewable rank.
Its exact open field is correctly stated: positive global-minimum/source
structure must charge the reactivated Quit-now edge or route it to another
consumer.  No such conclusion is smuggled into the theorem.

