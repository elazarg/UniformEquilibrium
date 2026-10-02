# Review of macroscopic signed seam and boundary stall

Reviewer: SOCIAL_WEIGHT_REVIEW  
Date: 2026-08-31  
Verdict: **REVISE, with no failure of the main inequality or regression.**

## Claim checked

The note starts from a full-debt global minimum and a complete response by one
player which kills that player's debt.  It claims that the resulting debt
transfer forces either an opponent cap rise or an opponent prescribed-payoff
loss, of size at least one sixth of the mover debt plus endpoint excess in
Fin4.  It also gives a source-attached approximate-response version and a
four-player local regression in which the cap vector and unique
all-Continue root survive the paid response.

The signed-seam theorem, factor \(1/6\), limiting passage, and explicit table
are correct.  The note does not consume either target arm.  Its repeated claim
that the “debt box” itself remains unchanged must be replaced by the narrower
and correct statement that the cap vector, and hence the exact-root problem at
that cap, remains unchanged.

## 1. Exact leakage and the Fin4 constant

Let \(x=(u,b)\) be a global minimum with total debt \(D_*\), and let player
\(p\)'s exact response produce \(y=(\widehat u,\widehat b)\).  Because only
\(p\)'s prescribed strategy changes,

\[
 \widehat b_p=b_p,\qquad
 \widehat u_p=b_p,\qquad
 d_p(y)=0.
\]

Putting \(F=D(y)-D_*\ge0\), exact summation gives

\[
 \sum_{i\ne p}\bigl(d_i(y)-d_i(x)\bigr)
 =d_p(x)+F.
\tag{1}
\]

For every opponent,

\[
 d_i(y)-d_i(x)
 =(\widehat b_i-b_i)-(\widehat u_i-u_i)
 \le(\widehat b_i-b_i)_+ +(u_i-\widehat u_i)_+.
\]

There are \(2(|I|-1)\) nonnegative summands.  Therefore one is at least

\[
 \frac{d_p(x)+F}{2(|I|-1)}.
\tag{2}
\]

For four players this is exactly \((d_p(x)+F)/6\).  No factor is missing.
If the statement is presented generically, it must assume \(|I|\ge2\);
the Fin4 theorem already has this automatically.

The unsigned estimate in the note is valid but unnecessarily weak.  It says
\(\lVert y-x\rVert_\infty\ge d_p(x)/2\) by comparing the two coordinates
forming \(p\)'s debt.  Exact own-cap invariance actually gives

\[
 |\widehat u_p-u_p|=d_p(x),
\]

so under the usual product sup norm the sharper bound is
\(\lVert y-x\rVert_\infty\ge d_p(x)\).

## 2. Approximate-response limit

The source-attached limiting form is correct.  At finite rank, own-cap
invariance is exact:

\[
 \widehat B_{p,n}=B_{p,n}.
\]

For an \(\varepsilon_n\)-best response,

\[
 B_{p,n}-\varepsilon_n
 \le \widehat U_{p,n}\le B_{p,n}.
\]

If the source semantic pairs converge to \(x\), the target pairs converge
along one common subsequence to \(y\), and \(\varepsilon_n\to0\), then

\[
 \widehat B_p=\widehat U_p=b_p,
 \qquad d_p(y)=0,
 \qquad \widehat U_p-u_p=d_p(x).
\]

The carrier is closed, so \(D(y)\ge D_*\), and (1)--(2) pass to the limit.
No unrelated target realization is selected.

The minimum/off-minimum split is also exact:

- if \(D(y)>D_*\), the literal response endpoints converge to an off-minimum
  target carrying the signed seam;
- if \(D(y)=D_*\), then \(p\) is absent from the target positive-debt support,
  while the full-debt source support is all of \(I\).

This is a strict one-step support inclusion.  The note correctly does not
claim renewability: a later response may reactivate \(p\)'s debt.

## 3. Debt-box use and required wording repair

The audited debt-box lemma says that every continuation vector
\(v\in[u,b]\) has all Continue as its unique exact root.  Hence if the target
cap satisfies

\[
 u\le\widehat b\le b,
\]

then the exact-root problem at \(\widehat b\) is inert.  In the cap-rise arm,
\(\widehat b\) crosses the upper face; in the payoff-loss arm it may remain
inside the source box.

However, the regression does **not** leave the debt box itself unchanged.
The source has

\[
 u=(0,0,0,0),\qquad b=(1,1,1,1),
\]

whereas the target has

\[
 \widehat u=(1,-1,0,0),\qquad
 \widehat b=(1,1,1,1).
\]

Thus \([\widehat u,\widehat b]\ne[u,b]\).  What is unchanged is:

1. the cap vector \(b\);
2. its membership on the upper face of the original box; and
3. the unique all-Continue exact-root problem at that cap.

The title of Section 5 and the phrases “the debt box may remain completely
unchanged” and “unchanged cap in the whole debt box” should be repaired
accordingly.  The mathematical no-go only needs unchanged cap/root data.

## 4. Exact regression

I recomputed every relevant value.

At \(S=\{0,1,2\}\), the prescribed payoff is zero.  Continuing by players
\(0,1,2\) respectively gives rewards at
\(\{1,2\},\{0,2\},\{0,1\}\), all equal to one; joining by player \(3\) gives
reward one at \(I\).  Hence

\[
 U(\sigma)=0,\qquad B(\sigma)=(1,1,1,1).
\]

At \(T=\{1,2\}\), the prescribed payoff and caps are

\[
 U(\tau)=(1,-1,0,0),\qquad B(\tau)=(1,1,1,1).
\]

Thus player \(0\)'s Continue response gains one, its debt is killed, player
\(1\)'s debt rises from one to two, and total debt remains four.

The claimed unique-root elimination is also exact:

1. player \(0\) strictly prefers Continue against every pure opponent
   coalition;
2. after \(0\) is fixed Continue, player \(1\) strictly prefers Continue
   against every coalition of \(\{2,3\}\);
3. after \(0,1\) Continue, player \(2\) strictly prefers Continue against
   either action of player \(3\); and
4. player \(3\) strictly prefers Continue against all Continue.

Linearity extends each strict comparison to mixed product opponents, forcing
the root hazards to vanish in that order.  All Never has zero debt because
every singleton reward is \(-2\), so the example's global minimum is zero.
The regression is therefore correctly limited to the local fields and is not
a Fin4 counterexample.

## 5. Novelty and consumer value

The exact leakage identity is standard in the cap-response and
minimum-fibre packets.  Nearby work already contains:

- recipient debt localization with a Fin4 one-sixth scale;
- full-reset payoff-loss/cap-escalation dichotomies; and
- examples showing that old exact roots cannot be reused after a paid fork.

The useful new statement here is the particularly clean **absolute signed
orientation for one full-debt response**:

\[
 \max_{i\ne p}
 \max\{(\widehat b_i-b_i)_+,(u_i-\widehat u_i)_+\}
 \ge\frac{d_p(x)+D(y)-D_*}{6}.
\]

Its limiting form is genuinely source-attached to the literal response
endpoints.  This is a useful one-step certificate, but not a new terminal
consumer:

- cap rise does not produce an exact root at the new cap;
- payoff loss does not produce chronological absorption;
- a one-time killed coordinate is not a renewable rank; and
- compact recurrence does not compose the horizontal edges.

The note should therefore remain an internal strengthening/no-go after the
wording repairs.  It does not answer the full-debt or paid-port consumer
questions by itself.

