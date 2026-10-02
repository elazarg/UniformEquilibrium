# Review of the ballistic normalized-flow omega-chain

## Verdict: PASS after repair

The compact bi-infinite omega-chain theorem, its finite-window actual-source
provenance, the sign of the limiting collision relation, and the displayed
rational matrix calculation are sound.  The regression's conclusion is
overstated: the same relation used in the example has an explicit stationary
fixed point.  The example proves that a particular source-compatible
bi-infinite chain need not be periodic; it does not prove that the relation
fails to contain a stationary or finite-period orbit.

The author has now made exactly this correction in the note: the title,
status, question, regression conclusion, and remaining lifting problem all
refer to nonclosure of the selected source-compatible chain; the fixed point
\((u,u,1/2)\) is displayed explicitly.  With that repair incorporated, the
note passes.

## Claim checked

The note claims that a uniformly ballistic, fully binding strict ray has a
bi-infinite path in the compact relation

\[
  \Lambda=\rho\lambda+(1-\rho)\Lambda^+,
\]

\[
  W_i=(M\Lambda)_i+\rho(J\lambda)_i\le0,
  \qquad \lambda_iW_i=0,
\]

with every finite window arising as a limit of actual ray windows.  It then
gives a rational full-support irrational-rotation orbit and uses it to argue
that the normalized data do not force stationary or periodic closure.

## 1. The omega-chain and provenance are valid

After the renewal ratios have a common lower bound, the actual normalized
states lie in compact

\[
  X_\eta=\Delta\times\Delta\times[\eta,1].
\]

Choose strictly increasing centers tending to infinity and diagonalize over
the countable integer offsets.  Negative offsets are defined eventually.
Restriction to any fixed finite window commutes with this extraction, giving
the stated window provenance.  For each fixed offset, the shifted centers are
again eventually a strictly increasing subsequence of actual ray dates, so the
checked subsequence collision theorems apply.

This last strictness should be said explicitly in a formalization plan, but it
is no mathematical gap.

## 2. The sign of the collision relation is correct

`QuittingTailNormalizedCapFlow.subseq_collision_nonpos` in
`Research/Quitting/ForwardExactCapTailFlow.lean` states

\[
  0\le -(M\Lambda)_i-\rho(J\lambda)_i.
\]

This is exactly

\[
  (M\Lambda)_i+\rho(J\lambda)_i\le0.
\]

The checked complementarity theorem gives

\[
  \lambda_i\big((M\Lambda)_i+\rho(J\lambda)_i\big)=0.
\]

Thus equations (1)--(3) use the correct sign convention.

## 3. The rational rotation calculation is exact

For

\[
  R=\begin{pmatrix}3/5&-4/5\\4/5&3/5\end{pmatrix},
\]

the geometric tail operator is indeed

\[
  H=\frac12(I-\tfrac12R)^{-1}
   =\begin{pmatrix}7/13&-4/13\\4/13&7/13\end{pmatrix}.
\]

With the displayed (M,J,u,v,w), direct rational arithmetic gives

\[
  Mu+\tfrac12Ju=0,
\]

\[
  M(\tfrac7{13}v+\tfrac4{13}w)+\tfrac12Jv=0,
\]

and

\[
  M(-\tfrac4{13}v+\tfrac7{13}w)+\tfrac12Jw=0.
\]

Therefore

\[
  M\Lambda(\theta)+\tfrac12J\lambda(\theta)=0
\]

for every phase.  The coordinates of \(\lambda\) lie in
\([1/8,3/8]\), so support is uniformly full.  The proof that
\((3+4i)/5\) has infinite multiplicative order is also correct, and the
current vector recovers both phase coordinates.  Hence this particular orbit
has no finite period.

The reward-table compatibility is honest at the claimed scope.  Own singleton
rewards zero and (r_i(\{j\})=M_{ij}) realize the normalized solo matrix;
(r_i(\{i,j\})=M_{ij}+J_{ij}) realizes the collision matrix.  No conflicting
coordinate assignments occur, and higher coalitions remain free.

## 4. The regression also has a stationary fixed point

The decisive correction is immediate from the constant calculation above.
Set

\[
  x_*=(u,u,1/2).
\]

Then the renewal equation is

\[
  u=\tfrac12u+\tfrac12u,
\]

and

\[
  Mu+\tfrac12Ju=0.
\]

Since every coordinate of (u) is positive, both the inequality and
complementarity conditions hold.  Therefore

\[
  x_*\,\mathcal R_{M,J,1/2}\,x_*.
\]

The exact relation used by the purported no-periodicity regression contains a
stationary normalized orbit.

Consequently the example does **not** establish any of the following:

* that \(\mathcal R_{M,J,1/2}\) has no stationary point;
* that it has no finite periodic orbit;
* that the matrix fields fail to imply existence of some stationary normalized
  state; or
* that an arbitrary source-derived chain cannot be accompanied by another
  periodic state elsewhere in the same relation.

What it does establish is still useful:

\[
  \boxed{
    \text{a bi-infinite full-support solution of the normalized relation need
    not itself be periodic.}
  }
\]

Thus compact recurrence and the displayed local identities do not identify
the *selected source omega-chain* with a finite cycle.  A new selection or
lifting theorem would be needed to replace it by the fixed point (x_*), and
even (x_*) contains no absolute root scale or payoff Bellman seam.

## 5. Required repair

Keep Sections 1--4 and the exact construction.  Revise the status, Section 5
conclusion, and Section 6 so that they distinguish:

1. nonperiodicity of the displayed source-compatible chain; from
2. nonexistence of periodic states in the full relation.

Only the first is proved.  The second is false for the displayed (M,J).

A genuine regression against existential stationary/periodic normalized
conclusions would need a relation satisfying all advertised hard fields and
having no fixed or periodic point.  Alternatively, the current example may be
retained as a regression solely against the assertion that every omega-chain
or every recurrent source selection is periodic.
