# Live cap-band target: approximate cap-Nash word or an outsider pre-tail response

Author: CODEX_HAHN

## Status

**Exact ordinary mathematics; proof draft, not Lean-checked and not a
consumer.**  Apply the late-receiver cap-band construction with widths
tending to zero.  The resulting owner deterministically Continues through
the old exact word, so the modified word retains a fixed joint-survival
floor.  Its cap-anchored defect ledger then gives an exhaustive alternative:

1. the whole modified word is cap-Nash against its literal successor caps
   with total error tending to zero; or
2. one fixed outsider has a fixed-gain pure-time response whose first
   disagreement occurs inside the still-live word.

This converts loss of the outsiders' old root inequalities into a precise
second source-attached edge.  It still does not return either child as the
next positive-minimum source.

## 1. Input and vanishing-width live target

Let \(I=\operatorname{Fin}4\), and let every reward coordinate have absolute
value at most \(R\).  For each \(n\), let

\[
 \Sigma_n=W_n\triangleright X_n
\tag{1}
\]

be an actual profile, where \(W_n\) is a finite word of exact payoff Nash
roots against its literal successors and has length \(m_n\).  Fix one player
\(k\) and \(\eta>0\).  Assume eventually

\[
 d_k(\Sigma_n)\ge D_*/2,
 \qquad
 \Pr_{\Sigma_n}(T_{-k}\ge m_n)\ge\eta,
 \qquad D_*>0.
\tag{2}
\]

These are the owner-debt and host-deleted reach conclusions of the
unique-sure persistent-word branch.

Choose any sequence

\[
 e_n>0,
 \qquad e_n\longrightarrow0,
 \qquad e_n<D_*/4.
\tag{3}
\]

At each rank select a pure-time-or-Never receiver within \(e_n/2\) of
player \(k\)'s complete cap and apply the width-\(e_n\) cap-band pushforward
to \(k\)'s source stopping law.  Call the actual target \(Y_n\).

The finite exact-word stopping screen says that every pure stopping time
strictly before \(m_n\) pays player \(k\) at most
\(U_k(\Sigma_n)\).  Since the cap is at least
\(U_k(\Sigma_n)+D_*/2\), every such clock is outside the width-\(e_n\) band,
whereas an \(e_n/2\)-near receiver cannot be inside the word.  Consequently
the pushforward moves all of \(k\)'s preboundary stopping mass to the
boundary, later, or Never.  Thus

\[
 \Pr_{Y_n}(T_k\ge m_n)=1,
 \qquad
 a_n:=\Pr_{Y_n}(T_I\ge m_n)\ge\eta.
\tag{4}
\]

The cap-band estimates also give

\[
 U_k(Y_n)-U_k(\Sigma_n)\ge d_k(\Sigma_n)-e_n,
 \qquad
 d_k(Y_n)\le e_n.
\tag{5}
\]

Write \(Z_n\) for the literal actual suffix of \(Y_n\) at the boundary
\(m_n\).  It has the old opponents from \(X_n\) and the conditional residual
of the pushed owner law.  It is not silently identified with \(X_n\).

## 2. The cap-anchored ledger of the modified word

Let \(y_{n,t}\) be the actual live product root of \(Y_n\) at row
\(t<m_n\), and let \(B_{n,t+1}\) be the complete cap vector of its literal
successor.  Define the coordinate defect

\[
 c_{n,t,i}
 :=\operatorname{NashDefect}_i(r,B_{n,t+1},y_{n,t})\ge0.
\tag{6}
\]

Let \(A_{n,t}\) be joint reach through the rows strictly before \(t\), and
put

\[
 L_{n,i}=\sum_{t<m_n}A_{n,t}c_{n,t,i},
 \qquad L_n=\sum_iL_{n,i}.
\tag{7}
\]

Because final joint reach is \(a_n\ge\eta\), monotonicity gives

\[
 A_{n,t}\ge a_n\ge\eta
 \qquad(t<m_n).
\tag{8}
\]

The arbitrary-root cap--debt telescope is exact coordinatewise:

\[
 d_i(Y_n)=L_{n,i}+a_n d_i(Z_n).
\tag{9}
\]

In particular, all terms are nonnegative and (5) gives

\[
 0\le L_{n,k}\le e_n\longrightarrow0.
\tag{10}
\]

## 3. Exhaustive ledger dichotomy

After passing to a subsequence, exactly one of the following alternatives
holds.

### A. Approximate literal cap-Nash word

\[
 \sum_{i\ne k}L_{n,i}\longrightarrow0.
\tag{11}
\]

Then \(L_n\to0\).  Define the unweighted total row error

\[
 E_n:=\sum_{t<m_n}\sum_i c_{n,t,i}.
\tag{12}
\]

Equations (7)--(8) imply

\[
 0\le E_n\le L_n/\eta\longrightarrow0.
\tag{13}
\]

Therefore every displayed root is an \(E_n\)-Nash root against the complete
cap of its literal actual successor, and the sum of all rowwise coordinate
defects is at most \(E_n\).  The actual-payoff Bellman identities are exact
because these are the actual roots and actual suffix payoffs of \(Y_n\).
Hence

\[
 Y_n=(y_{n,0},\ldots,y_{n,m_n-1})\triangleright Z_n
\tag{14}
\]

is a literal approximate **cap-Nash** word with total cap-root error tending
to zero and endpoint reach at least \(\eta\).  It is not an ordinary
approximate Nash--Bellman block: its root inequalities use successor cap
vectors, whereas its exact Bellman identities use successor prescribed
payoff vectors.

This is stronger than pointwise root convergence: the unweighted error over
the entire growing word tends to zero.

### B. Fixed outsider pre-tail response

There are a fixed outsider \(i\ne k\), a number \(\ell>0\), and a
subsequence such that

\[
 L_{n,i}\ge\ell.
\tag{15}
\]

By (9), \(d_i(Y_n)\ge\ell\).  Pure-time extremality supplies a deterministic
finite-or-Never response \(Q_{r_n}\) with gain at least

\[
 U_i(Y_n[i\leftarrow Q_{r_n}])-U_i(Y_n)
 \ge d_i(Y_n)-\ell/4\ge3\ell/4.
\tag{16}
\]

This response must first disagree with player \(i\)'s prescribed behavior at
a date \(s_n<m_n\).  Indeed, if \(r_n<m_n\), this is immediate.  If
\(r_n\ge m_n\) or \(r_n=\mathrm{Never}\), the pure response Continues
through the word.  If the source has positive Quit mass at any word row,
the first such row is a preboundary disagreement.  If instead the source
player already Continues surely throughout the word, then changing only the
reached tail can gain at most

\[
 a_n d_i(Z_n).
\]

But (9), (15), and (16) give a gain strictly larger than that quantity,
which is impossible.  Thus the first disagreement is inside the word in all
cases.

Since the original and deviating profiles agree before \(s_n\), the source
probability of reaching this first disagreement is

\[
 A_{n,s_n}\ge a_n\ge\eta.
\tag{17}
\]

Thus alternative B supplies a fixed outsider label, a fixed complete
behavioral gain, and an actually reached first disagreement strictly before
the same live tail boundary.

### Exhaustiveness

Apply the real subsequence dichotomy to the nonnegative scalar sequence
\(\sum_{i\ne k}L_{n,i}\).  If its liminf is zero, refine so that it tends to
zero and obtain A.  Otherwise it has a positive eventual floor; finite
pigeonhole among the three outsider coordinates gives B.

## 4. What this does and does not solve

The original cap-band edge and the ledger fork now have exact source
incidence:

\[
 \Sigma_n\dashrightarrow_k Y_n,
\]

followed either by a literal approximate cap-Nash word from \(Y_n\) to its
actually reached suffix \(Z_n\), or by

\[
 Y_n\dashrightarrow_iY_n[i\leftarrow Q_{r_n}],
 \qquad i\ne k,
\]

whose first disagreement is reached before \(Z_n\) with probability at
least \(\eta\).

Alternative A still does not identify \(Z_n\) with the next member of one
renewable source family.  More basically, cap-root control does not bound
the ordinary payoff-root Nash error because the successor debt
\(B_{n,t+1}-U_{n,t+1}\) may be macroscopic.  Alternative B is a horizontal
complete-response edge; changing player \(i\)'s law can invalidate the
comparisons that made the owner edge profitable.  The positive ledger is
not being called an additive prescribed-payoff chronology.

Thus the dichotomy consumes the local outsider-root ambiguity but not the
global source-reprojection waist.  The remaining exact question is:

> Does the particular reached suffix \(Z_n\) in A regenerate the hard source
> packet, or does the fixed outsider edge in B give a return before changing
> the owner response's cap comparison?

Without one of those facts, neither branch is a terminal consumer or a
renewable rank.

## Sources inspected

- `notes/CODEX_SPINOZA__EXACT_WORD_FORCES_LATE_CAP_BAND_RECEIVER_AND_LIVE_TARGET.md`;
- `notes/CODEX_SPINOZA__UNIQUE_SURE_PERSISTENT_WORD_HOST_PAYER_CAP_BAND.md`;
- `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`;
- `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `Research/Quitting/FiniteWordWeightedCapDefectLedger.lean`;
- `Research/Quitting/PaidNonexactCapStackAccount.lean`; and
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

## Boundary tests and nonclaims

- The final reach floor is essential for (13).  A small reached ledger does
  not control the unweighted error of rows hidden behind vanishing reach.
- The vanishing band width is essential for (10).  A single fixed-width
  target leaves a fixed owner ledger allowance.
- Alternative B does not select one row with fixed local defect; the ledger
  may diffuse over a growing word.  It selects one complete pure-time
  response with an early first disagreement.
- Vanishing cap-root defect does not imply vanishing payoff-root defect.  In
  the one-row regression with a tail where \(j\) Quits surely, take only
  \(r_k(\{k,j\})=1\), \(r_i(\{j\})=-1\), and
  \(r_i(\{i,j\})=1\) nonzero.  The late \(k\)-response makes the target root
  all Continue.  For outsider \(i\), Continue is optimal against the tail
  cap \(1\), so the cap-root defect is zero, while Quit is better than
  Continue against the tail prescribed payoff \(-1\), giving ordinary
  payoff-root defect one.  This local table has \(D_*=0\); it diagnoses the
  missing cap/payoff bridge and is not a hard-branch counterexample.
- No punishment-floor property, exact-root repair, return, renewable rank,
  terminal approximate Nash profile, or uniform-equilibrium payoff is
  claimed.
