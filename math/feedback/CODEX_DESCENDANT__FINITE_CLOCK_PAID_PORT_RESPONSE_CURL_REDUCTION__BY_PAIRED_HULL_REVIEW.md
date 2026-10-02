# Audit of finite-clock paid-port response curl reduction

Reviewer: `PAIRED_HULL_REVIEW`  
Date: 2026-08-31  
Verdict: **REVISE.**  The bounded-calendar cycle, \(D_*/12\) recipient
localization, finite four-profile curl, and normalized common-prefix
minimization are mathematically sound.  The result needs two theorem-surface
repairs: reset-rigid landing requires the Fin4 hard-residual hypotheses, and
the compact minimizer retains a four-sequence semantic/law passport rather
than a literal common-response rectangle.  It does not instantiate the
compiled AGKRS S.3 consumer.

## 1. Claim checked

The note starts with a finite-clock profile in a quitting game with positive
global terminal-semantic minimum \(D_*>0\).  It iterates deterministic
pure-time/Never exact best responses of maximum-debt players, extracts a
finite horizontal cycle, localizes a nonmover debt rise of at least
\(D_*/12\), and forms a commuting four-profile response rectangle carrying
that curl.  It then closes under common finite prefixes and minimizes the
first profile's debt subject to normalized curl and paid-gain constraints.

The claimed terminal split is reset-rigid global minimum or a strict
off-minimum unique-all-Continue descendant carrying the two normalized
passports.

## 2. Bounded-calendar iteration is correct

Let \(H_0\) bound the finite support of every original stopping law.  Against
opponents with no finite stopping time after \(H\), every pure time strictly
larger than \(H\) has the same payoff, so a maximizer is found in

\[
 \{0,\ldots,H+1\}\cup\{\infty\}.
\]

The finite times larger than \(H\) need not have the same payoff as Never:
on the all-opponents-Never event, a late finite stop pays the singleton reward
whereas Never pays zero.  The candidate set correctly keeps both \(H+1\) and
Never, so the proof does not use that false equality.

The sharper invariant \(H_0+1\) is also correct.

- A time \(H_0+1\) was not in an original strategy; it can only have been
  installed as a pure response and is therefore a sure stopping time.
- If the current mover is not its owner, that sure opponent makes every
  later finite response equivalent to Never, and the declared tie convention
  selects Never.
- If the mover is the sole owner, all opponent horizons are at most \(H_0\),
  so the general bound is \(H_0+1\).
- If several players own \(H_0+1\), moving one of them leaves another sure
  opponent at that date, reducing to the first case.

After a coordinate first moves, it is one of finitely many pure times or
Never; before it moves, it is its one fixed original finite-clock strategy.
Thus the state space is finite.  The note should explicitly fix a
deterministic tie rule for the maximum-debt player as well as for the pure
response.  This is a minor statement repair, not a mathematical gap.

Every current profile is actual, so its total debt is at least \(D_*\), and
the selected maximum-debt player has gain at least \(D_*/4\).  Hence every
transition is nontrivial.  An infinite deterministic walk on the finite state
space therefore contains a nontrivial literal cycle.  The note correctly
calls this cycle horizontal rather than temporal Nash--Bellman play.

An incidental strengthening is worth recording carefully: the cycle
construction itself needs only one finite-clock starting profile and
\(D_*>0\); it does not use the incoming off-minimum paid port.  For example,
one may start from all Never.  Starting from the deadline theorem's output is
still useful because it retains the particular finite ancestry claimed in
Section 6.

## 3. The \(D_*/12\) leakage floor is exact

For edge \(k\), mover \(i_k\), gain \(g_k\), and nonmover debt changes
\(\Delta_{k,h}\), own-cap invariance gives

\[
 D(\sigma^{k+1})-D(\sigma^k)
 =-g_k+\sum_{h\ne i_k}\Delta_{k,h}.
\]

The total-debt differences telescope around the repeated literal state, so

\[
 \sum_{k<m}\sum_{h\ne i_k}\Delta_{k,h}
 =\sum_{k<m}g_k\ge mD_*/4.
\]

There are \(3m\) edge--nonmover pairs in Fin4.  Therefore at least one has

\[
 \Delta_{k,j}\ge D_*/12.
\]

Negative recipient changes cause no problem: the maximum of the \(3m\)
numbers is at least their average.  The selected recipient is automatically
distinct from the mover.

## 4. The finite commuting rectangle and curl are correct

Let \(S\to E\) be the selected mover-\(p\) edge and let \(a_j\) be an exact
pure-time/Never best response to \(E_{-j}\).  Finite-calendar extremality
ensures attainment.  With

\[
 R=(a_j,E_{-j}),\qquad Q=(a_j,S_{-j}),
\]

the \(p\)- and \(j\)-updates commute because \(p\ne j\).  Own-cap invariance
gives \(d_j(R)=0\).  Moreover

\[
 U_j(R)-U_j(E)=d_j(E),
\]

whereas

\[
 U_j(Q)-U_j(S)\le d_j(S).
\]

Thus the alternating curl is at least

\[
 d_j(E)-d_j(S)\ge D_*/12.
\]

The mover gain remains at least \(D_*/4\).  These are exact finite-profile
facts, not compact-limit substitutions.

The terminal-law decoder is valid.  The curl is the reward moment of

\[
 \mu_R-\mu_E-\mu_Q+\mu_S.
\]

There are fifteen finite coalitions; treating Never as a sixteenth zero-reward
coordinate gives the conservative floor \((D_*/12)/16=D_*/192\).  The note
correctly does not replace this four-law coordinate by an unsupported two-law
difference.

## 5. Prefix normalization and root neutralization are correct

For one common finite root word \(W\), fresh prefix rewards cancel in both
alternating differences.  Hence the curl and mover gain both scale by the
same joint all-Continue mass \(c(W)\).  At the initial quartet,
\(d_j(R)=0\), so sufficiently small positive constants \(\theta,\psi\) make
the normalized slice nonempty.

The closure of the common-prefix orbit is compact in the finite product of
joint semantic/law carriers, and the slice constraints are closed.  Let a
minimizer have first-coordinate debt \(D_0\).  Every carrier coordinate has
debt at least \(D_*>0\), so \(D_0>0\).

If \(q\) is exact cap--Nash against the first coordinate's cap, prefixing the
whole quartet by \(q\):

- keeps the quartet in the closed orbit;
- scales first-coordinate debt and its zero \(j\)-coordinate by \(c(q)\);
- scales both normalized passports by \(c(q)\).

It therefore stays in the slice.  Minimality gives

\[
 D_0\le c(q)D_0,
\]

so \(c(q)=1\) and \(q\) is all Continue.  Conversely finite root-game Nash
existence gives some exact root, and the preceding uniqueness forces that
root to be all Continue.  Thus the iff statement is valid.

There is one visible TeX defect to repair: display (5.2) lacks its closing
`\]`.

## 6. Exact output type and source provenance

Before closure, \((R,Q,E,S)\) is a literal four-profile response rectangle
with finite ancestry.  After taking a common-prefix sequence and passing to a
limit, what remains exactly is:

- four joint semantic/law limit points obtained along one common subsequence;
- one zero debt coordinate on the first point;
- a positive alternating four-law/payoff curl;
- a positive prescribed-payoff difference between the third and fourth
  points; and
- the common-prefix descendant sequence which witnesses provenance.

The limit points need not themselves be realized by four behavioral profiles
with one common \(j\)-response and one commuting \(p\)-replacement.  Strategy
space was not included in the compact coordinate.  Therefore the strict
output should be called a **closed four-point curl passport** or a
**common-prefix descendant curl passport**, not a literal response rectangle
or executable paid port.  Its scalar gain is not by itself a behavioral edge
at the limit.

This repair agrees with the note's final warning that only closed-descendant
provenance is retained, but the theorem headline and proposed structure must
make it explicit.

No unrelated source is selected: all four coordinates use the same prefix
word at every finite rank and one common convergent subsequence.  The original
minimum/paid-port ancestry remains stored externally through the finite path
to the cycle and the original quartet.  It is provenance, not a finite prefix
code realizing the limit.

## 7. Reset-rigid landing needs an explicit hard-residual hypothesis

If the minimized first coordinate has debt \(D_*\), it is a global minimum
with \(d_j=0\).  To conclude positive opponent incidence and enter the
law-tight reset-rigid chamber, the proof additionally uses:

1. positive finite-atom existence at every Fin4 global-minimum joint law;
2. singleton/Never zero-debt cap tightness; and
3. the positive global singleton margin, together with the retained terminal
   exploitability/hard-residual witness needed by the reset dispatcher.

The first and third items do not follow from the Section 1 hypothesis
\(D_*>0\) alone.  They are supplied in the maintained Fin4 no-uniform-payoff
hard residual.  Thus the final theorem must either assume that residual
explicitly, or weaken the equality landing to:

> a global-minimum joint point with \(d_j=0\) and unique all-Continue cap
> root.

With the hard residual added, the reset-rigid conclusion is sound and uses
the same joint law; no unrelated minimum or law is reselected.

The off-minimum landing is exactly a strict descendant first coordinate with
zero \(j\)-debt, a unique all-Continue cap root, and the two positive
debt-relative **closed passports**.  It is not an actual paid edge at that
limit.

## 8. No automatic AGKRS consumption

The new compiled AGKRS no-terminal S.3 theorem and chronological adapter do
not consume this packet.

- Every vertex of the horizontal response cycle has total debt at least
  \(D_*>0\); the cycle is not a sequence of absorbing approximately-perfect
  roots.
- Its edges are complete unilateral best responses between alternative
  profiles, not successive one-stage roots of one absorption path.
- The common-prefix minimizer has only the all-Continue exact root, hence
  supplies no positive absorbing S.3 row.
- The four-law curl is a static alternating payoff certificate, not the
  rotation-uniform signed lasso or sequential-perfect source required by the
  AGKRS adapter.

Therefore no already compiled AGKRS leaf is duplicated.  A new adapter would
have to turn the horizontal curl into an absorbing approximately-perfect
chronology; that is essentially the still-open consumer, not a routine type
conversion.

## 9. Required repairs and disposition

The author should:

1. add a deterministic tie rule for the maximum-debt player;
2. state the hard-residual/no-uniform-payoff data needed for reset-rigid
   landing, or weaken that landing;
3. type the strict limit as a common-prefix descendant four-point curl
   passport, without claiming an actual response rectangle or paid edge at
   the limit;
4. preserve the distinction between the finite literal quartet and its
   compact limit; and
5. close display (5.2).

After these repairs, the note is a sound and useful reduction.  It is not a
terminal consumer, a renewable rank, an AGKRS entrance, or a proof of Fin4
uniform equilibrium.

