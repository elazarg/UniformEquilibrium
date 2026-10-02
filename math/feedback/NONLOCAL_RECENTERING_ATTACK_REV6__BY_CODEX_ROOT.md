# Review of `NONLOCAL_RECENTERING_ATTACK.md`, Revision 6

Reviewer: `CODEX_ROOT`

## Verdict

Sections 14--15 add real and useful mathematics.  The exact window-deletion
identity is correct, the minimum-debt screening inequality has the correct
orientation, and the impure-row route avoids the unsupported assumption that
purified endpoints themselves are near-minimizing.  This is not yet a
consumer: the proposed screening system is a necessary-condition generator,
and its finite infeasibility has not been proved.

The document is also unusually well matched to the current full-debt
frontier.  The newly produced uniformly reached paid suffix is naturally a
**deleted-observer/counterfactual car**, not automatically an actual
absorption car.  The typed-train distinction in Section 12 is therefore
load-bearing.

## Check of the new deletion calculation

Write the original profile as

\[
 \sigma=\pi\star V\star T
\]

and replace the window by an all-Continue word of the same length:

\[
 \sigma'=\pi\star C\star T.
\]

The graft identities give

\[
 U_i(\sigma)
 =U_i^\pi+\rho_a\bigl(U_i^V+\rho_VU_i(T)\bigr),
 \qquad
 U_i(\sigma')=U_i^\pi+\rho_aU_i(T),
\]

which subtract to Theorem 14.2's prescribed-payoff identity.  Applying the
cap max formula first across \(\pi\), and then across \(V\), gives exactly the
two displayed outer maxima.  No tail cap appears through the all-Continue
window except as \(\max(r_i(\{i\}),B_i(T))\), as stated.

Since

\[
 D(\sigma')-D(\sigma)
 =\sum_i\Delta B_i-\sum_i\Delta U_i
 \ge -\bigl(D(\sigma)-D_*\bigr),
\]

Corollary 14.3 follows with the displayed sign.  The pure-pair values in
Remark 14.4 are also correct: deleting any one player still leaves at least
one sure quitter, so every \(\rho_V^{-i}\) is zero before deletion.

Lemma 15.1 is valid for a one-row product root.  For an outsider \(i\), the
event realizing exactly the pair \(\{j,o\}\) is disjoint from opponents-all-
Continue after deleting \(i\), and its probability in the deleted product is
at least its probability in the original root.  Thus
\(\rho_V^{-i}\le1-c\).

## Small corrections outside Revision 6

The conclusion of Theorem 13.2 is sound, but the displayed proof's harmless
constant is too optimistic under the stated reward convention.  From

\[
 |A_i(t)-N_i|\le R\varepsilon
 \quad\text{and}\quad
 |Q_i(t)-(A_i(t)+\rho^{-i}_tr_i(\{i\}))|
 \le2R\varepsilon,
\]

one obtains \(Q_i(t)\ge N_i-3R\varepsilon\), not necessarily
\(N_i-2R\varepsilon\).  Letting \(\varepsilon\downarrow0\) proves the same
lower-semicontinuity theorem, so Sections 13.5--13.6 are unaffected.

Corollary 13.6 should say that a *pointwise convergent subsequence* of a
minimizing sequence attains the infimum, or retain the standing assumption
that the sequence itself converges pointwise.  Compactness supplies such a
subsequence, but not convergence of every original sequence without
selection.

## Connection to the current full-debt chamber

The current source-facing paid-block work gives a literal first-disagreement
row with a uniform positive `liveMass` and gain, retained behind arbitrarily
long exact prefix orbits.  Here `liveMass` is

\[
 \rho^{-i}_{t},
\]

the survival of the observer's opponents.  It is not the actual joint reach
\(\rho_t\): the observer may already have quit on the prescribed path.  Thus
the uniform row belongs directly to the deleted-\(i\) train used to compute
\(B_i\); Theorem 4.2 cannot promote it to an actual full kernel without an
additional owner-survival field.  This is exactly the typing correction of
Section 12, not a minor API distinction.

There is also a sharp all-Continue-delay regression.  If \(\sigma\) is any
paid block in the minimum-fibre all-Continue tube, define

\[
 \sigma^{H+1}=\mathbf C\star\sigma^H.
\]

Every prefix is exact, the complete semantic pair and time-forgetting
terminal law are unchanged, the retained finite atom and paid gain are
unchanged, and the suffix entrance probability is one; nevertheless the paid
row moves from `start` to \(H+\text{start}\), while every fixed calendar row
converges to all Continue.  Recentering recovers \(\sigma\) but forgets an
absolute source cut and does not create a forward right-extending chronology.

Therefore neither uniform reach, terminal-law tightness, nor the train
decomposition alone can solve the full-debt temporal escape.  A successful
recentered consumer must retain an extension-compatible absolute cut, or
produce a genuine bounded-time restart/return edge.  This regression should
be included when the note promotes the screening program from necessary
conditions to a claimed chronology theorem.

## What Revision 6 accomplishes

The important advance is not a solution of N3 but a correct bifurcation:

1. if purified endpoints can be proved near-minimizing, the pure-row formula
   gives a small explicit constraint system; otherwise
2. the same deletion inequality applies directly to the actual impure
   realizers, and the pair-mass field supplies quantitative outsider
   screening without purification.

Route (2) is mathematically available now.  The next serious test is to write
the one-round Fin4 system with all max branches exposed and ask whether it is
feasible under the full-debt moat, paid-gain floor, zero selected defect, and
global minimum inequalities.  A feasible exact rational point would be useful
negative information; an infeasibility certificate would be a genuine chamber
consumer.  Until that calculation is done, Section 15 should remain labeled a
program rather than a reduction theorem.

