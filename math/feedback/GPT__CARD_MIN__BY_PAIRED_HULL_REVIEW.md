# Review of CARD_MIN

Reviewer: PAIRED_HULL_REVIEW  
Date: 2026-08-31  
Verdict: **PASS as reached-face normalization and no-go; it does not answer
the cardinal-minimal consumer question**

## Exact theorem checked

Assume a cardinal-minimal finite quitting counterexample with terminal gap
\(\gamma>0\). For every nonempty proper deleted block \(B\), every
sufficiently accurate terminal equilibrium approximation of the survivor
game has a deleted outsider with a finite pure-time gain at least \(\gamma\).
The note proves that one may pass to the actually reached suffix at that
witness and obtain, uniformly in \(B\):

1. reach at least \(\rho=\gamma/(2M)>0\);
2. an immediate-Quit outsider gain at least \(\gamma\); and
3. terminal survivor exploitability divided by at most \(\rho\).

Because there are finitely many proper blocks, one common subsequence fixes
all outsider labels and compactifies all face data simultaneously. Each face
then has a reached limiting zero-debt survivor source with its fixed immediate
outsider obstruction. The note also identifies the absence of a profilewise
cross-face compiler.

This theorem is correct.

## 1. Reached-suffix normalization: PASS

If \(d\) is prescribed Never and quits at time \(t\), the baseline and
deviating plays coincide before \(t\). Conditioning on the all-Continue
history gives

\[
G_d(t;\sigma)=p_tG_d(0;\sigma^{[t]}).
\]

Every payoff difference is at most \(2M\), hence

\[
p_t\ge\frac{\gamma}{2M}.
\]

Since \(p_t\le1\), the conditional immediate gain is at least \(\gamma\).

For a survivor, splice any suffix deviation after time \(t\). Its source gain
is \(p_t\) times its suffix gain, so terminal \(\varepsilon\)-Nash of the
source implies terminal \(\varepsilon/p_t\)-Nash of the suffix against all
behavioral deviations. The chosen

\[
\varepsilon_0=\frac12\min\{\rho\eta,\gamma\}
\]

is strictly below \(\gamma\) and gives the advertised \(\eta\) bound.

## 2. Simultaneous face selection: PASS

There are finitely many proper blocks, so one diagonal subsequence fixes all
outsider labels. Products of the terminal-law simplices, root cubes,
payoff/cap boxes, and reach intervals are compact. Survivor debts tend to
zero. The immediate outsider gain is a continuous finite polynomial in the
date-zero root and payoff. Thus the simultaneous limiting assertions are
valid.

The limit is correctly described as a joint-carrier limit, not necessarily
the semantic pair of one attained behavioral profile. Uniform positive-reach
provenance belongs to the approximating actual suffixes.

## 3. Cross-face obstruction and regression: PASS

Cardinal minimality separately produces a zero-debt source on each proper
face. It gives no extension, restriction, suffix, or continuation map between
two selected sources. A positive gap on the fiber extending one chosen child
equilibrium is not a gap of the whole child or parent game.

The two-player regression is exact. With player 1 constrained to Never and
\(p\) the probability player 2 eventually Quits,

\[
d_2=1-p,
\qquad
G_1(Q_0)=2p-1-\frac12p_0\ge\frac32p-1.
\]

Hence the constrained fiber has exploitability at least \(1/5\). Yet the
parent profile in which player 1 Quits at date zero and player 2 Continues
then Quits at date one is an exact behavioral terminal equilibrium. This
refutes compact fiber separation as a cardinal-reduction argument.

## 4. Compiler inequality: PASS

The proposed finite-family certificate

\[
e_r(L(x_1,\ldots,x_m))
\le C\max_a e_{G_a}(x_a)
\]

is sufficient in both directions. For a finite independent product,

\[
\inf_{(x_a)}\max_a e_{G_a}(x_a)
=\max_a\inf_{x_a}e_{G_a}(x_a).
\]

Quiet lifting one selected face cannot satisfy this inequality because its
child error tends to zero while the deleted outsider retains gain at least
\(\gamma\). This specifies the missing reduction; it does not construct it.

## 5. Singleton-survivor extraction: PASS

For \(s_i\ge0\), a one-player stopping time uniform on
\(\{1,\ldots,N\}\) is an exact terminal equilibrium. Letting
\(N\to\infty\) in the displayed gain formula forces some \(d\ne i\) with

\[
s_d-r_d(\{i\})\ge\gamma.
\]

For \(s_i<0\), the unique one-player equilibrium is Never, and the outsider
conclusion yields some \(s_d\ge\gamma\).

The resulting serial graph may be described on the players plus a bottom
state. Its cycle need not use one uniform reward-inequality type and gives no
bounded player kernel. The note does not claim otherwise.

The table \(r_i(S)=\mathbf1_{\{i\in S\}}\) correctly shows that perfectly
coordinated immediate outsider labels on all faces coexist with an exact
ambient all-Quit equilibrium.

## 6. Does it answer the maintained question?

**No.** It gives:

* no cardinal bound;
* no finite-child compiler;
* no inherited positive child gap; and
* no certified positive-gap table.

It removes a false obstruction: identity, time, accuracy, law, payoff, and
uniformly reached suffix provenance can be coordinated simultaneously inside
all finitely many faces. The remaining obstruction is the cross-face
compiler.

## 7. Novelty

The content is useful but mostly consolidating.

* The operational-essential-support note already gives every-block outsiders
  and exact finite pure-time witnesses.
* The codimension-one quiet-face note already proves the same reach lower
  bound and unrestricted suffix-Nash rescaling for singleton deletion, with
  a stronger coalition-atom extraction.
* The Fin5 frozen-source and phase-seam notes already give stronger exact
  regressions for unrelated face sources.

The distinct addition is the simultaneous all-proper-block packaging and the
abstract score-compiler criterion. That is a modest strengthening, not a
conjecture contraction.

## Disposition

Retain as an internal normalization/no-go if desired. It should not resolve
questions/CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md and does not justify a
separate export.
