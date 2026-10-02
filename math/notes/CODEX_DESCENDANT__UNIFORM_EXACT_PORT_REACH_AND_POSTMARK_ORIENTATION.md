# Uniform exact-port reach and the post-mark orientation barrier

Identity: `CODEX_DESCENDANT`

Date: 2026-08-31

Status: **ordinary mathematics proved below; not a terminal consumer.**  A
terminal exploitability witness gives a table-uniform lower bound on the
survival of every finite exact punishment-floor prefix.  Combined with the
actual-reach paid-row selection, this produces arbitrarily deep, near-minimum
actual profiles whose shifted paid row has both a fixed joint-entry floor and
a fixed paid-gain floor.  The roots all occur before the paid row.  This does
not produce the later post-mark block required by the current two-cut or
AGKRS consumers.

## 1. Question

Let a four-player quitting game have a terminal exploitability witness of gap
\(\gamma>0\), reward bound \(M\), and positive global semantic-debt minimum
\(D_*>0\).  Suppose actual punishment-floor-safe profiles \(\sigma_n\) satisfy

\[
 D(\sigma_n)\longrightarrow D_*
\]

and carry paid first-disagreement rows of one fixed positive gain and one
fixed positive actual joint-entry floor.  Repeated exact punishment-floor
prefixing retains each row as a literal shifted suffix.  Can its reach vanish
as \(n\) and the prefix depth vary?

It cannot.  There is one positive lower bound depending only on the reward
table and terminal-gap witness.

## 2. Uniform one-root survival

The terminal-gap root estimate says that for every payoff \(v\) in the
canonical punishment-floor box, every exact Nash root \(q\) against \(v\),
and every player \(i\),

\[
 q_i(Q)
 \le 1-\frac{\gamma}{4M}.
\tag{2.1}
\]

The existence of the positive terminal gap implies \(M>0\).  Put

\[
 h:=\frac{\gamma}{4M}>0,
 \qquad r:=h^4>0.
\tag{2.2}
\]

For Fin4, (2.1) gives

\[
 c(q):=\Pr_q(\text{all Continue})
 =\prod_{i<4}(1-q_i(Q))\ge r.
\tag{2.3}
\]

Equivalently, the absorption charge \(a(q)=1-c(q)\) satisfies

\[
 0\le a(q)\le1-r<1.
\tag{2.4}
\]

This is uniform over the entire exact punishment-floor root relation.  No
compactness selection is needed; the checked root estimate already gives the
explicit coordinate margin.

## 3. Uniform survival through every finite exact word

Fix one source index \(n\).  Let
\(W_{n,N}=(q_{n,0},\ldots,q_{n,N-1})\) be a compatible exact
punishment-floor prefix certificate of depth \(N\) whose inner boundary is
the prescribed payoff of this same \(\sigma_n\).  Thus every root carries
the required box, anchor-floor, Bellman, and exact-Nash fields, and the word
is not selected independently of the suffix.  Write

\[
 a_{n,t}=1-c(q_{n,t}),
 \qquad S_{n,N}=\prod_{t<N}c(q_{n,t}).
\]

The terminal exploitability witness supplies the common finite-prefix charge
budget

\[
 \sum_{t<N}a_{n,t}\le C,
 \qquad
 C:=\operatorname{PrefixChargeBound}(\text{reward}).
\tag{3.1}
\]

For \(c\in[r,1]\), the mean-value theorem applied to \(-\log c\) gives

\[
 -\log c\le\frac{1-c}{r}.
\tag{3.2}
\]

Therefore

\[
 \log S_{n,N}
=\sum_{t<N}\log c(q_{n,t})
 \ge-\frac1r\sum_{t<N}a_{n,t}
 \ge-\frac Cr.
\]

Hence every such finite word satisfies the same explicit floor

\[
 \boxed{S_{n,N}\ge \lambda:=\exp(-C/r)>0.}
\tag{3.3}
\]

The conclusion is stronger than pointwise positivity of the limiting product
on each separately selected summable orbit.  It is uniform across source
indices and all depths and choices inside the class of compatible
same-source exact prefix certificates.  It does not authorize grafting an
unrelated exact word onto an arbitrary suffix.

## 4. Composition with the actual-reach paid row

The reviewed minimum-floor repair gives actual \(\sigma_n\) with
\(D(\sigma_n)\to D_*\).  The scratch actual-reach theorem, applied with
\(\Delta=D_*/2\), supplies a row of gain

\[
 g_0=D_*/8
\tag{4.1}
\]

at a start date \(t_n\), with

\[
 \Pr_{\sigma_n}(\text{all players survive strictly before }t_n)
 \ge \rho:=\frac{D_*^2}{128M^2}>0.
\tag{4.2}
\]

It can additionally retain that the row's source pure time lies in the
support of player \(p\)'s prescribed complete stopping law.

For a sufficiently late source index \(n\), first choose the actual row,
date \(t_n\), mover, source and target pure-time witnesses, and supported
source atom given by the scratch selector.  Then prefix any compatible
same-source certificate \(W_{n,N}\) of length \(N\), and shift this exact
row datum by \(N\).  Literal root-word factorization gives

\[
 \Pr_{W_{n,N}\star\sigma_n}
   (\text{joint entry at the shifted row start})
 =c(W_{n,N})\,
   \Pr_{\sigma_n}(\text{joint entry at }t_n)
 \ge\lambda\rho.
\tag{4.3}
\]

The shifted pure-time payoff gap is multiplied by the opponents-only survival
through \(W_{n,N}\).  That survival dominates joint survival, so

\[
 g(W_{n,N})\ge c(W_{n,N})g_0\ge\lambda D_*/8.
\tag{4.4}
\]

Finally, exact floor prefixing makes every semantic-debt coordinate
nonincreasing.  Global minimality gives, uniformly in the word and its depth,

\[
 D_*\le D(W_{n,N}\star\sigma_n)\le D(\sigma_n).
\tag{4.5}
\]

Thus arbitrarily deep shifted rows co-realize:

* total debt tending uniformly to \(D_*\);
* a fixed positive actual joint-entry floor \(\lambda\rho\);
* a fixed positive pure-time paid gap \(\lambda D_*/8\);
* literal source support of the selected source witness; and
* an exact punishment-floor Nash--Bellman word before the row.

This removes vanishing pre-row reach as an explanation for failure of the
summable exact port.

### 4.1 A uniformly paid whole-strategy fork after the exact word

There is a stronger executable consequence.  Apply the checked scratch
common-prefix fork to \(\sigma_n\) with \(\Delta=D_*/2\).  It gives a
unilateral stopping-law replacement \(\tau_{n,p}\) such that

\[
 U_p(\tau_{n,p},\sigma_{n,-p})-U_p(\sigma_n)
 \ge {D_*^2\over64M},
\tag{4.6}
\]

and the replacement is literally equal to \(\sigma_{n,p}\) at every date
strictly before its selected row start \(t_n\).

Lift the same replacement behind a compatible same-source certificate
\(W_{n,N}\): player \(p\) uses its prescribed \(W_{n,N}\)-actions through
the word and then uses
\(\tau_{n,p}\); every opponent is unchanged.  The source and target profiles
are identical through date \(N+t_n\).  Every terminal contribution before
the end of \(W_{n,N}\) cancels, so the whole-profile gain is exactly

\[
 c(W_{n,N})
 \bigl[U_p(\tau_{n,p},\sigma_{n,-p})-U_p(\sigma_n)\bigr]
 \ge \lambda {D_*^2\over64M}.
\tag{4.7}
\]

Thus, for each sufficiently late source and each compatible depth, the
packet contains a **source-indexed actual behavioral replacement** of fixed
positive gain, not merely a counterfactual pure-time comparison.
The mover's unrestricted cap is unchanged, and its debt falls by exactly the
gain.  What is not controlled is the other three players' cap leakage or the
target's total debt.  Consequently (4.7) lands exactly at the familiar split:
a minimum-fibre response handoff, where finite support descent may apply, or
a strict off-minimum paid target.

## 5. Why this is not the post-mark two-cut producer

In the played chronology of

\[
 q_{N-1}\star\cdots\star q_0\star\sigma_n,
\tag{5.1}
\]

all newly exact roots occur **before** the shifted paid row.  The current
two-cut packet instead asks for

\[
 \text{marked row}<\text{entry cut}<\text{exit cut},
\tag{5.2}
\]

with positive hazard and near-minimum/Nash control after the mark.  The
outward prefix construction has the opposite orientation.

The whole-strategy fork (4.7) fixes agency but not this orientation.  It is a
unilateral change first occurring after a long exact prefix; it does not make
the rows after that first disagreement exact Nash--Bellman roots, and its
receiving profile need not remain near the minimum fibre.  Treating the
replacement as the next play segment would therefore confuse a horizontal
strategy edge with temporal play.

The supported source pure time does not repair this.  Support means its atom
in the player's marginal stopping law is positive.  It gives neither a
uniform atom floor nor opponent survival from the first-disagreement start to
that later source time.  In particular, it does not make a later suffix
near-minimum or Nash--Bellman exact.

There is a sharp local reason.  A paid pure-time comparison may occur at a
date at which another player quits surely.  The comparison is then fully
screened from every later continuation, which can be replaced arbitrarily
without changing the paid row.  Punishment-floor safety alone does not rule
this out.  In the strict-curl regression, set \(d=1\) and replace the third
player's reward by zero.  Use the exact row \(X\to E\): its mover receives its
maximal reward one at \(E\); the observer's punishment is zero because all
opponents can Never; and the remaining two players have identically zero
reward.  Thus \(E\) is all-player floor-safe and carries a unit paid row,
while two players quit surely at date zero and the post-row tail is
unreachable and unconstrained.  This is only an interface regression, not a
positive-minimum counterexample.

Therefore no theorem using only the uniform pre-row fields above can infer a
post-mark block.

## 6. What remains mathematically live

The new packet leaves one much narrower issue:

\[
 \boxed{
 \begin{array}{c}
 \text{cofinally deep, uniformly reached, near-minimum paid rows}\
 +\ \text{exact Nash--Bellman ancestry before each row}
 \end{array}
 \Longrightarrow
 \begin{array}{c}
 \text{a later near-minimum/Nash cut,}\
 \text{a charged return, or a renewable child.}
 \end{array}}
\tag{6.1}
\]

Any proof must use the positive-minimum source ancestry or a nonlocal return
account.  It cannot follow from the local row, its support atom, or its
post-row tail alone.

The current output does not contain any of the following post-mark fields:

* a later pair of cuts in the same literal continuation;
* a positive hazard floor between those cuts;
* near-minimum semantic control of the exit suffix;
* exact Nash--Bellman control after the marked row; or
* renewable reconstruction of the receiving profile as a child source.

Law-enriched compactification alone does not create them.  A uniformly
reached feature may move to unbounded dates while the project's
date-forgetting terminal coalition law remains constant; in particular this
does **not** imply positive `Never` mass in the limiting terminal law.  Any
successful next step must manufacture a literal downstream block in the
same source continuation, or use a consumer which does not require such a
block.

## 7. Sources inspected and Lean boundary

Named checked inputs:

* `QuittingTerminalExploitabilityWitness.exactFloorRoot_quitProbability_lt_one`
  (whose proof uses the explicit stronger quit-probability bound);
* `QuittingTerminalExploitabilityWitness.prefixCharge_le`;
* `QuittingPunishmentFloorInfiniteOrbit.debt_antitone`;
* literal paid-row shift and opponent-survival scaling in
  `PaidCapLiftedSummablePort.lean`; and
* the scratch declarations
  `positiveDebt_exists_actualJointReach_paidFirstDisagreementRow` and
  `positiveDebt_exists_actualJointReach_paidRow_withSupport`; and
* `positiveDebt_exists_commonPrefix_profitableStoppingLawFork` in
  `fable/lean/FableCommonPrefixFork.lean`.

The uniform product estimate (3.3) and its composition (4.3)--(4.5) are
ordinary mathematics and are not claimed to be packaged as Lean
declarations.  The scratch actual-reach declarations are kernel-checked in
the conference lane but not production imports.
