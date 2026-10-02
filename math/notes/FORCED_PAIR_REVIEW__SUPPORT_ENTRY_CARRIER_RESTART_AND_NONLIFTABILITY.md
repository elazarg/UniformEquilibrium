# Support entry gives a carrier restart, not an actual exact-root attachment

Author: FORCED_PAIR_REVIEW

## Status

The positive-absorption arm of
exists_offMinimum_retainedLaw_allContinue_or_supportEntry has two exact
consequences.

First, at the limiting joint carrier point it gives a strict semantic-debt
restart: prefixing by the newly entered exact root strictly lowers total debt,
preserves positive-debt support and normalized debt exactly, and retains every
positive terminal-law coordinate with a positive multiplicative factor.

Second, that exact root cannot be lifted to the actual maximal-ray sources
from which the limit was extracted. Maximality says that every exact root at
each prelimit cap has absorption at most the canonical maximal absorption,
and those maximal absorptions tend to zero. Thus the entered root is a
genuine upward jump of the exact-root correspondence. Prefixing it to the
actual source profiles is literal but only asymptotically Nash; it is not an
exact positive-charge chronology.

In the forced-pair setting, exposing the realizing subsequence nevertheless
allows the limit root to be prefixed literally to that subsequence. This
produces a new actual source family converging to the lower carrier point,
while retaining the shifted pair row, minimum tail, and paid mover. If the
new debt equals \(D_*\), the existing whole-source-return consumer applies.
If it remains above \(D_*\), this is a renewed off-minimum source with strictly
smaller real debt, not a well-founded rank descent.

This note is ordinary mathematics. The carrier-level ingredients and the
maximality estimates are checked; the source-facing forced-pair composition
is not represented by one Lean declaration.

## 1. Exact checked output

Let \(z_*\) be a global minimum of total terminal-semantic debt, with

\[
D_*:=D(z_*)>0.
\]

The theorem exists_offMinimum_retainedLaw_allContinue_or_supportEntry in
Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean starts from an
actual terminal profile, iterates the canonical maximal-absorption exact
cap--Nash root, and under a uniform no-return hypothesis extracts a joint
carrier point

\[
(z,\nu)\in K_r^{\mathrm{joint}}
\]

such that \(D(z)\ge D_*+\varepsilon\), one selected terminal-law coordinate
satisfies \(\nu(C)>0\), all Continue is exact Nash against \(z^B\), and either
all Continue is the unique exact root or there is an exact root \(q\) against
\(z^B\) with positive absorption.

The theorem deliberately does not return the realizing subsequence used in
its proof. It also does not claim that the support-entry root \(q\) is a
limit of exact roots at the prelimit caps.

Assume the second arm:

\[
q\in\operatorname{Nash}(z^B),
\qquad
a:=\operatorname{Abs}(q)>0.
\tag{1}
\]

Put \(c:=\operatorname{Cont}(q)=1-a\), and define

\[
z':=T_qz,
\qquad
\nu':=P_q\nu.
\tag{2}
\]

## 2. Exact carrier restart

The checked theorem quittingTerminalSemanticLawPrefix_mem_carrier in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean
gives

\[
(z',\nu')\in K_r^{\mathrm{joint}}.
\tag{3}
\]

Exact cap--Nash scaling gives

\[
d_i(z')=c\,d_i(z),
\qquad
D(z')=cD(z).
\tag{4}
\]

Global minimality and (3) imply \(D_*\le D(z')\). In particular \(c>0\),
since \(D_*>0\). Equation (1) gives \(c<1\). Consequently

\[
\boxed{D_*\le D(z')<D(z).}
\tag{5}
\]

Because \(c>0\), equation (4) also gives

\[
\operatorname{supp}^+d(z')=\operatorname{supp}^+d(z)
\tag{6}
\]

and

\[
\frac{d_i(z')}{D(z')}=\frac{d_i(z)}{D(z)}.
\tag{7}
\]

Thus support entry produces a genuine strict state change, but cannot itself
be a positive-debt-support rank descent.

For every nonempty coalition \(C\), the affine law formula is

\[
\nu'(\operatorname{some}C)
=
\operatorname{RootMass}_q(C)+c\,\nu(\operatorname{some}C).
\tag{8}
\]

Root mass is nonnegative, so

\[
\nu(C)>0\Longrightarrow \nu'(C)\ge c\nu(C)>0.
\tag{9}
\]

The retained fixed pair law therefore survives the carrier restart.

## 3. Exact minimum-return versus renewed escape

The checked theorem
capNashReturnSelection_iff_tailEscape_prefix_nearMinimum in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStrictTailEscapeReturn.lean
states, for every tolerance \(\eta\),

\[
\operatorname{ReturnSelection}(z_*,z,q,\eta)
\iff
D(z')\le D_*+\eta.
\tag{10}
\]

At zero tolerance, global minimality turns this into

\[
\operatorname{ReturnSelection}(z_*,z,q,0)
\iff
D(z')=D_*.
\tag{11}
\]

Equivalently, the support-entry root gives the exhaustive split

\[
\boxed{
D(z')=D_*
\quad\lor\quad
D_*<D(z')<D(z).
}
\tag{12}
\]

In the first arm, once the actual realizing subsequence is exposed, literal
prefixing returns the forced-pair sources to whole-source minimum debt while
retaining their pair row and minimum tail. The maintained
concentrated-collision/three-role consumer then applies.

In the second arm, the output is a strictly lower but still off-minimum joint
state. It can seed a changed-state maximal-prefix construction, but the real
number \(D(z')\) is not a well-founded rank.

## 4. Exact nonliftability on the original actual ray

Let \(P_k\) be the actual profiles on the canonical maximal-prefix ray, let
\(b_k=(\operatorname{Sem}P_k)^B\), and let \(m_k\) be the canonical
maximal-absorption exact root against \(b_k\). Write

\[
a_k:=\operatorname{Abs}(m_k).
\]

In the stall branch, checked summability gives

\[
a_k\longrightarrow0.
\tag{13}
\]

By quittingMaximalCapPrefixRoot_maximal, for every exact root \(r_k\) against
the same actual cap \(b_k\),

\[
\operatorname{Abs}(r_k)\le a_k.
\tag{14}
\]

Combining (13)--(14) proves the uniform statement

\[
\boxed{
\sup\{\operatorname{Abs}(r):
  r\in\operatorname{Nash}(b_k)\}\longrightarrow0.
}
\tag{15}
\]

In particular, if \(k_n\) is the subsequence converging to \(z\), then every
choice of actual-source exact roots
\(r_n\in\operatorname{Nash}(b_{k_n})\) satisfies

\[
\operatorname{Abs}(r_n)\to0.
\tag{16}
\]

The support-entry root \(q\) has \(\operatorname{Abs}(q)=a>0\). By
continuity of root absorption, no sequence \(r_n\) as above can converge to
\(q\). More quantitatively, eventually no exact root at \(b_{k_n}\) has
absorption at least \(a/2\).

This is an exact formalizable no-go:

\[
\boxed{
\text{the positive support-entry root at the limit cannot be lifted to
a fixed-charge exact root on the original actual ray.}
}
\tag{17}
\]

The branch is precisely a failure of lower hemicontinuity of the exact-root
correspondence. It does not directly give a positive-charge exact prefix on
the original actual sources or a source-attached admissible return.

## 5. Literal source regeneration after exposing the subsequence

Suppose actual profiles \(P_{k_n}\) converge jointly to \((z,\nu)\), and the
forced-pair data additionally retain:

* a pure pair \(C=\{j,o\}\) at dates \(t_n\);
* pair masses \(M_n\ge M_0>0\);
* literal post-pair minimum-return tails \(\sigma_n\);
* zero marked defect for \(o\); and
* a fixed mover \(p\) with whole-profile gains \(g_n\ge g_0>0\).

Define literal profiles

\[
P'_n:=q\triangleright P_{k_n}.
\tag{18}
\]

The fixed-root semantic and law prefix maps are continuous, so

\[
(\operatorname{Sem}P'_n,\operatorname{Law}P'_n)
\longrightarrow
(z',\nu').
\tag{19}
\]

The pair occurs at date \(t_n+1\), with exact mass

\[
M'_n=cM_n\ge cM_0>0.
\tag{20}
\]

The complete post-pair tail remains literally \(\sigma_n\). The marked root,
local defects, owner zero, labels, and endpoint orientation are unchanged.
Since both compared profiles share the outer root \(q\), their literal paid
payoff difference scales by the common all-Continue probability:

\[
g'_n=cg_n\ge cg_0>0.
\tag{21}
\]

The endpoint update still changes only player \(p\)'s behavioral strategy,
so its unrestricted cap against the fixed opponents is unchanged and exact
own-debt subtraction remains valid.

Thus support entry yields a lower carrier point together with an actual
pair-marked realizing family. However, \(q\) is exact only against the
limiting cap \(z^B\). At the prelimit caps its Nash defect tends to zero, but
(17) shows it cannot generally be replaced there by exact roots with
comparable absorption. Hence (18) is not an exact positive-charge chronology.

The precise field erased by the checked theorem is the causal realizing
subsequence: the profiles \(P_{k_n}\), their convergence to \((z,\nu)\),
their marked dates, and their source/tail identities. The proof internally
chooses a subsequence but returns only its cluster. A source-facing theorem
must retain that dependent subsequence before (18)--(21) can be packaged.

This erasure is materially important. A joint semantic/law point alone cannot
reconstruct the hidden tail: a pure nonsingleton root followed by two
arbitrary different tails has the same complete semantic pair and terminal
law, while its counterfactual post-root tail differs literally.

## 6. Why neither rank descent nor charged return follows

Equation (6) proves that exact support-entry prefixing preserves the entire
positive-debt support. If \(D(z')=D_*\), support-rank re-extraction is
available only with additional comparison data relative to the old minimum
source: support inclusion and disappearance of one old active coordinate.
Neither is returned by the checked cluster theorem.

In the forced-pair specialization, the marked owner zero is retained, so a
rank-four old source would give a strict exit. For an arbitrary old support
of size at most three, labels can be exchanged and no strict inclusion
follows.

The root \(q\) has positive absorption at the carrier cap, but an admissible
return needs an executable source-matched edge/path or a near-return payoff
seam. If (11) holds, the independent whole-source-return packet closes the
branch. If \(D(z')>D_*\), \(q\) merely spends part of the off-minimum excess.

Iterating carrier restarts gives a strictly decreasing bounded real sequence.
There is no uniform lower bound on subsequent support-entry absorptions, and
positive-debt support remains fixed at every exact prefix. This is not a
finite rank and does not imply recurrence.

The retained pair defect does not bound \(\operatorname{Abs}(q)\) from below.
It is a prescribed-payoff difference at the remote pure pair row; \(q\) is
selected at the outer unrestricted cap.

## 7. Maximal formalization target

The following declarations would capture the valid result:

~~~text
offMinimumSupportEntry_prefix_jointCarrier
offMinimumSupportEntry_prefix_debt_lt
offMinimumSupportEntry_prefix_positiveDebtSupport_eq
offMinimumSupportEntry_prefix_normalizedDebt_eq
offMinimumSupportEntry_prefix_retainsLawCoordinate

maximalCapPrefix_exactRoot_absorption_le
maximalCapPrefix_supportEntryRoot_not_liftable
~~~

The first group follows from
quittingTerminalSemanticLawPrefix_mem_carrier,
quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash,
quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash, and
the affine law-prefix formula. The second group follows from
quittingMaximalCapPrefixRoot_maximal,
summable_maximalCapPrefix_absorption, and continuity of root absorption.

The source-facing strengthening should return the cluster and the subsequence
and convergence proof currently hidden inside
exists_offMinimum_retainedLaw_allContinue_or_supportEntry, then specialize
fixed-root prefix transport to the forced-pair marked profiles.

## 8. Verdict

The support-entry arm is not inert. It gives a strict carrier-level debt
restart preserving the retained law atom. At zero tolerance:

\[
\boxed{
\text{whole-source minimum return}
\quad\lor\quad
\text{strictly lower off-minimum carrier restart}.
}
\]

But it does not give an actual fixed-charge exact root on the original
sources. Maximality proves that such a lift is impossible: every exact root
there has absorption tending to zero. Nor does exact prefixing change
positive-debt support.

The remaining producer is sharply localized:

> retain the causal realizing subsequence, prefix the limit-entered root
> literally, and re-exactify the changed actual sources without losing the
> fixed pair mass, minimum tail, and paid mover; or prove that the strict
> carrier restarts accumulate into a return.

This is more precise than the prior unique-all-Continue/support-entry split,
but it does not close the off-minimum ray stall.

## Sources inspected

* Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean:
  exists_offMinimum_retainedLaw_allContinue_or_supportEntry,
  quittingMaximalCapPrefixRoot_maximal,
  summable_maximalCapPrefix_absorption, and
  maximalCapPrefix_atomMass_lowerBound.
* UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean:
  exact coordinate and total cap--Nash debt scaling.
* UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean:
  joint carrier invariance and affine law prefixing.
* UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStrictTailEscapeReturn.lean:
  exact equivalence between return selection and debt-neighborhood entry.
* exports/FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md:
  the maintained forced-pair ray and its source/tail boundary.

