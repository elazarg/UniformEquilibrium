# Passive padding excludes universal exact periodic certificates in Fin4

Authors: CODEX_SPINOZA

Independent reviews:
[CODEX_NEGATIVE_CERTIFICATE](../feedback/CODEX_SPINOZA__PERIODIC_COMPLEMENTARITY_AND_PASSIVE_PADDING_NO_GO__BY_CODEX_NEGATIVE_CERTIFICATE.md)
and
[CODEX_SNELL](../feedback/CODEX_SPINOZA__PERIODIC_COMPLEMENTARITY_AND_PASSIVE_PADDING_NO_GO__BY_CODEX_SNELL.md)

## Exact statement

Let \(G=(I,r)\) be a finite zero-Never quitting game. At every live date,
players independently Quit or Continue; the first nonempty quitting coalition
\(S\) terminates play with payoff \(r(S)\), and infinite play pays zero.
Unilateral deviations range over all behavioral strategies, including Never
and arbitrarily late quitting.

Choose \(H_i\) such that

\[
r_i(S)\le H_i
\quad(i\in I,\ \varnothing\ne S\subseteq I),
\tag{1}
\]

and choose \(P>0\). Add one dummy \(d\), with padded reward

\[
\widehat r_i(T)=r_i(T\cap I),\qquad \widehat r_d(T)=0
\quad\text{if }T\cap I\ne\varnothing,
\tag{2}
\]

and

\[
\widehat r_i(\{d\})=H_i,\qquad \widehat r_d(\{d\})=-P.
\tag{3}
\]

All padded Never payoffs are zero.

**Theorem A.** For every \(K\ge1\), an exact bounded, absorbing,
punishment-admissible \(K\)-periodic Nash--Bellman cycle of \(\widehat G\)
projects, by deleting the dummy hazards, to a bounded completely absorbing
inverse iterate of \(G\).

**Theorem B.** There exists a rational Fin4 table, given by the explicit
parametric formula (17)--(18) for an existentially chosen sufficiently small
rational parameter, with no `IsQuittingBlockCertificate` of any finite
period. Hence no universal exact finite-period certificate theorem, with
period bound \(4\) or any other bound, holds for all Fin4 tables.

**Theorem C.** Let \(E_G(\sigma)\) be literal terminal exploitability against
all unilateral behavioral deviations. In this theorem specialize to the
canonical endpoints and width

\[
L_i=\min\left(0,\min_{\varnothing\ne S\subseteq I}r_i(S)\right),\qquad
H_i=\max\left(0,\max_{\varnothing\ne S\subseteq I}r_i(S)\right),\qquad
W=\max_{i\in I}(H_i-L_i).
\]

Every padded profile \(\widehat\sigma\) then has
an old live-root projection, and every old profile has a quiet lift, with

\[
E_G(\operatorname{project}\widehat\sigma)
 \le\left(1+\frac WP\right)E_{\widehat G}(\widehat\sigma),
\qquad
E_{\widehat G}(\operatorname{quiet}\sigma)\le E_G(\sigma).
\tag{4}
\]

Both operations preserve every literal period of the live hazard word.

Theorem B uses only the bounded correction of Solan (2001), Theorem 2.1.
No claim about a quantitative period-versus-error rate is used.

## Conjecture-facing change

The question
[FIN4 approximate forward packet or capacity barrier](../archive/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md)
uses approximate periodic profiles after producing a long charged packet. A
tempting stronger route was universal existence of an exact consumer-ready
periodic cycle, perhaps of period at most four. Theorem B removes that route:
one rational Fin4 table has no such exact cycle of any finite period.

This does not decide
[FIN4 direct decision](../archive/FIN4_DIRECT_DECISION.md). A gap restricted
to periodic profiles is a listed nonanswer there. The packet instead proves
that exact finite periodicity cannot be the exhaustive direct producer;
tolerance-dependent forward packets or a genuinely nonperiodic mechanism
remain necessary.

## Definitions and assumptions

For \(q\in[0,1]^I\), define

\[
c(q)=\prod_{i\in I}(1-q_i),\qquad
P_q(S)=\prod_{i\in S}q_i\prod_{i\notin S}(1-q_i),
\tag{5}
\]

and

\[
F_q(z)=\sum_{\varnothing\ne S\subseteq I}P_q(S)r(S)+c(q)z.
\tag{6}
\]

Let \(Q_i(q_{-i})\) be player \(i\)'s payoff when it Quits surely, and
\(C_i(q_{-i},z_i)\) its payoff when it Continues surely and the
all-opponents-Continue outcome pays \(z_i\). Put

\[
g_i(q,z_i)=Q_i(q_{-i})-C_i(q_{-i},z_i).
\tag{7}
\]

A length-\(K\) cyclic complementarity solution has
\(q^k\in[0,1]^I\), \(z^k\in\mathbb R^I\), indexed modulo \(K\), with

\[
z^k=F_{q^k}(z^{k+1}),
\tag{8}
\]

\[
q_i^k g_i(q^k,z_i^{k+1})\ge0,\qquad
(1-q_i^k)g_i(q^k,z_i^{k+1})\le0.
\tag{9}
\]

It is absorbing if some \(c(q^k)<1\), and punishment-admissible if every
player \(i\) satisfies

\[
\prod_{k=0}^{K-1}c(q^k\text{ with }q_i^k=0)<1
\quad\text{or}\quad r_i(\{i\})\ge0.
\tag{10}
\]

Together with cyclic closure and the finite reward box, (8)--(10) are the
ordinary-mathematics fields of `IsQuittingBlockCertificate`.

For Theorem C,

\[
E_G(\sigma)=\max_i\sup_{\tau_i}
\bigl(\gamma_i(\tau_i,\sigma_{-i})-\gamma_i(\sigma)\bigr)_+,
\tag{11}
\]

with the supremum over all behavioral replacements. Projection reads the
actual old-player live roots; quiet lift appends dummy Never.

## Source correspondence

`IsQuittingBlockCertificate` and
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` are in
[`BlockPeriodicProfile.lean`](../../../UniformEquilibrium/UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean).
The cyclic response comparison is
`quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_admissible` in
[`AdmissibleCycleTerminalEquilibrium.lean`](../../../UniformEquilibrium/UniformEquilibrium/Quitting/Cycles/AdmissibleCycleTerminalEquilibrium.lean).

The padding reward, live-root projection, and quiet lift are in
[`PassivePlayerPadding.lean`](../../../UniformEquilibrium/UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean)
and
[`PassivePlayerPaddingRetraction.lean`](../../../UniformEquilibrium/UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingRetraction.lean).
The exploitability inequalities in Theorem C are in
[`AKRSReverseS3Hardness.lean`](../../../UniformEquilibrium/UniformEquilibrium/Quitting/Classification/Existence/AKRSReverseS3Hardness.lean)
and
[`PassivePlayerPaddingExploitabilityRetraction.lean`](../../../UniformEquilibrium/UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean).

The inverse-iterate definitions are `IsQuittingInverseIterate`,
`IsCompletelyAbsorbing`, and
`NoBoundedCompletelyAbsorbingInverseIterate` in
[`UnboundedInverseIterate.lean`](../../../UniformEquilibrium/UniformEquilibrium/Quitting/Boundary/Analytic/UnboundedInverseIterate.lean).
That file checks the homogeneous-boundary defect but does not prove the
bounded Solan no-go.

The literature input is E. Solan, *The Dynamics of the Nash Correspondence
and n-Player Stochastic Games*, International Game Theory Review 3 (2001),
Theorem 2.1. The
[image-checked transcription](../../literature/SOLAN_2001__CLEANED_TEXT.md)
records the exact mismatch: the paper states nonexistence of every completely
absorbing inverse iterate, but its convex-hull step requires bounded values.
The literal unbounded statement is false; the remainder of the proof
establishes the bounded form. This packet uses only that bounded form, and a
finite-period value word is automatically bounded.

The new content is Theorem A's projection of exact cyclic Bellman and
complementarity data through the dummy boundary, especially the sure-Quit
case. The checked profile-level retraction does not state this inverse-iterate
projection.

## Proof

Let a padded exact \(K\)-cycle be given. Write

\[
\widehat q^k=(p^k,x_k),\qquad
A_k=\prod_{i\in I}(1-p_i^k),\qquad
A_{k,-i}=\prod_{j\ne i}(1-p_j^k).
\tag{12}
\]

Let \(v_i^k\) be the old displayed values and \(w^k\) the dummy value.

### Dummy contraction and zero dummy-only mass

At \(d\), the second admissibility alternative is
\(0\le\widehat r_d(\{d\})=-P\), which is false. Thus the first alternative is

\[
A:=\prod_{k=0}^{K-1}A_k<1.
\tag{13}
\]

This is old-opponent contraction, not merely full-profile absorption.

The padded cycle is absorbing. Cyclic Bellman equality therefore identifies
its displayed values with the terminal-value mixture. Dummy terminal rewards
are \(0\) or \(-P\), so \(w^k\le0\).

If the dummy switches to Never, (13) makes its old opponents absorb almost
surely, and every reached terminal coalition pays it zero. Its refusal value
is zero. For the exact checked comparison, convert the certificate with
`isQuittingCyclicContinuationBlock_of_isQuittingBlockCertificate`, identify
the displayed values with cyclic terminal values by
`eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing`, and
apply `quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_admissible`
to the identically-Never dummy hazard at each cyclic rotation. Hence
\(w^k\ge0\), so \(w^k=0\).

The dummy Bellman equation becomes

\[
0=-P x_kA_k+(1-x_k)A_k\,0,
\]

and therefore

\[
x_kA_k=0\qquad(k=0,\ldots,K-1).
\tag{14}
\]

### Old Bellman and complementarity equations

For every old \(i\), conditioning on whether the old quitting part is empty
gives

\[
F^{\widehat G}_{(p^k,x_k),i}(v^{k+1})
=
F^G_{p^k,i}(v^{k+1})
+x_kA_k(H_i-v_i^{k+1}).
\tag{15}
\]

The correction vanishes by (14), so old Bellman equality survives.

Forcing old player \(i\) to Quit makes the old part nonempty, hence its Quit
endpoint is unchanged. The padded Continue endpoint has one extra dummy-only
branch. Thus

\[
g_i^G
=
g_i^{\widehat G}
+x_kA_{k,-i}(H_i-v_i^{k+1}).
\tag{16}
\]

The old displayed value is a mixture of old rewards bounded above by \(H_i\)
and the dummy-only reward \(H_i\), so \(v_i^{k+1}\le H_i\).

If \(p_i^k<1\), then
\(0=x_kA_k=x_k(1-p_i^k)A_{k,-i}\) implies
\(x_kA_{k,-i}=0\). The gaps coincide and both complementarity clauses pass.
If \(p_i^k=1\), the projected Continue clause is vacuous. The padded Quit
clause gives \(g_i^{\widehat G}\ge0\), and (16) adds a nonnegative correction,
so the projected Quit clause passes. No division by \(1-p_i^k\) occurs.

The projected values inherit the finite box. By (13), survival after \(n\)
turns is \(A^n\to0\). Repeating the projected word gives a bounded completely
absorbing inverse iterate. This proves Theorem A.

### Rational Fin4 family

Solan's integer-scaled three-player table \(G_\varepsilon\) has rewards

\[
\begin{array}{c|c}
S&r(S)\\ \hline
\{1\}&(1,3,0)\\
\{2\}&(0,1,3)\\
\{3\}&(3,0,1)\\
\{1,2\}&(1+\varepsilon,0,1)\\
\{1,3\}&(0,1,1+\varepsilon)\\
\{2,3\}&(1,1+\varepsilon,0)\\
\{1,2,3\}&(0,0,0).
\end{array}
\tag{17}
\]

For every sufficiently small positive \(\varepsilon\), the bounded content
of Solan's Theorem 2.1 excludes bounded completely absorbing inverse
iterates. Choose rational \(\varepsilon\) in that interval and below \(2\).
Rational density supplies it, but the source gives no numerical threshold.

Every coordinate in (17) is at most \(3\). Add \(d\) by (2) and set

\[
\widehat r(\{d\})=(3,3,3,-1).
\tag{18}
\]

This proves existence of a rational Fin4 table given by an explicit
parametric formula, not a numerically isolated table. Any finite
`IsQuittingBlockCertificate` would contradict Theorem A and the bounded
Solan no-go. This proves Theorem B.

### Approximate projection and quiet lift

The checked retraction and quiet-lift theorems give (4). Projection restricts
each live hazard row to old coordinates; quiet lift appends the constant zero
dummy hazard. Hence both preserve a \(K\)-periodic word.

For (17), \(W=3\) and \(P=1\), so

\[
E_{G_\varepsilon}(\operatorname{project}\widehat\sigma)
\le4E_{\widehat G_\varepsilon}(\widehat\sigma).
\tag{19}
\]

If \(e_K(G)\) is the infimum of exploitability over all \(K\)-periodic
behavioral profiles, then

\[
\frac14e_K(G_\varepsilon)
\le e_K(\widehat G_\varepsilon)
\le e_K(G_\varepsilon).
\tag{20}
\]

Equivalently, let \(d_G(\delta)\) be the least \(K\ge1\) for which a
\(K\)-periodic profile of exploitability at most \(\delta\) exists, and put
\(d_G(\delta)=+\infty\) if there is none. Then

\[
d_{G_\varepsilon}(4\delta)
\le d_{\widehat G_\varepsilon}(\delta)
\le d_{G_\varepsilon}(\delta).
\tag{21}
\]

Thus every padded \(\delta_n\)-periodic family with \(\delta_n\to0\) projects
to an old \(4\delta_n\)-approximate family with the same period, while every
old approximate periodic profile quiet-lifts without error or period loss.

Solan's Theorem 2.2 claims divergence of the old minimal periods as error
vanishes. It gives no rate, does not formally define “periodic
\(\delta\)-equilibrium,” and its sketch has known gaps. Neither that
divergence nor a rate is claimed here. The sound theorem is the checked
sandwich (19)--(21). This proves Theorem C.

## Boundary tests

1. **Penalty.** \(P>0\) is essential. At \(P=0\), the dummy can use the
   nonnegative-solo admissibility branch, so (13) need not follow.
2. **Admissibility.** Full-cycle absorption alone is insufficient: a
   dummy-only absorbing phase can leave every old hazard zero.
3. **Upper endpoint.** The sure-Quit case needs
   \(v_i^{k+1}\le H_i\); canonical padding supplies it.
4. **Sure Quit.** For \(p_i^k<1\), the correction in (16) vanishes. For
   \(p_i^k=1\), it may remain, but has favorable sign and the Continue clause
   is vacuous.
5. **Unbounded values.** Solan's literal theorem fails for an unbounded
   inverse iterate. Periodic repetition is bounded, so only the corrected
   bounded theorem is used.
6. **Zero perturbation.** At \(\varepsilon=0\), the Flesch mechanism has an
   exact period-three cycle. The small positive perturbation is essential.
7. **Positive controls.** Other Fin4 tables in the repository have exact
   period-three and period-four admissible certificates. Theorem B is
   table-specific.
8. **Approximate control.** Old approximate periodic equilibria quiet-lift,
   so Theorem B does not create a positive all-profile exploitability gap.
9. **Strategy class.** A local approximate root packet must first compile to
   terminal behavioral exploitability before Theorem C applies.

## Adapter and consumer

The actual-data adapter is canonical one-dummy padding. Starting from (17),
`quittingPassivePaddingReward` with one fresh player, upper endpoint
\(H=(3,3,3)\), and penalty \(1\) gives (18).

The contradiction consumer is
`NoBoundedCompletelyAbsorbingInverseIterate`: Theorem A maps a hypothetical
padded certificate to the forbidden old object.
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` independently
confirms that the excluded input is the consumer-ready unrestricted
behavioral certificate class.

At positive error, the checked consumers are
`QuittingPayoffTable.oneDummyPadding_project_exploitability_le` and
`quittingTerminalExploitability_passivePaddingQuietProfile_le`. They retain
all-behavior deviation power and preserve the period word through checked
live-root identities.

## Lean handoff

Use `IsQuittingBlockCertificate`,
`isQuittingCyclicContinuationBlock_of_isQuittingBlockCertificate`,
`eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing`,
`quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_admissible`,
the old/fresh reward identities for `quittingPassivePaddingReward`, and
`IsQuittingInverseIterate` with the survival-prefix lemmas.

The narrow theorem shape is:

```text
IsQuittingBlockCertificate
  (quittingPassivePaddingReward oldReward upper penalty) hazard U
→ ∃ rows values M,
    (∀ t i, |values t i| ≤ M) ∧
    IsQuittingInverseIterate oldReward rows values ∧
    IsCompletelyAbsorbing rows
```

under \(P>0\) and (1). Define rows and values by periodic projection. Prove:
dummy deleted-cycle contraction; dummy refusal zero; \(w^k=0\);
\(x_kA_k=0\); (15); then the two cases of (16).

The Solan bounded no-go is a literature dependency and must not be encoded as
an axiom or assumed structure field. Theorem C is already checked except for
an optional small periodicity-preservation wrapper.

## Scope and nonclaims

- Theorem B is existential within an explicit rational parametric family; no
  numerical rational perturbation is isolated.
- It excludes exact finite absorbing punishment-admissible Nash--Bellman
  certificates, not nonadmissible exact cycles.
- It excludes neither approximate cycles, growing periods, nonperiodic
  profiles, nor uniform-equilibrium payoffs.
- It gives no all-behavior positive exploitability gap and does not decide
  Fin4 directly.
- It does not prove or repair Solan's Theorem 2.2 and gives no
  period-versus-error rate.
- The bounded Solan theorem is literature mathematics, not a checked
  declaration in `UnboundedInverseIterate.lean`.
- Theorem A is ordinary mathematics awaiting Lean formalization; no `L`,
  `A`, or `C` seal is claimed.
