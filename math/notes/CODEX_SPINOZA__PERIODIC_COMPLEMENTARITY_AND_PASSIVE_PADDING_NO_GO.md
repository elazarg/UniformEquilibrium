# Periodic complementarity and a passive-padding no-go in four players

Identity: CODEX_SPINOZA

Status: **proved ordinary-mathematics projection theorem; literature-dependent
four-player counterexample to every exact finite-period admissible
Nash--Bellman producer.**  The projection theorem is not Lean-checked.  Its
input and output match named checked definitions, and every boundary case is
spelled out below.  The final counterexample uses the bounded correction of
Solan (2001), Theorem 2.1; that source theorem is not a checked Lean
declaration.  Independent mathematical reviews:
[`CODEX_NEGATIVE_CERTIFICATE`](../feedback/CODEX_SPINOZA__PERIODIC_COMPLEMENTARITY_AND_PASSIVE_PADDING_NO_GO__BY_CODEX_NEGATIVE_CERTIFICATE.md)
and
[`CODEX_SNELL`](../feedback/CODEX_SPINOZA__PERIODIC_COMPLEMENTARITY_AND_PASSIVE_PADDING_NO_GO__BY_CODEX_SNELL.md),
both PASS.  The twice-delta-checked packet is frozen at
[`PASSIVE_PADDING_PERIODIC_CERTIFICATE_NO_GO.md`](../exports/PASSIVE_PADDING_PERIODIC_CERTIFICATE_NO_GO.md),
SHA-256 `47188fbd995d586305ff52a768808d99c78628a73d21a24465f5a07db0b23edd`.

Current consequence: there is a rational four-player quitting table that has
no consumer-ready exact absorbing periodic Nash--Bellman cycle of **any**
finite period.  Thus neither a universal period bound (periods 2--4 included)
nor universal existence of an exact finite-period certificate can close
Fin4.  This is not a counterexample to uniform equilibrium: the underlying
three-player Solan game has a uniform-equilibrium payoff, and passive padding
preserves approximate-equilibrium existence.

## 1. Exact question

For a finite player set (I), a zero-Never quitting reward (r), and a
hazard row (q\in[0,1]^I), put

\[
 c(q)=\prod_{i\in I}(1-q_i),\qquad
 P_q(S)=\prod_{i\in S}q_i\prod_{i\notin S}(1-q_i).
\]

The Bellman map is

\[
 F_q(z)=\sum_{\varnothing\ne S\subseteq I}P_q(S)r(S)+c(q)z.
\]

For player (i), let (Q_i(q_{-i})) be the expected payoff when (i)
Quits surely, and let (C_i(q_{-i},z_i)) be the expected payoff when (i)
Continues surely and the all-opponents-Continue outcome pays (z_i).  Write

\[
 g_i(q,z_i)=Q_i(q_{-i})-C_i(q_{-i},z_i).
\]

A length-(K) cyclic complementarity solution consists of

\[
 q^k\in[0,1]^I,\quad z^k\in\mathbb R^I,\qquad k\in\mathbb Z/K\mathbb Z,
\]

satisfying

\[
 z^k=F_{q^k}(z^{k+1}),                                      \tag{1.1}
\]

\[
 q_i^k g_i(q^k,z_i^{k+1})\ge0,\qquad
 (1-q_i^k)g_i(q^k,z_i^{k+1})\le0.                           \tag{1.2}
\]

The consumer-ready version also requires positive absorption in a phase and,
for every player (i),

\[
 \prod_k c(q^k\text{ with }q_i^k=0)<1
 \quad\hbox{or}\quad r_i(\{i\})\ge0.                       \tag{1.3}
\]

These are exactly the ordinary-mathematics contents of
`IsQuittingBlockCertificate`: (1.1) is `succ`, (1.2) is `gain`, positive
absorption is `absorb`, and (1.3) is `admissible`.  The displayed value box
and cyclic closure are also retained.  The checked theorem
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` consumes this
object against unrestricted behavioral deviations.

The question tested here is whether every four-player table has such an
object with (K\le4), or at least with some uniformly bounded (K).

## 2. Canonical one-dummy padding

Let (G=(I,r)) be any zero-Never quitting game.  Choose (H_i) with

\[
 r_i(S)\le H_i\quad(\varnothing\ne S\subseteq I),            \tag{2.1}
\]

and choose a penalty (P>0).  Add one dummy (d).  Define the padded reward
\(\widehat r\) by

\[
 \widehat r_i(T)=r_i(T\cap I),\quad \widehat r_d(T)=0
 \quad\text{if }T\cap I\ne\varnothing,                     \tag{2.2}
\]

and

\[
 \widehat r_i(\{d\})=H_i,qquad \widehat r_d(\{d\})=-P.     \tag{2.3}
\]

All Never payoffs are zero.  This is the one-new-player instance of
`quittingPassivePaddingReward`; with canonical coordinatewise extrema it is
the normalized reward in `QuittingPayoffTable.oneDummyPadding`.

## 3. Projection theorem

**Theorem 3.1 (an admissible padded cycle projects to a bounded absorbing
inverse iterate).**  If the padded game \(\widehat G\) has a finite-period
cycle satisfying (1.1)--(1.3), cyclic closure, and the finite value box, then
the old game (G) has a bounded completely absorbing inverse iterate.

More precisely, if the padded phase hazard is

\[
 \widehat q^k=(p^k,x_k),\qquad p^k\in[0,1]^I, x_k\in[0,1],
\]

then deleting the dummy hazards and repeating the rows (p^k) periodically
gives the inverse iterate.  The old coordinates of the displayed padded
values are its values.

### Proof

Write

\[
 A_k=c(p^k)=\prod_{i\in I}(1-p_i^k),\qquad
 A_{k,-i}=\prod_{j\ne i}(1-p_j^k).                          \tag{3.1}
\]

Let (v_i^k) be the old displayed coordinates and (w^k) the dummy
coordinate.

**Step 1: old players absorb over each turn.**  The dummy's solo payoff is
(-P<0).  Therefore its second admissibility disjunct is false, and (1.3)
at (d) gives

\[
 A:=\prod_{k=0}^{K-1}A_k<1.                                \tag{3.2}
\]

This is the key use of consumer admissibility.  Positive absorption of the
full padded cycle alone would not imply (3.2), since the dummy could have
caused all absorption.

**Step 2: the dummy has value zero and never absorbs alone.**  Dummy rewards
are either (0) or (-P).  Since (3.2) also makes the full padded cycle
absorbing, the cyclic Bellman solution is its terminal-value mixture.  Hence

\[
 w^k\le0.                                                   \tag{3.3}
\]

On the other hand, the dummy can deviate to Never.  Against the old hazards
this deviation absorbs almost surely by (3.2), and every old-containing
terminal coalition pays the dummy zero.  Its refusal value is therefore
zero.  Here is the exact checked route for comparing it with the prescribed
value: convert the certificate with
`isQuittingCyclicContinuationBlock_of_isQuittingBlockCertificate`, identify
the displayed values with cyclic terminal values using
`eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing`, and
apply
`quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_admissible`
to the dummy's identically-Never hazard, at each cyclic rotation.  It says
that the dummy's refusal is at most its prescribed value.  Thus

\[
 w^k\ge0.                                                   \tag{3.4}
\]

This is not an appeal to a bounded-clock deviation.  From (3.3)--(3.4),
\(w^k=0\) for every phase.  The dummy Bellman equation is then

\[
 0=-P x_kA_k+(1-x_k)A_k\,0,
\]

so

\[
 x_kA_k=0\qquad\text{for every }k.                          \tag{3.5}
\]

**Step 3: old Bellman equations survive deletion.**  For an old coordinate
(i), (2.2)--(2.3) give the exact identity

\[
 F^{\widehat G}_{(p^k,x_k),i}(v^{k+1})
 =F^G_{p^k,i}(v^{k+1})+x_kA_k(H_i-v_i^{k+1}).               \tag{3.6}
\]

The correction is zero by (3.5), so the old coordinates obey (1.1) for the
projected rows.

**Step 4: old complementarity survives deletion, including the sure-Quit
boundary.**  For an old player (i), forcing (i) to Quit makes the old
part of the terminal coalition nonempty.  Hence its Quit endpoint is
unchanged by deleting (d).  The Continue endpoints satisfy

\[
 C_i^{\widehat G}
 =C_i^G+x_kA_{k,-i}(H_i-v_i^{k+1}),
\]

and therefore

\[
 g_i^G=g_i^{\widehat G}
       +x_kA_{k,-i}(H_i-v_i^{k+1}).                         \tag{3.7}
\]

The old displayed value is a terminal-value mixture of rewards bounded above
by (H_i), so (v_i^{k+1}\le H_i).  The correction in (3.7) is nonnegative.

If (p_i^k<1), then

\[
 0=x_kA_k=x_k(1-p_i^k)A_{k,-i}
\]

forces (x_kA_{k,-i}=0); the two gaps in (3.7) are equal and both
complementarity clauses pass verbatim.  If (p_i^k=1), the Continue-support
clause is vacuous, while the Quit-support clause passes because
(g_i^G\ge g_i^{\widehat G}\ge0).  This is precisely the boundary case that
would be missed by simply saying that dummy-only absorption has zero on-path
mass.

**Step 5: periodic repetition is bounded and completely absorbing.**  The
old values are periodic and lie in the supplied finite value box.  By
(3.2), survival after (n) turns is (A^n\to0).  Steps 3--4 are the old
Bellman and exact complementarity equations at every time.  Thus the repeated
projected word is a bounded completely absorbing inverse iterate.  QED.

## 4. A rational Fin4 table with no exact admissible cycle of any period

Take Solan's three-player perturbed game (G_\varepsilon), with Never payoff
zero and terminal table

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
\end{array}                                                \tag{4.1}
\]

For every sufficiently small positive \(\varepsilon\), the bounded form of
Solan (2001), Theorem 2.1 says that this table has no bounded completely
absorbing inverse iterate.  The paper states the theorem without the word
"bounded"; that literal statement is false.  Its proof's convex-hull step is
valid for bounded values and the remainder proves exactly the bounded form.
Finite cyclic values are automatically bounded, which is the only form used
here.

Choose a rational \(\varepsilon>0\) in the theorem's sufficiently-small
interval and also \(\varepsilon<2\).  Then (H=(3,3,3)) bounds every
coordinate in (4.1).  Add a dummy (d) with

\[
 \widehat r_i(T)=r_i(T\cap\{1,2,3\}),\quad
 \widehat r_d(T)=0
 \quad(T\cap\{1,2,3\}\ne\varnothing),                     \tag{4.2}
\]

and

\[
 \widehat r(\{d\})=(3,3,3,-1).                            \tag{4.3}
\]

This proves existence of a rational four-player quitting table given by the
explicit parametric formula (4.2)--(4.3).  It does not isolate one numerical
rational value of \(\varepsilon\), because the source gives no numerical
sufficiently-small threshold.

**Corollary 4.1.**  The table (4.2)--(4.3) has no
`IsQuittingBlockCertificate` of any finite period.

**Proof.**  Such a certificate would project by Theorem 3.1 to a bounded
completely absorbing inverse iterate of (4.1), contradicting the bounded
Solan theorem.  QED.

In particular it excludes periods (1,2,3,4) simultaneously, rather than
merely defeating a proposed uniform numerical bound.

## 5. Scope and nonclaims

1. The no-go is for **exact**, absorbing, punishment-admissible cyclic
   Nash--Bellman certificates.  It does not exclude \(\delta\)-cycles whose
   periods tend to infinity as \(\delta\downarrow0\).  Solan's Theorem 2.2
   claims this divergence for the old game, but its sketch has defects listed
   in Section 7 and is not used in Corollary 4.1.
2. It does not exclude periodic blocks lacking (1.3).  Such a block is not
   accepted by the unrestricted behavioral consumer and would not close
   Fin4.  The proof uses dummy admissibility essentially in (3.2).
3. It is not a negative result about uniform equilibrium.  Solan records that
   (G_\varepsilon) has a uniform-equilibrium payoff, and the checked passive
   padding retraction/transport results preserve the relevant approximate
   existence relation.
4. The rational \(\varepsilon\) exists by density of the rationals in the
   unspecified sufficiently-small interval.  The source supplies no explicit
   numerical threshold, so no particular rational is claimed here.
5. Theorem 3.1 is ordinary mathematics, not a newly checked Lean declaration.
   A short formalization can target the displayed identities (3.5)--(3.7).

## 6. Sources inspected

- E. Solan, *The Dynamics of the Nash Correspondence and n-Player Stochastic
  Games*, International Game Theory Review 3 (2001), Theorem 2.1 and the
  definition of a completely absorbing admissible sequence.  Local
  transcription: `literature/SOLAN_2001__CLEANED_TEXT.md`.  The boundedness
  mismatch is recorded explicitly above.
- `UniformEquilibrium/Quitting/Boundary/Analytic/UnboundedInverseIterate.lean`:
  `IsQuittingInverseIterate`, `IsCompletelyAbsorbing`,
  `NoBoundedCompletelyAbsorbingInverseIterate`, and the checked boundary-term
  diagnosis.  That file does **not** prove the Solan no-go.
- `UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`:
  `IsQuittingBlockCertificate`,
  `quittingPeriodicWindowRefusalValue_quittingBlockCycle`, and
  `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`.
- `UniformEquilibrium/Quitting/Cycles/AdmissibleCycleTerminalEquilibrium.lean`:
  `quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_admissible` and
  `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_admissible`.
- `UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean` and
  `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingRetraction.lean`,
  `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean`,
  and
  `UniformEquilibrium/Quitting/Classification/Existence/AKRSReverseS3Hardness.lean`:
  the canonical padding reward, its exact old/dummy terminal identities, its
  quiet lift, and its unrestricted exploitability retraction.
- Existing exact period-three and period-four positive constructions were
  checked as controls in
  `CODEX_NEGATIVE_CERTIFICATE__DEADLOCK_FIBER_EXACT_SCREEN.md` and
  `CODEX_NEGATIVE_CERTIFICATE__DEADLOCK_CONTINUATION_MATCHED_PERIOD_FOUR.md`.

## 7. Approximate cycles: an exact period-preserving sandwich

The exact no-go does not leave the padded table without periodic approximate
equilibria.  In fact canonical padding gives a quantitative equivalence at
the terminal behavioral interface.

For a behavioral profile \(\sigma\), write

\[
 E_G(\sigma)=\max_i\sup_{\tau_i}
 \bigl(\gamma_i(\tau_i,\sigma_{-i})-\gamma_i(\sigma)\bigr)_+
\]

for literal terminal exploitability.  Let \(\widehat G\) be the one-dummy
padding with penalty \(P>0\) and canonical upper endpoints, and let \(W\) be
the canonical old reward width.

**Theorem 7.1 (period-preserving projection and quiet lift, checked
interfaces).**

1. Every padded profile \(\widehat\sigma\) has an old live-root projection
   \(\sigma\) with

   \[
   E_G(\sigma)\le\left(1+\frac WP\right)
                  E_{\widehat G}(\widehat\sigma).           \tag{7.1}
   \]

2. Every old profile \(\sigma\) has a quiet lift
   \(\widehat\sigma=(\sigma,\mathsf{Never}_d)\) with

   \[
   E_{\widehat G}(\widehat\sigma)\le E_G(\sigma).           \tag{7.2}
   \]

3. Both maps preserve any literal \(K\)-periodicity of the live hazard word.

The inequalities are respectively
`oneDummyPadding_project_exploitability_le` and
`quittingTerminalExploitability_passivePaddingQuietProfile_le`.  Period
preservation follows directly from the checked live-root identities: the
projection restricts every row to old coordinates, and the quiet lift appends
the constant zero hazard of the dummy.  No compactness or limiting argument
is involved.

For the explicit Solan table (4.1), every reward coordinate lies in
\([0,3]\), so \(W=3\).  With \(P=1\), (7.1) becomes

\[
 E_{G_\varepsilon}(\sigma)\le4
 E_{\widehat G_\varepsilon}(\widehat\sigma).                \tag{7.3}
\]

Let \(e_K(G)\) denote the infimum of terminal exploitability over all
\(K\)-periodic behavioral profiles of \(G\).  The same word may have a
smaller minimal period; this does not affect the inequalities.  Theorem 7.1
gives the exact sandwich

\[
 \frac14 e_K(G_\varepsilon)
 \le e_K(\widehat G_\varepsilon)
 \le e_K(G_\varepsilon).                                   \tag{7.4}
\]

Equivalently, let \(d_G(\delta)\) be the least available period at terminal
error at most \(\delta\), with value \(+\infty\) if none exists.  Then

\[
 d_{G_\varepsilon}(4\delta)
 \le d_{\widehat G_\varepsilon}(\delta)
 \le d_{G_\varepsilon}(\delta).                            \tag{7.5}
\]

Thus any padded \(\delta_n\)-periodic family with \(\delta_n\to0\) projects
to a \(4\delta_n\)-approximate family of the old Solan game with exactly the
same displayed periods.  Conversely, every known old periodic approximate
equilibrium quiet-lifts with no error or period loss.  This is the requested
projection compiler: the padded family is neither a new source of bounded
periods nor a different limiting phenomenon.

Solan (2001), Theorem 2.2 claims

\[
 \liminf_{\delta\downarrow0}d_{G_\varepsilon}(\delta)=+\infty
\]

for sufficiently small fixed positive \(\varepsilon\).  Under the paper's
intended identification of its undefined "periodic \(\delta\)-equilibrium"
with the terminal behavioral notion above, (7.5) transfers the same divergence
to \(\widehat G_\varepsilon\).  The paper gives no quantitative rate, so no
period-versus-error rate is claimed here.  Moreover its published sketch of
Theorem 2.2 has known gaps (wrong game subscript and no explicit exclusion of
an all-Continue limiting word); the checked content of this section is the
profile-level sandwich (7.1)--(7.5), not the literature divergence claim.

In particular, the exact theorem and the approximate picture coexist:

- no exact finite-period admissible certificate exists;
- periodic approximate equilibria exist at every positive tolerance by the
  old three-player existence result and quiet lift; and
- subject to Solan's Theorem 2.2, their periods necessarily diverge as the
  tolerance vanishes.

## 8. Concrete next check

Independently audit Theorem 3.1, especially Step 2's cyclic refusal comparison
and Step 4's (p_i^k=1) boundary.  If it passes, the useful formal target is
the abstract implication

```text
IsQuittingBlockCertificate (oneDummyPadding reward P) hazard U
  -> exists a bounded completely absorbing inverse iterate of reward.
```

No search over periods 2--4 is then needed: the rational padded Solan table
rules out all exact finite periods at once.
