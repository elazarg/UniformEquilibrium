# Review of structured paid-source one-stage root classification

Reviewer: `CODEX_SPINOZA`

Reviewed note:
`notes/CODEX_NEGATIVE_CERTIFICATE__STRUCTURED_PAID_SOURCE_ONE_STAGE_ROOT_CLASSIFICATION.md`

Reviewed exact SHA256:
`f46c2456860a0fc744eb15ccd79cd4a525e23dada28748e67096491c0a133622`

## Verdict

**PASS.**  I independently reconstructed the exact prefix-debt estimates,
the five-bucket Fin4 concentration argument, product-law purification, root
complementarity, the complete-cap upgrade at the pure paid-player boundary,
and the uniformization over all exact root selections.  I found no missing
case or source-hypothesis mismatch.

This is an ordinary-mathematics review.  I checked that the named Lean
declarations have the claimed types under their imports; I did not formalize
the new compactness argument in Lean.

## Claim checked

For the reviewed structured stationary source sequence
`X_n=(u_n,B_n)`, the paid player `b` has a fixed debt
`d_{n,b}≥γ>0`, its cap coordinate converges to the singleton reward
`B_{n,b}→s_b`, the global terminal-semantic debt floor is
`D_*>0`, and every exact product Nash root against the literal payoff
`u_n` has a common positive absorption floor.  The note claims a uniform
`δ>0` such that every sufficiently late exact root spends at least
`δ` of actual total semantic debt after literal prefixing.

## Reconstruction

Let `e_n=D(X_n)-D(Prefix(q_n,X_n))`.  Exact prefixing
weakly decreases every coordinate debt.  The checked inequalities in
`TerminalSemanticFinFourOffMinimumChargedBlockerGate.lean` give

\[
 D_*\operatorname{Coll}(q_n)\le e_n
\]

and, for `j≠k`,

\[
 \mu_{q_n}(\{k\})d_{n,j}\le e_n.
\]

If `e_n→0`, positivity of `D_*` kills collision mass.  Taking
`j=b` and using `d_{n,b}≥γ` kills every singleton bucket
`{k}` with `k≠b`.  Since collision mass plus the four singleton
masses is exactly root absorption and absorption has a common positive
floor, a positive amount of mass remains on (\{b\}).

For each `j≠b`, positivity of `μ({b})` permits the exact
product ratio

\[
 {\mu(\{b,j\})\over\mu(\{b\})}
 ={q_j\over1-q_j}.
\]

The numerator is collision mass, hence `q_{n,j}→0`.  Meanwhile the paid
source pins imply

\[
 \limsup u_{n,b}\le s_b-\gamma.
\]

Thus the paid player's Quit-minus-Continue endpoint difference in the
`u_n`-tail root is eventually strictly positive.  The surviving singleton
mass gives `q_{n,b}>0`; exact binary complementarity then rules out
`q_{n,b}<1`, so `q_{n,b}=1` eventually.

At that boundary all outsiders remain screened by the sure quitter `b`,
even under their unilateral behavioral replacements.  Their exact root
inequalities are therefore unchanged when the tail vector is replaced by
the complete cap `B_n`.  Only `b`'s Continue deviation can expose the
tail.  Its exact extra defect is

\[
 \zeta_n=
 [C_b(q_{n,-b};B_{n,b})-Q_b(q_{n,-b})]_+.
\]

Because `q_{n,-b}→0` and `B_{n,b}→s_b`, both endpoints converge
to `s_b`, hence `ζ_n→0`.  The root is consequently a
`ζ_n`-Nash root against the actual continuation best-response vector.
`isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash`
then makes the literal root/source splice a terminal
`ζ_n`-equilibrium against unrestricted behavioral deviations.  Its
law converges to singleton `{b}`, so its payoff converges to the fixed
vector `r({b})`.  This contradicts the stored positive terminal gap.

Finally, failure of a uniform `δ,N` would permit a diagonal selection
of indices `n_m≥m` and exact roots with drop below `1/m`, reproducing
the forbidden zero-drop sequence.  The quantifier upgrade to every late root
selection is valid.

## Source and declaration audit

The staged-and-promoted tropical packet supplies the needed fixed label after
subsequence selection, the exact cap-attaining Quit0 gain, vanishing source
hazards, and the cluster pin (B_b(y)=s_b).  Boundedness plus equality of
every cluster coordinate yields `B_{n,b}→s_b`.  Section 8 of
`CODEX_SPINOZA__STRUCTURED_STATIONARY_PAID_PORT_EXACTIFICATION_BARRIER.md`
does give a root-absorption lower bound uniform over every exact root
selection, not merely one selected equilibrium.

The three debt-drop declarations named by the author occur in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourOffMinimumChargedBlockerGate.lean`
with the required complete terminal-semantic meanings.  The first-branch
compiler occurs in `UniformEquilibrium/Quitting/Root/FirstBranch.lean` and
requires precisely a sure quitter plus root Nash against
`quittingContinuationBestResponse`; the cap-tail calculation supplies
those hypotheses.  The positive terminal gap supplies a debt coordinate at
least the gap for every actual profile by
`QuittingTerminalExploitabilityWitness.exists_terminalGap_le_terminalSemanticDebt`.

## Boundary checks

- Without `D_*>0`, collision mass is not charged and a mixed absorbing
  root is possible; the author's qualification is necessary.
- Without the fixed `b`-debt, singleton concentration may select a
  different owner.
- Without `B_{n,b}→s_b`, the pure-`b` root retains an unscreened
  Continue-then-tail defect.
- A sure quitter alone does not screen its own deviation; the explicit
  `ζ_n` calculation is essential and is present.
- The product ratio is not valid for correlated coalition laws; the note
  correctly restricts the theorem to independent product roots.

No objection remains.
