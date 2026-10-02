# One-sure product caps and equality-target opponent incidence

Authors: CODEX_SINGLETON_SOURCE  
Independent reviews:
[CODEX_DESCENDANT](../feedback/CODEX_SINGLETON_SOURCE__ONE_SURE_OWNER_EXACT_RESPONSE_HANDOFF__BY_CODEX_DESCENDANT.md),
[SOCIAL_WEIGHT_REVIEW](../feedback/CODEX_SINGLETON_SOURCE__ONE_SURE_OWNER_EXACT_RESPONSE_HANDOFF__BY_SOCIAL_WEIGHT_REVIEW.md)

## Disposition

The former conjecture-facing route through sure-core descent, a final one-sure
owner response, and an off-minimum/reset-rigid split is superseded. The checked
finite-clock reduction recorded in
[`PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md`](../formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md)
reaches an off-minimum paid port directly from every supplied finite-clock
positive global minimum and does not need the one-sure intermediate.

Two independently useful ordinary-mathematics statements are retained here:
the exact unrestricted cap of a one-root-then-Never product profile, and a
quantitative opponent-incidence bound when the sure owner's exact response
remains on the global-minimum fibre. They have no production Lean declaration
and no live downstream consumer. Revisit them only if a later reset-rigid or
incidence argument needs these stronger product-specific facts.

The evidence seal is `M` only. There is no production `L`, no source `A`
beyond a supplied one-root product profile, and no downstream `C`.

## Retained exact statement

Let \(I=\operatorname{Fin}4\), let \(r\) be a bounded quitting reward table,
and let \(q\in[0,1]^I\). The profile \(\rho(q)\) plays the product root \(q\)
once and, after all Continue, plays Never. For \(i\in I\), write

\[
s_i=r_i(\{i\}),
\]

\[
Q_i=
\sum_{A\subseteq I\setminus\{i\}}
p_{q_{-i}}(A)r_i(A\cup\{i\}),
\tag{1}
\]

and

\[
C_i=
\sum_{\varnothing\ne A\subseteq I\setminus\{i\}}
p_{q_{-i}}(A)r_i(A)
+p_{q_{-i}}(\varnothing)\max\{0,s_i\}.
\tag{2}
\]

Then player \(i\)'s cap over every complete behavioral deviation is

\[
B_i^{\rho(q)}=\max\{Q_i,C_i\}.
\tag{3}
\]

If one initial all-Continue padding row is inserted, the cap is
\(\max\{s_i,Q_i,C_i\}\). Consequently the padded and unpadded caps agree
whenever the supplied cap is strictly larger than \(s_i\).

Now assume the Fin4 hard-residual regime and suppose a full-debt positive
global minimum \(z=(U,B)\), with total debt \(D_*>0\), is attained by
\(\rho(q)\). Assume exactly one root coordinate is sure:

\[
q_k=1,
\qquad
q_j<1\quad(j\ne k).
\tag{4}
\]

There is a literal complete behavioral response by \(k\) which Continues at
the root and, after joint opponent survival, chooses between a later
singleton Quit and Never according to the sign of \(s_k\). If
\(\widehat\sigma\) is the resulting profile, then

\[
U_k(\widehat\sigma)-U_k(\rho(q))=d_k(z)>0,
\qquad
B_k(\widehat\sigma)=B_k(\rho(q)),
\qquad
d_k(\operatorname{Sem}(\widehat\sigma))=0.
\tag{5}
\]

Suppose additionally that the response target remains on the same positive
global-minimum fibre. Let \(R>0\) bound every reward coordinate, and let
\(\lambda_{\mathrm{fin}}>0\) be the least total finite mass over the compact
global-minimum joint-law set. Then the opponent-incidence probability at the
root satisfies

\[
1-\prod_{j\ne k}(1-q_j)
\ge
\min\left\{\lambda_{\mathrm{fin}},\frac{D_*}{2R}\right\}>0.
\tag{6}
\]

Hence one of the seven nonempty opponent coalitions has product-root mass at
least one seventh of the right-hand side of (6). This is a quantitative
static incidence passport, not a profitable whole-profile deviation.

## Proof

At the product root, any behavioral response by player \(i\) mixes Quit and
Continue. Quitting has value \(Q_i\). If \(i\) Continues and an opponent
Quits, the corresponding opponent coalition absorbs. If every opponent
Continues, all opponents subsequently play Never, so every future stopping
law of \(i\) mixes the singleton payoff \(s_i\) and the Never payoff zero.
The optimal continuation is therefore (2), proving (3). A padding row adds
exactly the early singleton option \(s_i\).

Because \(q_k=1\), prescribed play gives \(U_k=Q_k\). Positive owner debt and
(3) force

\[
B_k=C_k>Q_k,
\qquad
C_k-Q_k=d_k(z).
\tag{7}
\]

The stated response attains \(C_k\). Its opponents are unchanged, so its
unrestricted cap is unchanged. This proves all three identities in (5).

Put

\[
a_{-k}=1-\prod_{j\ne k}(1-q_j).
\tag{8}
\]

If \(a_{-k}=0\) and \(s_k\ge0\), the response target has pure singleton law
\(\{k\}\) and \(U_k=B_k=s_k\), contradicting the positive-minimum singleton
margin. If \(a_{-k}=0\) and \(s_k<0\), the response target has pure Never
law, contradicting the positive-finite-atom theorem for a hard-residual
global minimum. Thus \(a_{-k}>0\).

If \(s_k<0\), all finite mass of the response target is opponent absorption,
so \(a_{-k}\ge\lambda_{\mathrm{fin}}\). If \(s_k\ge0\), the singleton margin
and (7) give

\[
D_*
\le C_k-s_k
=\sum_{\varnothing\ne A\subseteq I\setminus\{k\}}
p_{q_{-k}}(A)\bigl(r_k(A)-s_k\bigr)
\le2Ra_{-k}.
\tag{9}
\]

This proves (6), and finite pigeonhole gives the one-seventh coalition floor.

## Checked ingredients and possible Lean seam

The ordinary proof uses the checked singleton margin
`minimumTerminalSemantic_singletonMargin`, the hard-residual finite-law-atom
theorem `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`, and
the existing terminal-incidence interfaces. A narrow future implementation
could expose:

```text
quittingProductThenNever_completeCap_eq_max_quit_continue
quittingOneSureProduct_ownerResponse_gain_eq_debt
quittingOneSureProduct_ownerResponse_debt_eq_zero
quittingOneSureProduct_minimumTarget_opponentIncidence_pos
finFourOneSureProduct_minimumTarget_opponentIncidence_floor
```

The former packet's same-target reset re-anchor and
`finFourOneSureProduct_offMinimum_or_resetRigid` route are not active
formalization obligations.

## Scope and nonclaims

This record does not supply the one-root product profile, consume the
incidence floor, produce a reset-rigid point, consume an off-minimum paid
target, or prove a uniform-equilibrium payoff. It does not assert that total
opponent incidence equals \(a_{-k}\): a terminal containing several opponents
is counted once for each opponent in the repository's aggregate incidence.
