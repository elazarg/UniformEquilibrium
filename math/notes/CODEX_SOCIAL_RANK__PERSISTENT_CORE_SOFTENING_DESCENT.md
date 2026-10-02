# Persistent-core softening gives a renewable full-debt rank

Identity: CODEX_SOCIAL_RANK  
Date: 2026-08-31  
Status: **ordinary mathematics proof; independent delta review pending.**

## 1. Input

Let (I=operatorname{Fin}4), and assume the hard-residual contradiction
regime with positive global minimum debt (D_*>0).  Let (z=(U,B)) be a
global minimum semantic pair with full debt,

\[
 D(z)=D_*,
 \qquad
 d_i(z)>0
 \quad(i\in I).
\tag{1.1}
\]

Assume (z) is attained by the literal finite profile that plays one
all-Continue padding row, then one product root (q), and then Never, where

\[
 K:=\{i:q_i=1\},
 \qquad |K|\geq2.
\tag{1.2}
\]

This is exactly the zero-Never, zero-singleton arm of
`CODEX_SOCIAL_SOURCE__CLOSED_BEHAVIORAL_LAW_PRODUCT_BASE`: its law-closure
theorem produces the root and its cap theorem proves equality with the
original complete semantic pair.  The argument below begins with this
literal attained profile; it never selects another realization of (z).

The checked positive-minimum singleton margin gives

\[
 B_i-r_i(\{i\})\geq D_*
 \quad(i\in I).
\tag{1.3}
\]

## 2. Every sure quitter has an exact paid leave response

Write (s_i=r_i(\{i\})).  At the absorbing product root, let (Q_i) be
player (i)'s payoff from Quit and (C_i) its complete payoff from Continue,
including the optimal choice between a later singleton Quit and Never if all
opponents Continue at the root.

Because (K) has at least two members, every player has a sure quitter among
its opponents.  The all-opponents-Continue branch has probability zero, and

\[
 U_i=q_iQ_i+(1-q_i)C_i.
\tag{2.1}
\]

The complete cap of the padded profile is

\[
 B_i=\max\{s_i,Q_i,C_i\}.
\tag{2.2}
\]

Equation (1.3) makes the singleton option strictly nonbinding, so

\[
 B_i=\max\{Q_i,C_i\}.
\tag{2.3}
\]

Fix (p\in K).  Since (q_p=1), (2.1) gives (U_p=Q_p).  Full debt and
(2.3) then give

\[
 C_p-Q_p=d_p(z)>0.
\tag{2.4}
\]

This is a complete behavioral comparison, not a stationary truncation: one
other sure quitter screens every continuation after (p) changes its root
action.

## 3. Soften instead of deleting

For (0<\theta<1), let (q^{p,\theta}) agree with (q) except that

\[
 q^{p,\theta}_p=1-\theta,
\]

and let (z^{p,\theta}) be the semantic pair of the corresponding literal
padded product profile.  Only (p)'s strategy changes.  Therefore its cap is
unchanged, while its prescribed payoff moves by the exact amount

\[
 U_p(z^{p,\theta})-U_p(z)
 =\theta(C_p-Q_p)
 =\theta d_p(z)>0.
\tag{3.1}
\]

Consequently

\[
 d_p(z^{p,\theta})=(1-\theta)d_p(z)>0.
\tag{3.2}
\]

Every other debt is continuous in (	heta).  Hence some
(ar\theta>0) satisfies

\[
 0<\theta\leq\bar\theta
 \quad\Longrightarrow\quad
 d_i(z^{p,\theta})>0
 \quad(i\in I).
\tag{3.3}
\]

The use of a small softening is essential.  A pure deletion kills (p)'s
debt and may transfer all of it to one outsider, so the resulting point need
not be full debt and cannot automatically be iterated.  Equations
(3.2)--(3.3) prevent that reset of the rank comparison.

## 4. Exact minimum-child/off-minimum split

Along this one-coordinate segment, every root payoff (Q_i,C_i) and every
prescribed payoff is affine in (	heta).  Every cap is the maximum of those
affine functions and the constant singleton option.  Therefore

\[
 f(\theta):=D(z^{p,\theta})
\tag{4.1}
\]

is convex on ([0,1]).  Since (f(0)=D_*) is its global lower bound, (f)
is nondecreasing.

Fix any (	hetain(0,ar\theta]).  If

\[
 f(\theta)>D_*,
\tag{4.2}
\]

then also (f(1)>D_*).  The pure member-leaving target is therefore an
off-minimum actual profile, connected to (z) by the exact paid endpoint

\[
 U_p(z^{p,1})-U_p(z)=d_p(z)>0.
\tag{4.3}
\]

If instead

\[
 f(\theta)=D_*,
\tag{4.4}
\]

then (z^{p,\theta}) is another attained full-debt global minimum, by
(3.3).  Its maximal sure-quitter core is exactly

\[
 K\setminus\{p\}.
\tag{4.5}
\]

The child is literal: it is obtained from the parent profile by the one
unilateral root change above, and (3.1) is its backward paid edge.  No law,
cap, date, profile, or minimum point is reselected.

## 5. Renewal and the rank-two boundary

If (|K|\geq3), the equality child still has at least two sure quitters.
It is a positive full-debt global minimum, so (1.3)--(4.5) apply again.
Thus

\[
 \rho(z,q)=|\{i:q_i=1\}|
\tag{5.1}
\]

is a renewable natural-valued rank on the equality arm.

When (|K|=2), write (K=\{p,k\}).  Maximality of (K) gives (q_j<1)
for (j\notin K).  The softened equality child has the literal singleton
atom

\[
 \Pr(Q=\{k\})
 =\theta\prod_{j\notin K}(1-q_j)>0.
\tag{5.2}
\]

It also remains full debt.  At this one-sure-quitter child, player (k)'s
prescribed payoff is its Quit value (Q_k).  The singleton moat excludes
(s_k) from the cap, so full debt forces

\[
 B_k=C_k>Q_k=U_k.
\tag{5.3}
\]

The value (C_k) is attained by one explicit complete response: Continue at
the product root; if an opponent Quits, accept that terminal reward; if every
opponent Continues, Quit alone next period when (s_k>0), and otherwise play
Never.  Replacing only (k)'s strategy by this response gains exactly
(d_k), leaves (B_k) unchanged, and kills (k)'s debt.

The final response target is actual.  It is either strictly off minimum, or
it is a global minimum with a zero debt coordinate.  In the latter case, the
checked every-minimum-law positive finite atom theorem and the global Fin4
two-chamber classification place it in the reset-rigid branch.

Since (|K|\leq4), there are at most three minimum-child softenings before
the final response.  We obtain the finite transition

\[
 \boxed{
 \text{attained zero-singleton full-debt product minimum}
 \Longrightarrow
 \text{off-minimum paid target}
 \ \lor\ 
 \text{reset-rigid minimum}.}
\tag{5.4}
\]

This is a rank transition, not a terminal consumer.  The off-minimum paid
target and the reset-rigid minimum are the existing open downstream arms.

## 6. Provenance and strategy class

Every profile in the construction is an ordinary independent behavioral
profile.  Every equality child uses the same passive padding date and the
same absorbing root date as its parent.  The backward edge changes only one
player's root marginal.  The final rank-two response is a complete behavioral
strategy and explicitly includes Never and the post-root singleton deadline.

The argument proves scalar unrestricted-cap identities one player at a time.
It does not assert a common coupling for arbitrary simultaneous
multi-player interventions, and it does not identify an off-minimum target
with a later source chronology.

## 7. Checked inputs and open consumer

Named checked inputs used at the last handoff are:

- `minimumTerminalSemantic_singletonMargin`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- the global full-debt/reset-rigid classification in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`.

The product-law and padded-cap entrance is ordinary mathematics in
`CODEX_SOCIAL_SOURCE__CLOSED_BEHAVIORAL_LAW_PRODUCT_BASE`, with two independent
PASS reviews for its Theorems 5.1 and 6.1.  The softening rank (Sections
3--5) has not yet been checked in Lean or independently reviewed.

The remaining consumer is exactly the already known waist:

\[
 \text{off-minimum source-attached paid target}
 \quad\text{or}\quad
 \text{reset-rigid minimum}.
\]

