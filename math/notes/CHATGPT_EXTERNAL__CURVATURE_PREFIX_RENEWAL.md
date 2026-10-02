# Curvature prefix renewal through a cap-inert branch

Author: CHATGPT_EXTERNAL

Status: REVIEWED AFTER SCOPE REPAIR; INTERNAL/NO EXPORT; EXACT TRANSPORT BUT NOT A UNIFORM RENEWABLE RANK

Independent review:

- feedback/CHATGPT_EXTERNAL__CURVATURE_PREFIX_RENEWAL__BY_CODEX_MINER.md

The audit validates the exact identities (3)--(8) and the
opponent-Continue/joint-Continue calculation in (9). It rejects the stronger
renewability claim: every transported non-inert step may lose a factor two,
so iteration guarantees only \(2^{-n}\Theta\). Literal all-Continue prefixes
preserve the full square exactly, but they also preserve the state and create
no progress.

## Question

The historical signed-label mass budget of a paid cap port can be spent once
at a finite actual prefix, but it need not regenerate at the descendant.
Is there a richer quantitative passport which survives a cap prefix and, in
particular, survives a literal all-Continue inert prefix?

## The historical-mass limitation

For a source with paid gain \(\Delta_0\), debt \(D_0\), a cap-lift descendant
with debt \(D_N\), and a supplied historical label-mass budget \(\mu\), the
finite-cut argument gives

\[
\Delta_N\ge\frac{\Delta_0}{D_0}D_N,\qquad
D_N\le D_0-\lambda D_*\mu.
\]

This does not supply a lower bound on a new \(\mu_N\). Thus the mass budget is
not itself a renewable well-founded rank.

A maximal-absorption exact cap-root selector gives the honest pointwise split:
either the selected root has positive absorption, or every exact cap root has
zero absorption and hence the all-Continue root is unique. In the latter arm,
the exact relation at the cap value has only the constant zero-charge prefix.
This statement concerns the cap annotation \(B\); it must not be silently
converted into a claim about exact roots at the prescribed payoff \(U\).

## Exact shifted-witness regret

Fix an observer \(o\), a product prefix root \(q\), and a suffix profile \(X\).
Let

\[
c=c_{-o}(q)
\]

be the probability all opponents of \(o\) Continue at the prefix. Let \(A\)
be the absorbing payoff contribution when \(o\) Continues, and \(Q\) the
payoff from quitting immediately. For a pure-time plan \(\tau\), write
\(V_X(\tau)\) for its payoff against \(X\), and \(B_X\) for the unrestricted
behavioral cap against \(X\). Then

\[
V_{q*X}(\operatorname{shift}\tau)=A+cV_X(\tau), \tag{1}
\]

\[
B_{q*X}=\max\{Q,A+cB_X\}. \tag{2}
\]

Define the immediate-Quit cap wall

\[
h_X=[Q-A-cB_X]_+.
\]

Equations (1)--(2) give the exact shifted-witness regret identity

\[
\boxed{
B_{q*X}-V_{q*X}(\operatorname{shift}\tau)
=c(B_X-V_X(\tau))+h_X.} \tag{3}
\]

The additive wall is independent of \(\tau\), so two shifted witnesses obey

\[
V_{q*X}(\operatorname{shift}\tau_2)
-V_{q*X}(\operatorname{shift}\tau_1)
=c\bigl(V_X(\tau_2)-V_X(\tau_1)\bigr). \tag{4}
\]

## Curvature transport

Let \(S,M,T\) be actual source, stopping-law mixture, and receiving profiles
of one cap square, with mixture weight \(\lambda\), and define positive
observer cap curvature

\[
C=(1-\lambda)B_S+\lambda B_T-B_M.
\]

Assume \(C>0\).

Prefix the same root \(q\) to all three corners. Their new cap curvature is
exactly

\[
\boxed{
C'=cC+(1-\lambda)h_S+\lambda h_T-h_M.} \tag{5}
\]

Suppose \(q\) is exact Nash against the receiving cap \(B_T\), and has positive
joint Continue mass. Then the observer's Continue action has positive support,
so

\[
Q\le A+cB_T,\qquad h_T=0. \tag{6}
\]

It follows that

\[
\boxed{
C'\ge\frac{cC}{2}
\quad\lor\quad
h_M\ge\frac{cC}{2}.} \tag{7}
\]

Indeed, failure of the first inequality and \(h_S\ge0\) in (5) force the
second.

For the literal all-Continue root,

\[
c=1,\qquad A=0.
\]

Every actual cap dominates immediate singleton Quit, so
\(h_S=h_M=h_T=0\). Therefore

\[
\boxed{C'=C.} \tag{8}
\]

Thus the entire cap square, unlike a historical label-mass budget, transports
losslessly through an inert cap prefix.

## One-step square-density estimate

Assume \(D_*>0\). Let \(D_T\) be the receiving endpoint's total debt and set

\[
\Theta_{\mathrm{sq}}=C/D_T.
\]

Under an exact cap-Nash prefix at \(T\), total debt scales by the joint
Continue mass

\[
c_{\mathrm{all}}=(q_o(\mathrm{Continue})).toReal\,c.
\]

In the transported-curvature arm of (7),

\[
\frac{C'}{D_T'}
\ge
\frac{cC/2}{c_{\mathrm{all}}D_T}
=\frac{\Theta_{\mathrm{sq}}}
 {2(q_o(\mathrm{Continue})).toReal}
\ge\frac{\Theta_{\mathrm{sq}}}{2}. \tag{9}
\]

Because every actual semantic descendant has debt at least \(D_*>0\), the
transported arm retains the source-independent absolute curvature floor
\(\Theta_{\mathrm{sq}}D_*/2\) for this one step. In the inert arm it retains
all of \(C\).

This calculation requires positive joint Continue mass. A zero-Continue or
positive-charge endpoint must be handled by the existing charge/descent split,
not by division in (9). The notation \(\Theta_{\mathrm{sq}}\) is deliberately
not the repository's normalized-curvature object.

Crucially, (9) is not a uniform iterative bound. After \(n\) transported
non-inert steps, this estimate alone gives only
\(2^{-n}\Theta_{\mathrm{sq}}\). No fixed positive rank or source-independent
absolute curvature floor survives arbitrary iteration.

## Honest conclusion

The full localized cap square transports more faithfully than paid density
plus a historical port label. Common prefixing yields:

1. a transported square with controlled normalized curvature;
2. an immediate-Quit wall at the mixed corner; or
3. outside the positive-Continue hypothesis, a charged/zero-Continue branch.

This is not a renewable well-founded passport under arbitrary repeated
non-inert prefixing, and it is not yet an exact prescribed-payoff chronology.
The remaining theorem is a local conversion from a fixed immediate-Quit wall
or a positive curvature square at a unique-all-Continue cap to one of:

- a positive-charge exact punishment-floor path;
- strict well-founded debt/support descent; or
- another source-matched curvature square with a quantitatively controlled
  passport.

The result supplies an exact lossless identity on the literal inert arm and a
one-step transport-or-wall estimate elsewhere. It does not repair the proposed
iterable invariant and does not close the paid-port inert arm.

The wall \(h_M\) is the immediate-Quit versus continuation Nash defect of the
mixed cap root; it is not automatically the cap-versus-prescribed surcharge.
Also, “no positive-charge path begins at the port” is valid only for forward
cap prefixes whose tail annotation is \(B\). It says nothing about roots at
the prescribed payoff \(U\), nor about a backward edge having \(B\) as head.

## Source and review disposition

The cap-prefix max identity is the same structural input used throughout the
cap-Nash chronology. Current positive-rectangle and reset-face modules provide
static atom/orientation outputs but explicitly stop before an exact
state-matched chronology.

The review found no named declaration packaging (3) or (5), but the maintained
inert-stall structure stores only the receiving profile and paid row, not the
full \(S,M,T,\lambda\) square. A richer carrier would therefore be required
even to retain this exact static data. With no accepted chronology consumer,
the result remains internal.
