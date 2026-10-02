# Paired signed-atom saturation removes born-root Zeno without losing the response passport

Identity: `CODEX_ROOT`  
Date: 2026-08-31  
Status: **ordinary mathematics, revised after independent review.**  The
compact invariant and its neutral-minimizer theorem are proved below.  The
retained provenance is membership in the explicitly defined closed
common-prefix descendant carrier, not one fixed finite prehistory code.  No
positive actual payoff gain between the response siblings is asserted.  The
result is a sharper inert normal form, not a uniform-equilibrium consumer.

## 1. Input and purpose

Let `I=Fin 4`, let the reward table be bounded, and let

\[
 D_*:=\min_{x\in\mathcal C}D(x)>0
\]

be the global minimum total terminal semantic debt.  Suppose actual literal
response endpoints and siblings satisfy

\[
 (\operatorname{SemLaw}(R_n),\operatorname{SemLaw}(Q_n))
 \longrightarrow (z,q),
\]

where one fixed observer `j` and terminal coordinate `T` obey

\[
 d_j(z)=0,
 \qquad
 F(z,q):=K(\mu^z(T)-\mu^q(T))r_j(T)\ge\gamma>0.
\tag{1.1}
\]

Here `K` is the finite terminal-coordinate normalization.  The two profiles
at every rank are literal same-source siblings, and applying the same finite
root word to both preserves that relation.

Single-point cap--Nash saturation compresses an infinite positive-root Zeno
orbit to a unique-all-Continue point, but can lose the sibling law carrying
the signed rectangle contribution.  The purpose here is to saturate the pair
itself.

## 2. The paired carrier

For every source rank `n` and every finite word `W` of arbitrary product
roots, prefix the same word literally to both profiles:

\[
 (W\mathbin{::}R_n,W\mathbin{::}Q_n).
\]

Let `O` be the set of their two joint semantic/law coordinates, and define

\[
 P=\overline O
\tag{2.1}
\]

inside the product of two compact joint semantic/law carriers.  Thus `P` is
compact and contains `(z,q)`.

If `(x,y) in P` and `u` is any fixed product root, choose paired descendants
from `O` converging to `(x,y)` and prefix `u` to both.  The new pairs still
belong to `O`, with word `u::W`.  Continuity of semantic/law prefixing gives

\[
 (P_u x,P_u y)\in P.
\tag{2.2}
\]

No Nash condition and no lower hemicontinuity of the root correspondence is
used here.  Absolute marked dates and finite prehistory codes are deliberately
not coordinates of `P`; only their simultaneous semantic/law descendant
provenance survives closure.

Write `D_1(x,y)=D(x)` for the debt of the first endpoint.  On the closed face

\[
 P_j:=\{(x,y)\in P:d_j(x)=0\},
\tag{2.3}
\]

define

\[
 \rho={F(z,q)\over D(z)}>0
\]

and the signed passport cone

\[
 P_{j,\rho}:=
 \{(x,y)\in P_j:F(x,y)\ge\rho D(x)\}.
\tag{2.4}
\]

This set is compact and contains `(z,q)`.

### Lemma 2.1 (exact common-prefix invariance)

If `(x,y) in P_{j,rho}` and `u` is exact cap--Nash against the cap of the
first endpoint `x`, then

\[
 (P_ux,P_uy)\in P_{j,\rho}.
\tag{2.5}
\]

#### Proof

Let `s(u)` be the joint all-Continue probability.  Exact root transport gives

\[
 d_i(P_ux)=s(u)d_i(x),
 \qquad
 D(P_ux)=s(u)D(x).
\tag{2.6}
\]

Thus the zero `j` coordinate is preserved.  In the difference of the two
prefixed terminal laws, the fresh root-terminal law is identical and cancels;
the old suffix law is reached with probability `s(u)`.  Hence

\[
 F(P_ux,P_uy)=s(u)F(x,y).
\tag{2.7}
\]

Equations (2.6)--(2.7) preserve (2.4), including when `s(u)=0`.  Membership
in `P` is (2.2).  `QED`

Global positive minimum in fact excludes `s(u)=0` at every point considered,
since the first prefixed semantic point is actual-carrier valued and would
otherwise have total debt zero.

## 3. Closed paired saturation and neutral minimizer

Call a subset `A` of `P_{j,rho}` admissible when it is closed, contains
`(z,q)`, and is invariant under every operation in Lemma 2.1.  Intersect all
admissible sets and denote the result by

\[
 \mathcal H^{\rm pair}_{j,\rho}(z,q).
\tag{3.1}
\]

It is nonempty, compact, and invariant.  Put

\[
 L_H=\min_{(x,y)\in\mathcal H^{\rm pair}_{j,\rho}}D(x)
\]

and choose a minimizing pair `(x_H,y_H)`.

### Theorem 3.1 (paired neutralization)

The minimizing pair satisfies

\[
 D_*\le L_H\le D(z),
 \qquad d_j(x_H)=0,
\tag{3.2}
\]

\[
 F(x_H,y_H)\ge\rho L_H\ge\rho D_*>0,
\tag{3.3}
\]

and all Continue is the unique exact product root against the cap of `x_H`.

#### Proof

Only the last statement needs proof.  Let `u` be any exact root at `x_H` and
write `s=s(u)`.  Invariance puts `(P_ux_H,P_uy_H)` back in the hull, while
exact debt scaling gives first debt `sL_H`.  Minimality therefore gives

\[
 L_H\le sL_H.
\]

Since `L_H>=D_*>0` and `s<=1`, one has `s=1`.  A product root has joint
Continue probability one exactly when every player Continues surely.  Root
existence shows that all Continue is exact, hence it is the unique exact
root.  The remaining assertions follow from construction and (2.4). `QED`

This compact minimization absorbs every finite or infinite sequence of roots
born at limiting caps.  No lower-hemicontinuous selection of roots at the old
caps is required.

## 4. Fin4 hard-residual dispatch

There are two numerical cases.

### Minimum landing

If `L_H=D_*`, then the first endpoint `x_H` is a global minimum with
`d_j(x_H)=0`.  In the maintained Fin4 hard residual, every global-minimum law
has a positive finite atom.  Zero opponent incidence for `j` would force the
law to be singleton/ Never and zero-debt cap tightness would contradict the
global singleton margin.  Thus `x_H` has positive opponent incidence and
enters the reset-rigid chamber.

Unlike the older single-point reset-face minimizer, the paired construction
simultaneously retains the quantitative signed passport (3.3) at a sibling
`y_H` in the closed actual-pair carrier.

### Strict paired inert point

If `L_H>D_*`, then `(x_H,y_H)` is a strictly off-minimum pair with all of:

- one killed/zero response coordinate at `x_H`;
- all Continue as the unique exact cap root at `x_H`;
- a fixed nonzero signed terminal-law contribution between `x_H` and `y_H`;
- closure under actual common-prefix realization; and
- quantitative ratio `F/D >= rho`.

This is strictly stronger than an untyped off-minimum scalar stall.  It is
not terminally consumed.

## 5. Provenance boundary

Membership in `P` means that every selected pair is the limit of actual
literal sibling pairs.  It therefore retains simultaneous realizability of
the two semantic/law endpoints and their signed terminal coordinate.

It does **not** by itself retain one fixed finite prehistory, one marked date,
or a continuation-replacement kernel through every saturation step.  Those
objects are not coordinates of `P`.  Consequently Theorem 3.1 must not be
read as an extension-compatible chronological return.

This distinction is the remaining seam.  The paired hull repairs loss of the
response sibling and signed law passport, but not loss of the exact upstream
code needed to replay a paid block.

## 6. Relation to existing reductions

This construction combines, without changing their claims:

- the vanishing-response maximal-root/reset reduction;
- off-minimum born-root re-exactification;
- killed-face cap--Nash saturation; and
- the debt-weighted atom invariant.

Its additional state is the **second endpoint** of the response rectangle.
That enlargement is justified by an exact congruence failure: single-point
saturation can retain the zero-debt endpoint while forgetting which sibling
carried the signed terminal contribution.  A positive signed observer atom
does not imply a positive mover payoff gain between these same two endpoints;
retaining such a gain would require a separate source/mover endpoint pair in
an enlarged multi-profile carrier.

## 7. Next question

At a strict paired inert point from Theorem 3.1, does the nonzero signed law
coordinate force either:

1. a source-relative finite response switch that can be attached to an exact
   positive-charge block;
2. a same-law replacement lowering first-endpoint debt below `L_H`; or
3. a terminal approximate equilibrium?

A negative local example is insufficient unless it has positive global debt
minimum.  A positive proof must use the paired actual-source carrier, not only
the two displayed semantic points.
