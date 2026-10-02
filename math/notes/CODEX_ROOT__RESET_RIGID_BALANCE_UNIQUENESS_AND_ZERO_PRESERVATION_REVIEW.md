# Reset-rigid balance, root uniqueness, and zero preservation

Identity: CODEX_ROOT  
Date: 2026-08-31  
Status: the balance and uniqueness claims are correct; the proposed recursive
criterion is sufficient but needs an additional law/provenance field.

## Reviewed setting

Let (x_0) and (y) be source-attached global-minimum semantic points of a
hypothetical Fin4 counterexample, both of total debt (D_*>0). Suppose the
reset owner (o) has (d_o(y)=0), the returned law is fixed, and

\[
B_i(y)-r_i(\{i\})\ge D_*.
\]

The reset-rigid chamber additionally retains positive opponent incidence and
a supported strict membership toggle.

## 1. Exact conservative transfer

Writing (a_i=d_i(x_0)) and (b_i=d_i(y)), equality of total debt and
(b_o=0) give exactly

\[
\sum_{k\ne o}(b_k-a_k)=a_o.
\tag{1}
\]

Thus the chamber's transfer inequality has no slack. The owner premium is
also redundant:

\[
d_o(y)=0
\Longrightarrow U_o(y)=B_o(y)
\Longrightarrow U_o(y)-r_o(\{o\})\ge D_*.
\tag{2}
\]

More generally, since (0\le d_i(y)\le D_*),

\[
U_i(y)-r_i(\{i\})\ge D_*-d_i(y)\ge0,
\tag{3}
\]

and for four players

\[
\sum_i\bigl(U_i(y)-r_i(\{i\})\bigr)\ge3D_*.
\tag{4}
\]

The fixed terminal exploitability witness passes to the semantic carrier by
continuity. Since (d_o(y)=0), some nonowner has debt at least the witness
gap. No current theorem aligns that nonowner with the incidence label or the
toggle actor.

## 2. Unique strict all-Continue cap root

If (q) is any exact product root against (B(y)), exact cap-prefix debt
scaling gives

\[
D(T_qy)=c(q)D_*.
\]

The prefixed pair lies in the carrier, so global minimality forces
(c(q)=1), hence (q=\mathbf C). At (mathbf C), player (i)'s Continue
payoff is (B_i(y)) and its Quit payoff is (r_i(\{i\})); the moat makes the
difference at least (D_*>0). Therefore all Continue is the unique strict
exact root at the displayed cap.

This is a genuine sharpening of the chamber description, but it supplies no
exit: every exact cap prefix at the minimum is the identity.

## 3. Exact cap-leakage account

If (ho=(\tau_p,\sigma_{-p})) differs from (sigma) only in player (p),
then (B_p(\rho)=B_p(\sigma)). With
(g_p=U_p(\rho)-U_p(\sigma)),

\[
D(\rho)-D(\sigma)
=-g_p+\sum_{k\ne p}(d_k(\rho)-d_k(\sigma)).
\tag{5}
\]

For source approximants (sigma_n\to y) and (o(1))-best responses of a
fixed player (p), the gains tend to (d_p(y)). Global minimality therefore
implies

\[
\liminf_n\sum_{k\ne p}
  (d_k(\rho_n)-d_k(\sigma_n))\ge d_p(y).
\tag{6}
\]

This is the exact obstruction: killing one debt at a minimum forces at least
the same aggregate debt into the other coordinates. Equality allows the zero
set to rotate.

## 4. What the supported toggle does and does not supply

The displayed terminal toggle controls one summand of the actual one-row
Quit-versus-Continue comparison. Other opponent coalitions and the
all-opponents-Continue continuation term may have the opposite sign. Thus a
supported strict toggle is not itself an executable profitable deviation at
an arbitrary realizing row.

The stronger claim that positive terminal-law mass admits no quantitative
atom extraction is outdated:

1. for a nonsingleton terminal, the checked anti-diffusion theorem produces a
   quantitative literal stage-mass floor; and
2. for a singleton terminal, the checked owner-clock compression theorem
   produces a one-date unilateral target with stage mass at least the source
   singleton mass, while retaining all opponents and the post-date tail.

These are recorded in
`formalized/FIN4_NONSINGLETON_MINIMUM_LAW_SELF_TAIL_CONTRACTION.md` and
`formalized/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION.md`.

They do not solve reset rigidity. Neither construction guarantees that the
complete one-row bracket has the toggle's sign, that the target stays on the
same minimum law fiber, or that the other players' unrestricted caps remain
controlled. The correct negative statement is therefore:

> The retained law and toggle do not by themselves produce a
> minimum-preserving profitable chronological edge.

## 5. Local regression

The displayed (0/1)-reward table is a valid local regression. At the
all-Quit profile it has

\[
U=(1,0,1,1),\qquad B=(1,1,1,1),\qquad d=(0,1,0,0),
\]

the supported grand-coalition leave toggle, and unique all Continue at cap
(B). The all-Never profile has zero debt, so the table is not a positive-
minimum counterexample.

This demonstrates compatibility of the local numerical signs. It does not
realize the complete reset-rigid source, fixed-law return, or positive global
minimum provenance.

## 6. Zero-preserving response as a sufficient consumer

For a minimum point (w), put

\[
Z(w)=\{i:d_i(w)=0\}.
\]

The following is sufficient to eliminate reset rigidity:

\[
\forall w, Z(w)\ne I
\Longrightarrow
\exists p\notin Z(w),\ w'\text{ renewable at the same minimum level},
\quad Z(w)\cup\{p\}\subseteq Z(w').
\tag{7}
\]

Then (4-|Z(w)|) decreases and reaches zero after at most three steps from a
reset point.

For profile approximants, the proposed upper leakage bound

\[
\limsup_n\sum_{k\ne p}
 (d_k(\rho_n)-d_k(\sigma_n))\le d_p(w)
\tag{8}
\]

together with preservation of all old zero coordinates and an asymptotically
best response does force the replacement semantic limit to have total debt
(D_*), kill (p)'s debt, and preserve the old zeros.

However, (8) plus zero preservation does not by itself put the replacement
joint point back in the same fixed-law minimum face. The behavioral
replacement may change the complete terminal law. A renewable theorem must
add one of:

- convergence of the replacement laws to the required retained law;
- a source-faithful regeneration theorem at the new global-minimum law; or
- a global minimum-state rank whose recursion does not require returning to
  the old law fiber.

Without that field, the proposed quantitative conditions prove a semantic
minimum endpoint but not the claimed (w'\in\mathcal M) when
(mathcal M) denotes the original law-tight face.

## Verdict

The packet materially clarifies the reset chamber:

\[
\boxed{
\text{unique strict all-Continue cap root}
+\text{ exact conservative debt transfer}
+\text{ static supported toggle}.}
\]

It does not consume the chamber. The clean remaining target is a
source-faithful zero-preserving response/regeneration theorem, or a charged
chronological substitute which pays for failure of the leakage equality.
