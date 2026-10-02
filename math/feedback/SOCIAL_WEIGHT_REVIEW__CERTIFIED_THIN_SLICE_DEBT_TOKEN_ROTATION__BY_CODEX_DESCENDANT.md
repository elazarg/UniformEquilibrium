# Review of the global separation of the two debt minima

Reviewer: `CODEX_DESCENDANT`  
Verdict: **PASS for Section 9; one typographical repair**

I checked the claimed universal bound

\[
D_* - \eta\ge \sqrt{4M^2+\eta^2}-2M,
\qquad
\eta:=\inf_\sigma\max_i d_i(\sigma).
\]

The proof is sound.  For a near-minimizer of total debt, a maximal coordinate
has debt at most $\eta+h+\delta$, while every other coordinate has debt at
most $h+\delta$, where $h=D_*-\eta$.  Mixing that player's prescribed
stopping law with a $\zeta$-best response by weight $\theta$ gives

\[
d_p\le (1-\theta)(\eta+h+\delta)+\theta\zeta.
\]

For a nonmover, each fixed behavioral-response payoff is affine in the
mover's stopping-law mixture and changes by at most $2M\theta$.  Taking the
supremum preserves the same Lipschitz bound for the complete behavioral cap;
the prescribed payoff has the same bound.  Hence its debt rises by at most
$4M\theta$.  No attainment of either infimum or of the best response is used.

The interval

\[
\frac{h}{\eta+h}<\theta<\frac{\eta-h}{4M}
\]

is nonempty exactly when $h^2+4Mh-\eta^2<0$.  Choosing $\delta,\zeta$ after
the strict interval then makes every coordinate debt strictly below $\eta$,
the desired contradiction.  Solving the resulting quadratic gives the
displayed bound.  The constants and inequality directions are correct.

This is a genuine quantitative exclusion of the exact one-debtor-token face,
but it does not consume the multi-debtor or off-minimum paid-port residual.

The displayed formula after (33) contains a malformed `frac`; replace it by
the normal LaTeX command `\frac`.

## Second pass: the ratio-chamber port theorem

Verdict: **PASS for the revised Section 10.**

The exact-attainment version is correctly qualified.  The general carrier
version does not need attainment.  For actual realizers $\sigma_n\to x$, a
fixed maximal-debt label has debts $a_n\to a$.  The proof that $a>\eta$ is
valid: if $a=\eta$, the hypothesis $D_*<2\eta$ leaves a uniform gap below
$\eta$ on every nonmover, and a sufficiently small fixed mixture with an
$o(1)$-best response lowers the mover below $\eta$ while the $4M\theta$
bound keeps every nonmover below $\eta$.

For a $\zeta_n$-best-response target $\rho_n$, its mover debt
$e_n\le\zeta_n$, and along the literal stopping-law chord the mover debt is
exactly

\[
(1-\theta)a_n+\theta e_n.
\]

At a parameter tending to
$\theta_*=(a-\eta)/a$, just beyond the crossing, the mover is below $\eta$;
the definition of $\eta$ therefore forces a nonmover debt at least $\eta$.
The chord total debt has lower limit at least $2\eta$.  Convexity of every
complete debt coordinate gives

\[
\liminf_n D(\rho_n)
\ge \frac{\eta(2a-D_*)}{a-\eta},
\]

and hence

\[
\liminf_n(D(\rho_n)-D_*)
\ge \frac{a(2\eta-D_*)}{a-\eta}
\ge \frac{D_*(2\eta-D_*)}{D_*-\eta}.
\]

The last inequality has the correct direction because
$a\le D_*$ and $a/(a-\eta)$ is decreasing for $a>\eta$.  All denominators
are positive under $\eta<D_*<2\eta$.

The source claim is also honest: $\sigma_n$ and $\rho_n$ are actual profiles
with literally identical opponents, their payoff gain tends to at least
$\eta$, and compactification is used only to obtain an off-minimum target
cluster.  No limiting behavioral response or cap attainment is asserted.

I recommend exporting Sections 9--10 as a standalone quantitative
chamber-contraction packet after the normal gate.  It permanently excludes
minimum-fibre debtor rotation in the entire chamber
$1<D_*/\eta<2$ by sending it to the existing off-minimum paid port.  It is
not an off-minimum-port consumer and should not be described as closing the
Fin4 chamber.
