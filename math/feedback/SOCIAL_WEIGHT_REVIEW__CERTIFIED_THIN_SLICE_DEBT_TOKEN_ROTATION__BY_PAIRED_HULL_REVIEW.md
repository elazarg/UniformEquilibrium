# Delta review of the thin-slice ratio chamber

Reviewer: PAIRED_HULL_REVIEW  
Date: 2026-08-31  
Verdict: **PASS with a bounded attainment/limit clarification**

## Claim checked

Sections 9--10 claim two quantitative facts for

\[
\eta=\inf_\sigma\max_i d_i(\sigma)>0,
\qquad
D_*=\inf_\sigma\sum_i d_i(\sigma):
\]

1. a universal separation

   \[
   D_*-\eta\ge\sqrt{4M^2+\eta^2}-2M>0;
   \]

2. if an actual source has total debt \(\eta<S<2\eta\), then an exact
   best response by a maximal debtor lands strictly off its total-debt level:

   \[
   D(\rho)-S
   \ge\frac{a(2\eta-S)}{a-\eta}
   \ge\frac{S(2\eta-S)}{S-\eta}>0,
   \]

   where \(a=\max_i d_i(\sigma)\).

The mathematics is correct. Minimum-fibre debtor rotation is impossible
throughout \(1<D_*/\eta<2\). The note should clarify that an exact best
response need not be attained; the carrier-minimum statement uses
\(o(1)\)-best responses and a limiting crossing.

## 1. Convexity and crossing: PASS

Along the chord changing only player \(p\)'s stopping law:

* \(p\)'s opponents and hence \(B_p\) are fixed;
* every prescribed payoff is affine;
* for \(i\ne p\), \(B_i\) is the supremum of affine response-payoff
  functions, hence convex and continuous; and
* consequently every nonmover debt, and total debt, is convex.

For an exact best-response endpoint,

\[
d_p(\sigma^\theta)=(1-\theta)a.
\]

The proof that \(a>\eta\) is valid. If \(a=\eta\), then immediately after
moving toward the response the mover is below \(\eta\), so the global
maximum-debt floor forces a fixed nonmover to have debt at least \(\eta\).
Letting the parameter decrease to zero gives two source coordinates at least
\(\eta\), contrary to \(S<2\eta\).

At

\[
\theta_0=\frac{a-\eta}{a},
\]

the mover debt is exactly \(\eta\). For every larger parameter another
coordinate has debt at least \(\eta\); finiteness and continuity retain one
at \(\theta_0\). Hence \(D(\sigma^{\theta_0})\ge2\eta\).

## 2. Algebra and denominator inequalities: PASS

Convexity gives

\[
2\eta\le(1-\theta_0)S+\theta_0D(\rho).
\]

Solving yields the first inequality. All denominators are positive because
\(a>\eta\), and \(2\eta-S>0\). Moreover \(a\le S\), while
\(x/(x-\eta)\) is decreasing on \((\eta,\infty)\). Therefore

\[
\frac{a(2\eta-S)}{a-\eta}
\ge\frac{S(2\eta-S)}{S-\eta}.
\]

The direction of the second inequality in (42) is correct.

## 3. Actual minimum and carrier passage: PASS after clarification

If a global minimum is attained and an exact best response exists,
substituting \(S=D_*\) gives

\[
\Delta_{\mathrm{port}}
=\frac{D_*(2\eta-D_*)}{D_*-\eta}>0.
\]

For the general carrier statement:

1. choose actual \(\sigma_n\) with \(D(\sigma_n)\to D_*\);
2. stabilize a maximizing label \(p\), put
   \(a_n=d_p(\sigma_n)\), and choose an \(o(1)\)-best response \(\rho_n\);
3. pass to a subsequence with \(a_n\to a\);
4. prove \(a>\eta\): otherwise choose chord parameters tending to zero but
   just past the mover's \(\eta\)-crossing; a stabilized nonmover then has
   source debt tending to at least \(\eta\), forcing \(D_*\ge2\eta\);
5. use

   \[
   \theta_n=\frac{a_n-\eta}{a_n-d_p(\rho_n)}
   \]

   and pass to the limit.

This gives

\[
\liminf_n\bigl(D(\rho_n)-D(\sigma_n)\bigr)
\ge\frac{a(2\eta-D_*)}{a-\eta}
\ge\Delta_{\mathrm{port}}.
\]

Compactification gives a target carrier point of debt at least
\(D_*+\Delta_{\mathrm{port}}\). The literal source sequence and its response
targets retain common opponents, and the gains tend to \(a\ge\eta\). No
unrelated source is selected.

## 4. Global separation theorem in Section 9: PASS

Put \(h=D_*-\eta\). At an actual \(D_*+\delta\) approximant, every nonmover
debt is at most \(h+\delta\). Mixing toward an approximate best response
bounds the mover by

\[
(1-\theta)(\eta+h+\delta)+\theta\zeta
\]

and each nonmover by \(h+\delta+4M\theta\). The interval

\[
\frac{h}{\eta+h}<\theta<\frac{\eta-h}{4M}
\]

is nonempty exactly when \(h^2+4Mh-\eta^2<0\). Small
\(\delta,\zeta\) would then make every debt less than \(\eta\), a
contradiction. Solving the quadratic gives (33). The constants and convexity
direction are correct.

## 5. Corrections before any gate

1. State the actual-source theorem conditionally on exact response
   attainment, or use approximate responses.
2. Expand the actual-to-carrier passage as above.
3. Repair the displayed identifier for \(\Delta_{\mathrm{port}}\) and the
   earlier visible TeX remnants.

These are bounded repairs. The ratio chamber theorem survives and is
potentially important: it converts \(1<D_*/\eta<2\) into a source-matched
quantitative off-minimum paid port. It does not consume that port.
