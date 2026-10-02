# KKT infinitesimal corners do not align the minimum and escape scales

Author: `CODEX_HAHN`

## Status

**Exact rate audit and adapter failure; not a consumer.**  The full timing
bubble at the KKT pure-response corners cannot be moved infinitesimally onto
the finite-clock minimizing source at the scale required by the current
minimum-fibre or all-player-escape consumers.  The weak bubble is a
second-order product of two private mixtures, while the semantic displacement
is generically first order.  Alternating the four corners removes the
first-order terms, but creates a signed response square rather than one actual
profile or positive terminal-law escape account.

## 1. Literal infinitesimal square

Let `mu` be a finite-clock exploitability minimizer in the internal KKT
cross-amplification arm.  Let distinct players `j,i` have selected pure
responses `r,t`, and let `s` be the selected support time of player `i`.  For
`a,b in [0,1]`, define the actual product profile

\[
 \mu^{a,b}
 =\mu[j\leftarrow(1-a)\mu_j+a\delta_r,
       i\leftarrow(1-b)\mu_i+b\delta_s].
\tag{1}
\]

One can use `delta_t` in place of `delta_s`; both pure corners have the same
survival conclusion.  Suppose the selected first-disagreement dates tend to
infinity along growing horizons, and let `c>0` be the resulting full joint
survival floor at the pure corner.

The product expansion of the two private mixtures assigns weight exactly
`ab` to the pure `(r,s)` corner.  At the selected moving date the actual
profile (1) therefore satisfies

\[
 \Pr_{\mu^{a,b}}(T_k\text{ exceeds the selected date for every }k)
 \ge ab c.                                             \tag{2}
\]

For fixed positive `a,b`, every weak clock limit along the escaping horizons
therefore has all-player Never mass at least `ab c`.  If the amplitudes vary
and tend to zero, equation (2) is instead the corresponding normalized
finite-index lower bound.

This is a statement about the weak clock limit.  It is not automatically
terminal-law escape: the finite profiles may already put mass on literal
all-Never, and synchronized finite coalition mass can be lost at the weak
boundary.

## 2. Semantic displacement is first order

The marginal total-variation distance satisfies

\[
 \sum_k \operatorname{TV}(\mu^{a,b}_k,\mu_k)\le a+b. \tag{3}
\]

Product coupling therefore gives, uniformly in the horizon,

\[
 |U_k(\mu^{a,b})-U_k(\mu)|\le2M(a+b),                 \tag{4}
\]

and the response-uniform opponent coupling bound gives

\[
 |B_k(\mu^{a,b})-B_k(\mu)|\le2M(a+b).                 \tag{5}
\]

Thus the full terminal-semantic displacement is generically order `a+b`,
whereas the weak joint timing bubble in (2) is order `ab`.  With `a,b` tending
to zero,

\[
                    {a+b\over ab}\longrightarrow\infty. \tag{6}
\]

Taking `a=b=sqrt(lambda)` produces an order-`lambda` weak bubble but an
order-`sqrt(lambda)` semantic seam.  Taking `a,b` of order `lambda` gives an
order-`lambda` semantic seam but only an order-`lambda^2` bubble.

No choice of two vanishing positive amplitudes makes the ordinary semantic
displacement `o(ab)` without an additional first-order cancellation theorem.

## 3. Why the existing consumers do not accept this

The all-player escape account is one-sided and applies to one sequence of
actual profiles together with its own semantic and terminal-law limits.  Its
minimum consequences require that this same semantic limit minimize total
debt `D`.  Here `mu` minimizes finite-clock **maximum** exploitability, not
total debt, and the mixed profiles `mu^{a,b}` need not minimize either
quantity.

The minimum-fibre tangent machinery likewise cannot discard the order
`a+b` semantic displacement in favor of the order-`ab` timing effect.  A
flatness or balance assertion at the product scale would be an additional
theorem, not a consequence of KKT stationarity for the max-loss objective.

Taking the alternating square

\[
 F(a,b)-F(a,0)-F(0,b)+F(0,0)                            \tag{7}
\]

cancels affine first-order terms and isolates the `ab` interaction.  But (7)
is a signed object, not a probability law, a terminal semantic pair, or the
nonnegative escaped-mass measure used by the all-player account.  It returns
exactly to the existing response-square/cap-curvature lane, whose temporal
consumer remains open.

## 4. The deadline-heavy arm does not repair the mismatch

In the dual-heavy alternative, the finite-clock minimizer has a cap-active
new-deadline response `K` and a source-support pure time `s` with gain at least
the positive controller value.  This is a literal paid boundary response.
It is not an adjacent-deadline source: the minimizer is only an
`eta_K`-Nash profile on the old timing menu, and `eta_K` is bounded away from
zero in the counterexample regime.  The checked adjacent-deadline packet
requires exact Nash laws at both consecutive horizons.

Replacing the KKT minimizer by an independently chosen exact finite timing
Nash law recovers the existing adjacent-deadline producer, but loses the KKT
dual law and its same-source response square.  Thus this substitution rejoins
the known paid-port waist and does not consume the KKT boundary.

## Source audit

The finite KKT theorem is frozen in
`CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION`,
SHA-256
`9efcc2aa99ec6dbbd799297c228b20be78e5b1ec43799a267423160dfcf5dab1`.
The full timing-bubble compactification is frozen in
`CODEX_HAHN__FINITE_CLOCK_KKT_FIXED_FACE_OR_FULL_TIMING_BUBBLE`, SHA-256
`14a31273e02bcdf81304bd8eb48437c4879a00f113da0a0e0e81ca34f199af6a`.

The one-sided escape account is
`formalized/ALL_PLAYER_ESCAPE_DEBT_JUMP_AND_SOCIAL_SURPLUS_ATTAINMENT.md`.
The signed response-square boundary is
`formalized/CAP_SWITCH_RECTANGLE_FULL_CHORD_AND_FINITE_SPLICE_BOUNDARY.md`.
The exact adjacent-horizon source requirements are in
`formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`.

## Nonclaims and remaining test

- No impossibility of infinitesimal alignment under an additional balancing
  relation is claimed.
- Weak all-Never mass is not identified with positive escaped terminal-law
  mass.
- No total-debt-minimum provenance is supplied by finite-clock max-loss
  minimization.
- No chronological edge or uniform payoff is produced.

The remaining genuinely new test would be to derive first-order semantic
flatness of the two private reset directions from the simultaneous KKT law.
Without such a theorem, the infinitesimal square is only another presentation
of the already isolated cap-curvature obstruction.
