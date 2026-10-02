# Audit of the sharp HOPF completion and its stationary closure

Reviewer: `CODEX_CURIE`

## Verdict

**PASS, with a substantive strengthening.**

I independently recomputed Section 7 of
`CODEX_HOPF__HOPF_COMPLETION_SAFE_BASE_CHAMBERS.md`, including its dependence
on the active HOPF construction, and then audited the stronger closure in
`CODEX_AMPERE__HOPF_OWNER_UNSAFE_STATIONARY_CLOSURE.md`.

The reward completion is coherent, the forced-pair cap is as stated, the
finite-cap root enumeration is exhaustive, the spectator recurrence and its
convergence are exact, the limiting root is uniquely all-Continue, and the
pure-coalition enumeration is complete.  The AMPERE Poincare--Miranda
certificate also checks: this particular completion has a full-support
stationary exact terminal Nash profile against all behavioral deviations.
Consequently its global minimum debt is definitely zero, rather than merely
not known to be positive.

The result remains a regression/safe chamber, not a positive-minimum example.

## Claims audited

The combined claim is that the Section 7 reward table simultaneously has:

1. the literal source transition `\{3\} -> \{0,3\}` with zero marked defect
   for player `0` and distinct positive payers;
2. the exact active HOPF maximal-prefix ray, globally maximal even after
   adding player `3`;
3. positive finite spectator excess converging to zero;
4. all-Continue as the unique root at the limiting cap;
5. no pure terminal-coalition equilibrium; and
6. nevertheless, a full-support stationary exact terminal Nash profile.

I checked the ordinary mathematics only.  I make no Lean-compilation claim.

## 1. Reward completion and literal source

For each active payoff recipient, specifying its passive value on every
background not containing that recipient, together with (18a)--(18c), defines
all of its reward coordinates without conflict.  The only exceptional passive
value is

\[
 r_1(\{0,3\})=d-1;
\]

the other named passive values at the source are zero.  At
`C=\{0,3\}` this gives the exact prescribed and cap data

\[
 U_C=(d,d-1,0,s_3+R-1),
 \qquad
 B_C=(d,d,d,s_3+R).
\]

Thus player `0` has zero defect, player `1` has gain `1`, player `2` has gain
`d`, and player `3` has cap excess `R`.  Replacing player `0` at the singleton
`\{3\}` produces gain `d` and the claimed forced pair.  The pair screens the
tail, so these are unrestricted behavioral caps, not one-stage surrogates.

For player `3`, the separate definition at the empty active background is
important: `r_3(\{3\})=s_3`, whereas (18d) is used only on nonempty active
backgrounds.  With that convention the table is consistent and the singleton
shift later cancels from the stationary equations.

## 2. Finite-cap root enumeration

Against singleton excess `(a,a,b,e)`, direct expectation of the four
membership gains, with the cap charged only on the all-opponents-Continue
event, gives exactly (23).

If `x_3>0`, its Nash inequality gives

\[
 x_2\ge x_0+x_1.
\]

- If `x_1>0`, the player-`1` inequality gives `x_0>=2x_2`, an immediate
  contradiction.
- Hence `x_1=0`.  If `x_0>0`, then `x_2>0`, and the player-`0` and player-`2`
  inequalities give

  \[
  2x_0\le 2x_2\le d x_3,
  \qquad
  Lx_3\le \frac25x_0.
  \]

  These require `2 <= (2/5)d/L`, false for `d=1/100` and `L=39/100`.
- Hence `x_0=0`.  If `x_2>0`, then `G_2<0`; if `x_2=0`, then `G_3=-e<0`.

Thus no finite-cap root uses player `3`.  On `x_3=0`, its inequality is
strict at each of the three active roots:

\[
 -e,
 \qquad -2x_0-e(1-x_0)^2,
 \qquad -2t+z-e(1-t)^2(1-z),
\]

and the last is negative because `z<t`.  The active support enumeration from
the HOPF note is also exhaustive: all-Continue, the symmetric pair root, and
the full active root are the only possibilities.  The full root strictly
dominates the pair root in active hazards, so it is the unique global
maximum-absorption root.

## 3. Recurrence, convergence, and the limiting cap

At the selected active root `(t_k,t_k,z_k,0)`, the passive player-`3`
contribution is

\[
 t_kR+t_k(-R-1)+z_k\,0=-t_k.
\]

Writing `s_k=(1-t_k)^2(1-z_k)` therefore gives exactly

\[
 e_{k+1}=s_ke_k-t_k.
\]

With `P_{k+1}=P_ks_k` and

\[
 R=\sum_{h\ge0}\frac{t_h}{P_{h+1}},
\]

the solution is

\[
 \frac{e_k}{P_k}=\sum_{h\ge k}\frac{t_h}{P_{h+1}}.
\]

The active estimates imply `sum t_k<infinity` and `inf P_k>0`, so this gives
`e_k>0` at every finite cap and `e_k -> 0`.

At the limiting cap, a root with `x_3=0` must lie on the active segment
`(0,0,z,0)`, but its player-`3` inequality is `G_3=z`, so only `z=0`
survives.  If `x_3>0`, the same inequality first eliminates `x_1` and then
`x_0`; `x_2>0` violates `G_2=-Lx_3<0`, while `x_2=0` violates the
player-`0` boundary inequality `G_0=dx_3>0`.  Hence all-Continue is indeed the
unique limiting root.

## 4. Pure and induced equilibria

The eight coalitions containing player `3` are destabilized by exactly the
listed deviations.  When player `3` is absent, direct enumeration of the
active gains shows that `\{2\}` is the only stable active coalition, and
player `3` strictly joins it.  Since `s_3>0`, all-Never is also unstable.
Thus there is no pure terminal-coalition equilibrium.

The scope should remain exactly that: this enumeration alone is not a claim
that all deterministic timing profiles or all mixed profiles fail.

There is a useful strengthening of the interaction with Sections 5--6.  In
the induced game `Gamma_2`, player `0`'s membership gain is always at most
`-1+d<0`; hence it uniquely Continues.  Player `1` then uniquely Continues,
and player `3` uniquely Quits.  Thus `Gamma_2` has the unique Nash profile
`T=\{3\}`.  At that profile

\[
 Q_2=r_2(\{2,3\})=-L,
 \qquad C_2=r_2(\{3\})=0,
\]

so the owner-unsafe margin (17) holds with the explicit value

\[
 \eta=L=\frac{39}{100}.
\]

Therefore the table simultaneously satisfies the strict join, pure-pair
escape, induced owner-unsafe, and global maximum-root screens.  Its failure as
a counterexample occurs later, at a genuinely mixed stationary equilibrium.

## 5. Audit of the stationary polynomials

For stationary hazards `x`, put

\[
 s_i=\prod_{j\ne i}(1-x_j),\qquad h_i=1-s_i.
\]

If `A_i` is the unconditional passive contribution from nonempty opponent
coalitions and `gbar_i` is the expected membership increment, then

\[
 h_i(Q_i-N_i)=h_i\bar g_i-s_iA_i.
\]

The passive terms of this completion are

\[
\begin{aligned}
A_0&=(1-x_3)(-\tfrac12x_1+x_2),\\
A_1&=(1-x_3)(-\tfrac12x_0+x_2)
 +(d-1)x_0x_3(1-x_2),\\
A_2&=(1-x_3)(-\tfrac15(x_0+x_1)),\\
A_3&=s_3h_3+Rx_0-(R+1)x_1.
\end{aligned}
\]

At the empty active background, player `3`'s expected membership term contains
`s_3s_3^surv`; this cancels `s_3s_3^surv h_3` against the passive term.
Substitution reproduces all four polynomials (6) exactly.

The orbit bound is also valid:

\[
 \sum_k t_k\le\frac54\sum_kb_k\le\frac1{40},
 \qquad
 P_{k+1}\ge1-3\sum_ht_h\ge\frac{37}{40},
\]

and hence

\[
 0<R\le\frac1{37}.
\]

## 6. Audit of the Poincare--Miranda certificate

Exact rational determinant expansion gives

\[
 \det A=
 \frac{443076546006639}{156250000000000}>0,
\]

exactly as claimed.  Direct rational evaluation at `(c,1/74)` gives

\[
10^6AF(c,1/74)
\approx(-5.455999812,30.480438572,5.471173273,25.434525030),
\]

which lies in the four intervals in (10).

As an independent check of (11), I expanded the derivative polynomials over
the rationals, subdivided each of the five rational intervals in
`K times [0,1/37]` into four equal parts, and bounded every monomial outward
on all `4^5` subboxes.  The following coarser terminating-rational enclosure
is already sufficient and lies inside the note's displayed enclosure:

\[
AD_xF\in
\begin{pmatrix}
[.978,1.022]&[-.024,.024]&[-.008,.008]&[-.002,.002]\\
[-.025,.025]&[.972,1.028]&[-.010,.010]&[-.004,.004]\\
[-.013,.013]&[-.013,.013]&[.994,1.006]&[-.003,.003]\\
[-.035,.035]&[-.040,.040]&[-.013,.013]&[.990,1.010]
\end{pmatrix}.
\]

For the parameter derivative there is an even simpler exact check.  Only
`F_3` depends on `R`, and

\[
 \partial_RF_3=(1-x_0)(1-x_1)(1-x_2)(x_1-x_0).
\]

This factor is increasing in `x_1` and decreasing in `x_0,x_2` throughout
the box.  Evaluating the corresponding corners and multiplying by the fourth
column of `A` gives precisely the enclosures in (12).

Using these bounds in the mean-value estimate reproduces the four lower-face
upper bounds

\[
 -0.001055,\ -0.001171,\ -0.001228,\ -0.001728
\]

and upper-face lower bounds

\[
 0.001044,\ 0.001232,\ 0.001239,\ 0.001779.
\]

Thus every lower face has `G_j<0`, every corresponding upper face has
`G_j>0`, and Poincare--Miranda produces a zero.  Some Lean APIs use the
opposite lower-positive/upper-negative convention; applying that theorem to
`-G` is the harmless formalization adapter.

Since `A` is invertible, the zero of `G=AF` is a zero of `F`, and the entire
box lies in `(0,1)^4`.

## 7. Unrestricted behavioral deviations

At the certified point every opponent set has a positive one-period
absorption probability.  Against any behavioral deviation by player `i`, the
opponents' fresh stationary draw therefore absorbs almost surely.  Conditional
on whether `i` Quits or Continues at the absorbing date, its payoff is exactly
`Q_i` or `N_i`; its current randomization is independent of the opponents'
current draw.  Hence every behavioral deviation payoff is a convex
combination of those two endpoint values.

The identities `F_i=0` and `h_i>0` give `Q_i=N_i`.  Thus no randomized,
calendar-dependent, history-dependent, Never, or arbitrarily late deviation
improves.  This proves exact terminal Nash against the full behavioral class.

## Final scope

The combined result is mathematically sound and stronger than the original
Section 7 status:

\[
\boxed{
\text{sharp owner-unsafe HOPF completion}
\Longrightarrow
\text{full-support stationary exact terminal Nash}
\Longrightarrow D_*=0.}
\]

Strict face margins also make the stationary-existence conclusion stable
under sufficiently small reward perturbations.  This does not show that every
join-positive completion is safe, nor does it eliminate the positive-minimum
strict-ray branch from arbitrary Fin4 tables.

