# All-player escape: social-surplus versus cap-jump account

**Identity:** `CHATGPT_EXTERNAL`

**Source:** supplied directly by the user on 2026-08-26, as a companion to
`../idea_derivations.zip`.

**Status:** `INDEPENDENTLY REVIEWED AFTER ONE SCOPE REPAIR`; ordinary
mathematics, not Lean-checked; export eligibility is being audited.

Independent review:

-
  [`feedback/CHATGPT_EXTERNAL__CONCRETE_NONLOCALITY_DERIVATIONS_INTAKE__BY_TESLA_COMPACT_EXCHANGE.md`](../feedback/CHATGPT_EXTERNAL__CONCRETE_NONLOCALITY_DERIVATIONS_INTAKE__BY_TESLA_COMPACT_EXCHANGE.md)

The proved conclusion is attainment of the positive global minimum **value**
by some actual profile in the stated sign chamber. It does not say that every
carrier point on the minimum fiber is behaviorally attained.

## Question and logical correction

Let actual behavioral profiles have semantic pairs converging to a positive
global-minimum carrier point while all complete stopping laws converge weakly
on the one-point compactification.  What exact obstruction remains if every
limiting clock has positive Never mass?

A premise `D_* > 0` already gives a fixed all-profile terminal
exploitability gap (after choosing any strictly smaller constant than
`D_*/|I|`, to avoid assuming attainment of the cap supremum).  But universal
attainment of positive global minima and existence of a positive-gap table are
logically compatible: a counterexample could have an attained positive
minimum.  They are not a dichotomy.

## Exact escape account

Let

\[
  \operatorname{Sem}(\sigma^n)=(U^n,B^n)\to z=(u,b),
\]

and assume the stopping laws converge weakly to an actual compactified-law
profile `barSigma`, with semantic pair `(bar u, bar b)`.  After a subsequence,
let the finite terminal-outcome laws converge to `m*`; let `m` be the actual
outcome law of `barSigma`.  For each nonempty coalition put

\[
 e(S)=m^*(S)-m(S).
\]

The compact-outcome bubble argument gives

\[
 e(S)\ge0,
 \qquad
 u_i-\bar u_i=\sum_{S\ne\varnothing}e(S)r_i(S).
 \tag{1}
\]

Writing `R(S)=sum_i r_i(S)`, this yields

\[
 \sum_i(u_i-\bar u_i)=\sum_{S\ne\varnothing}e(S)R(S).
 \tag{2}
\]

Assume every own singleton reward is nonnegative:

\[
 r_i(\{i\})\ge0.
 \tag{3}
\]

For fixed finite quit time, the pure-time value is continuous under the
opponents' weak law convergence.  At the limit, finite quit times tending to
infinity approximate Never from above because the only extra limiting branch
pays `r_i({i}) >= 0`.  Pure-time extremality therefore gives

\[
 \bar b_i\le\liminf_n B_i^n=b_i.
 \tag{4}
\]

Put `Delta_i=b_i-bar b_i >= 0`.  Direct subtraction gives the exact identity

\[
 \boxed{
 D(\bar\sigma)-D(z)
 =\sum_{S\ne\varnothing}e(S)R(S)-\sum_i\Delta_i.
 }
 \tag{5}
\]

## Consequence at a global minimum

If `D(z)=D_*>0` is globally minimal on the terminal-semantic carrier, then
`barSigma` is an actual profile and hence

\[
 \boxed{
 \sum_S e(S)R(S)\ge\sum_i\Delta_i\ge0.
 }
 \tag{6}
\]

If equality holds in the first comparison, `barSigma` itself attains `D_*`,
even if the particular carrier point `z` is not realized.  If no behavioral
profile attains `D_*`, then the comparison is strict.  In that case the
escaped support contains a coalition with strictly positive aggregate reward.

This gives the special-case attainment theorem

\[
 \boxed{
 r_i(\{i\})\ge0\ \forall i,
 \quad
 \sum_i r_i(S)\le0\ \forall S\ne\varnothing
 \Longrightarrow
 \text{every positive global minimum is attained by an actual profile.}
 }
 \tag{7}
\]

Indeed, (5) gives `D(barSigma) <= D(z)`, while global minimality gives the
reverse inequality.

## Boundary test: singleton signs alone do not close escape

Take players `c,a` and rewards

\[
 r_c(S)=0\quad(S\ne\varnothing),
\]

\[
 r_a(\{c\})=-1,
 \qquad r_a(\{a\})=0,
 \qquad r_a(\{c,a\})=1.
\]

Let `c` choose uniformly among dates `0,...,n` and let `a` Never quit.  Then

\[
 U_c^n=B_c^n=0,
 \quad U_a^n=-1,
 \quad B_a^n=\frac1{n+1},
 \quad D(\sigma^n)=1+\frac1{n+1}.
\]

The semantic pairs converge to

\[
 z=((0,-1),(0,0)),\qquad D(z)=1,
\]

while both clocks converge to Never.  The point `z` is not realized: any
profile with `U_a=-1` must terminate at `{c}` almost surely; at the least date
in the positive support of `c`'s finite stopping law, `a` can quit and obtain
a strictly positive collision payoff.  Nevertheless all-Never is an actual
zero-debt profile, so the global minimum is zero.

This verifies that nonnegative singleton rewards and positive debt do not
remove the all-player escape arm.  Global-minimum provenance is essential.

## Conjecture-facing boundary

The result does not prove universal attainment or construct a positive-gap
table.  It narrows genuinely nonattained positive-minimum escape under (3) to

\[
 \sum_S e(S)R(S)>\sum_i\Delta_i\ge0.
\]

A positive proof must prevent that strict escaped-social-surplus inequality;
a negative proof must realize it in a table that still has `D_*>0` against
all actual behavioral profiles.

## Review request

Check the finite-coalition bubble sign, the approximation of Never by finite
quit times under nonnegative singleton rewards, the direction of cap lower
semicontinuity, identity (5), and the unrestricted-deviation calculation in
the two-player boundary test.  Compare the special class (7) with current
attainment and opponent-tight declarations before any export decision.
