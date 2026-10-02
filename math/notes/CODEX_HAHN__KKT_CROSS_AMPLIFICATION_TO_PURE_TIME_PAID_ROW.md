# KKT cross-amplification gives a literal pure-time paid row

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; followup to the finite-clock KKT dichotomy, not
Lean-checked and not a consumer.**  The cross-amplification branch can be
converted without cap approximation into one literal two-time response
square.  After the first player's cap response, a second player has a pure
stopping-time improvement of at least one third of the finite-clock minimum
exploitability.  The corresponding first-disagreement row has a uniform full
opponent-survival floor, and the square has the same pair-deleted survival
floor already at its common source.

## 1. Input

Use the notation and alternative B of
`CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION`.
Thus `mu` minimizes full exploitability on the length-`K` controller class,

\[
 E_K(\mu)=\eta>0,
\tag{1}
\]

and there are distinct players `j,i`, an internal pure time `r` for `j`, and
a pure tester time `t` for `i` such that

\[
 \mu'=\mu[j\leftarrow\delta_r],
 \qquad
 U_j(\mu')-U_j(\mu)=\eta,
\tag{2}
\]

\[
 g_{i,t}(\mu)=\eta,
 \qquad
 g_{i,t}(\mu')-g_{i,t}(\mu)\ge\eta/3.
\tag{3}
\]

Assume all terminal reward coordinates have absolute value at most `M`, with
`M>0`.

## 2. Support-time extraction

For a pure time `a` of player `i`, abbreviate

\[
 V_a=V_{i,a}(\mu_{-i}),
 \qquad
 V'_a=V_{i,a}(\mu'_{-i}),
 \qquad
 \Delta_a=V'_a-V_a.
\tag{4}
\]

Because prescribed play mixes player `i`'s pure times according to `mu_i`,

\[
 U_i(\mu)=\sum_a\mu_i(a)V_a,
 \qquad
 U_i(\mu')=\sum_a\mu_i(a)V'_a.
\tag{5}
\]

Consequently the cross increment in (3) is exactly

\[
 \begin{aligned}
 g_{i,t}(\mu')-g_{i,t}(\mu)
 &=\Delta_t-\sum_a\mu_i(a)\Delta_a\\
 &=\sum_a\mu_i(a)
   \bigl[(V'_t-V'_a)-(V_t-V_a)\bigr].
 \end{aligned}
\tag{6}
\]

### Theorem 2.1

There is a pure time `s` in the support of `mu_i` such that

\[
 (V'_t-V'_s)-(V_t-V_s)\ge\eta/3.
\tag{7}
\]

Moreover,

\[
 V_t-V_s\ge0,
 \qquad
 \boxed{V'_t-V'_s\ge\eta/3.}
\tag{8}
\]

#### Proof

Equation (6) and averaging select a support time satisfying (7).  Since `t`
is cap-active at the source, `V_t-U_i(mu)=eta`.  By definition of
`E_K(mu)=eta`, every pure response time `s` has

\[
 V_s-U_i(\mu)\le\eta.
\]

Thus `V_t>=V_s`.  Adding this nonnegative source gap to (7) proves (8).
QED

The two times are distinct, because their child payoff difference is
positive.  Therefore they have one finite first-disagreement date `ell`.

## 3. Actual reach at the child and source

Let

\[
 H_{-i}(\mu',\ell)
 =\Pr_{\mu'}(T_k\ge\ell\text{ for every }k\ne i)
\tag{9}
\]

be full opponent survival to the first disagreement, and let

\[
 H_{-i,-j}(\mu,\ell)
 =\Pr_{\mu}(T_k\ge\ell\text{ for every }k\notin\{i,j\})
\tag{10}
\]

be pair-deleted survival.  The latter is unchanged when `j` moves from
`mu_j` to `delta_r`.

Before `ell`, the two observer deviations `t` and `s` prescribe the same
actions.  Their terminal payoffs can differ only on the event in (9), and on
that event their difference has absolute value at most `2M`.  Equation (8)
therefore gives

\[
 \boxed{
 H_{-i}(\mu',\ell)\ge {\eta\over6M}.}
\tag{11}
\]

Deleting player `j` only enlarges the event.  Since the remaining opponents
have identical laws at source and child,

\[
 \boxed{
 H_{-i,-j}(\mu,\ell)
 =H_{-i,-j}(\mu',\ell)
 \ge {\eta\over6M}.}
\tag{12}
\]

Thus the exact same-source package is

\[
 \boxed{
 \mu\xrightarrow[\text{player }j]{\text{cap gain }\eta}\mu',
 \qquad
 \mu'\xrightarrow[\text{player }i]{s\to t}
 \text{gain at least }\eta/3,}
\tag{13}
\]

with a source-attached pair-deleted reach floor `eta/(6M)` at the second
edge's literal disagreement date.

## 4. Relation to existing response-square machinery

Mixing player `j` only partway toward `delta_r` scales the square difference
in (7) exactly by the mixture amplitude.  Hence (7) is a full-chord endpoint
for the checked stopping-law response-square and first-disagreement
localization machinery.  No cap supremum has to be approximated: `r` and `t`
are already active at the finite controller minimizer, and `s` is an actual
prescribed support time.

This ancestry is stronger than the generic actual-profile paid-port theorem:
the first edge is a cap-attaining response, the second paid row is linked to
it by an exact response square, and both tester responses were selected by
one simultaneous KKT law at the common source.

It is still not a chronological Nash--Bellman chain.  The strategy
replacement at the first arrow is horizontal, and the second arrow is a
profitable deviation, not prescribed play.  Passing only the second endpoint
to the generic paid-cap port would forget the minimizer, multiplier, and
square ancestry.

## 5. Boundary tests

1. The constant in (11) is `eta/(6M)`: the paid pure-time gap is `eta/3`
   and two terminal payoff values can differ by `2M`.
2. Full opponent survival in (11) is a child event.  Only pair-deleted
   survival transfers unchanged to the source, because player `j` changed.
3. The support condition on `s` is literal and needed for (6).  An arbitrary
   pure time does not satisfy the averaging conclusion.
4. If `s` or `t` is Never, their positive difference still gives a finite
   first disagreement: the other time must be finite.
5. A pair-deleted reach floor is not an actual Never-mass floor.  Along
   growing clocks, all mass in (12) may remain at finite dates moving to
   infinity.

## Source audit

The KKT input is the separately frozen note
`CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION`,
SHA-256
`9efcc2aa99ec6dbbd799297c228b20be78e5b1ec43799a267423160dfcf5dab1`.

The pure-time first-disagreement factorization is the same finite stopping-law
identity used by `quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul`
in
`UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.
No paper theorem or external equilibrium selection is used.

## Nonclaims

- The source need not be a total-debt minimum or a finite timing-game Nash
  law.
- The child need not minimize `E_K`.
- The pair-deleted reach floor need not survive as an actual terminal Never
  atom.
- Neither arrow in (13) is an exact Nash--Bellman predecessor edge.
- No renewable rank, charged return, terminal approximate equilibrium, or
  uniform-equilibrium payoff is produced.

## Next exact question

As `K` grows, compactify the primal source laws, the dual KKT law, and the two
selected pure times jointly.  Either both times remain visible in one finite
window, giving a literal limiting response square, or at least one escapes.
Can the latter be strengthened from pair-deleted late survival to an actual
source-reprojected clock packet without assuming a positive Never mass?
