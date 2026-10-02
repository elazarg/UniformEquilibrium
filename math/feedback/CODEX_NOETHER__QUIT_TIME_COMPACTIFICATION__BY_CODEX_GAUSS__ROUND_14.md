# Round 14 Feedback on Quit-Time Compactification

Reviewer: `CODEX_GAUSS`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 45, Proposition 42 and its first-crossing corollary. I did not
audit the later assembly of the full corrected Simon Theorem 3 equivalence.

Status: `VALID_ORDINARY_MATHEMATICS_AFTER_STATED_WEAK_INEQUALITY_CORRECTION`

## Claim checked

At a reached row `a=p_t`, with reach probability `u>0` and actual continuation
payoff `r`, the note raises only player `i`'s continuation coordinate to

```text
bar_r_i = max(r_i, chi_i-eta).
```

It then simultaneously deletes a `beta`-bad Quit action and purifies a
`beta`-bad Continue action. Under the displayed endpoint-continuity, rationality,
no-sure-quitter, and corrected-uniform-`rho` hypotheses, the resulting row is
`eta`-supported and cannot contain a sure quitter. The important quantitative
conclusion is

```text
Q(a)-Q(a^sharp) <= n*alpha/(u*beta),
1-Q(a) >= rho-n*alpha/(u*beta).
```

The second inequality must be weak in general. The note now states it weakly;
the earlier strict version was false at equality boundaries. The strict lower
bound needed at the first survival crossing is nevertheless recovered from the
strict inequality `u>theta/3`.

## Bad-Quit deletion is paid by an attainable deviation

Fix a bad-Quit coordinate `i`. There are two cases.

- If `r_i >= chi_i-eta`, then `bar_r_i=r_i`. Continuing at the current row and
  following the prescribed tail realizes exactly the forced-Continue endpoint
  computed with `bar_r_i`.
- If `r_i < chi_i-eta`, fix the opponents' actual continuation strategies.
  Their corresponding unilateral-response supremum is at least the min--max
  value `chi_i`. Even if the supremum is not attained, `eta>0` gives an actual
  behavioral response with payoff strictly above `chi_i-eta=bar_r_i`.

Thus `bar_r_i` is not being treated as a fictitious continuation payoff. The
deviator agrees with the profile before date `t`, Continues at date `t`, and,
conditional on everybody else also Continuing, uses the selected tail response.
On current-row terminal outcomes the payoff is exactly the ordinary forced-
Continue terminal part. This realizes a conditional endpoint at least
`Continue_i(bar_r,a)`.

The prescribed conditional payoff is the affine mixture

```text
a_i*Quit_i(a) + (1-a_i)*Continue_i(r,a).
```

Since `bar_r_i>=r_i`, bad Quit produces conditional gain strictly larger than
`a_i*beta`. Multiplication by the reach probability gives

```text
a_i < alpha/(u*beta).
```

This argument uses only the defining `inf sup` orientation of `MinMaxQuit`; it
does not require a best response to attain the supremum.

## Bad-Continue purification and simultaneous endpoint control

If coordinate `i` is bad Continue against `bar_r`, monotonicity in the
continuation coordinate makes it bad Continue against the smaller actual
continuation `r`. Quitting at date `t` therefore gains more than
`(1-a_i)*beta`, so

```text
1-a_i < alpha/(u*beta).
```

Bad Quit and bad Continue cannot hold simultaneously because `beta>0`.
The two coordinate estimates and `alpha<u*beta*d` give
`dist(a^sharp,a)<d`; this is the Pi/sup metric calculation appearing in
`dist_supportPurifiedRow_lt` in `Literature/Simon2007.lean`, so no factor of
the player count is missing. Uniform endpoint continuity and
`beta+2e<=eta` then give `a^sharp in E_eta(bar_r)` by the ordinary two-action
support calculation represented by
`supportPurifiedRow_mem_epsilonRow_of_endpoint_close` in the same file.

Because `bar_r` is `eta`-rational and `eta<=sigma`, a bad-Continue coordinate
would turn into a sure quitter in an `E_sigma` row, contradicting
`exists_scale_without_sure_quitter_of_not_instant`. Hence no Continue action is
purified, `a^sharp<=a`, and only the quantitatively small bad-Quit coordinates
are deleted.

## Corrected uniform-`rho` application

`QuitTailPayoff.feasible` in `Literature/Simon2007.lean` proves that the actual
tail `r` is feasible. The note's normalization must include `0`, every
terminal coordinate, and every min--max coordinate in one interval of diameter
at most one; the current text now says exactly this. Consequently clipping a
coordinate from `r_i` to `max(r_i,chi_i-eta)` moves it by at most one, so
`bar_r` is `NearFeasible G 1`.

Monotonicity from `eta` to `rho` lets the corrected compact-set conclusion of
`lemma5_corrected_2012` apply to `a^sharp`, yielding

```text
Q(a^sharp) <= 1-rho.
```

The product Lipschitz estimate for coordinatewise deletion gives

```text
Q(a)-Q(a^sharp)
  <= sum_i (a_i-a^sharp_i)
  <= n*alpha/(u*beta).
```

Combining these proves the weak survival inequality stated above. An equality
case in the uniform-`rho` bound, with no deleted mass, shows why no strict sign
is available in this general line.

## First-crossing constants

Suppose `T` is the first index with

```text
S_T <= theta/3 < S_(T-1).
```

Then `u=S_(T-1)>theta/3`. From

```text
alpha <= rho*theta*beta/(6*n)
```

one obtains strictly

```text
n*alpha/(u*beta) < rho/2.
```

The weak general bound therefore gives
`1-Q(p_(T-1))>rho/2`, and hence

```text
theta*rho/6 < S_T <= theta/3.
```

All earlier survivals are at least `S_T`. The additional error bound
`alpha<=eta*theta*rho/6` is therefore sufficient for
`equilibrium_tail_rational` at every tail through `T`, and the hypotheses of
`exists_supportPurifiedPrefixPath` have the claimed honest common survival
floor. I found no hidden circular use of rationality at the crossing row.

The crossing lemma remains conditional on the existence of such a first `T`;
the subsequent full necessity proof must separately show survival eventually
falls below `theta/3`. Section 45 does not claim otherwise.

## Source and formal-status audit

The exact project transcription inspected was Simon (2007), Theorem 3,
Section 4.4, in `Literature/Simon2007.lean`, together with the corrected 2012
Lemma 2.1 statement `lemma5_corrected_2012`. The maintained primary-source
synthesis in `docs/references/20_NONZERO_SUM_EQUILIBRIUM.md` confirms the
arbitrary-quitting-game scope and the exact Theorem 3 alternatives.

The note's literal source locator `literature/Simon2007/raw-utf8.txt` is not
present in the refreshed workspace, and the current source policy recommends a
flat lowercase reading library. This is a reproducibility/citation-location
repair, not a mathematical objection: the note should cite the primary paper
and an actually present local locator rather than the stale path.

The crucial corrected uniform-`rho` result and full corrected Theorem 3 end in
`sorry` in the non-built Literature transcription. Proposition 42 is therefore
ordinary mathematics only. It repairs the isolated survival-jump implication;
it is not itself the full equivalence and supplies no checked semantic theorem.

## Verdict

After the already incorporated correction from strict `>` to weak `>=` in the
general survival inequality, Proposition 42 and the displayed first-crossing
corollary are valid ordinary mathematics. The min--max clipping is genuinely
attainable player by player, including when a tail best response is not
attained; simultaneous purification, scale monotonicity, and all constants
check. The only remaining local repair is the stale reading-library path.
