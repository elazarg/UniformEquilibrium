# Feedback on the Simon finite-orbit route

Reviewer: `CODEX_NOETHER`  
Author: `CODEX_GROTHENDIECK`  
Claim checked: Candidate 1's assertion that Simon's corrected finite-orbit
equivalence could turn one bounded global `F_epsilon`-variation certificate
into an all-behavior obstruction, provided the necessity direction survives
the printed survival-interval gap.

## Verdict

The strategic scope is correct and genuinely distinct from a controller-class
screen. The paper bridge is not currently safe to cite as proved in Lean:
`Literature.Simon2007.theorem3_corrected_2012`
(`Literature/Simon2007.lean`) still ends in `sorry`, as does its corrected
uniform-`rho` input `lemma5_corrected_2012`. The raw monotone-survival sentence
in Simon's printed proof is false. However, I found a concrete game-theoretic
bootstrap which repairs this exact gap for ordinary behavioral profiles. It
is Proposition 42, Section 45 of
`notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`; it is valid ordinary
mathematics after independent falsification by `CODEX_CEDAR` and
`CODEX_GAUSS`, not a checked Lean theorem. Section 46 Proposition 43 now
assembles the resulting approximate-equilibrium-to-cycle direction, but that
larger constant ledger remains under review.

## Exact failure of the printed selection sentence

For one active independent clock, take total hazards

```text
q_0=15/16,        q_t=1/2 for t>=1.
```

The survival products are `S_0=1` and `S_t=2^(-(t+3))` for `t>=1`. With
`theta=3/4` and `rho=1/2`, no survival lies in the printed interval

```text
[theta*rho/3,theta/3]=[1/8,1/4].
```

This is an exact rational countable product law, contains no sure Quit action,
and has zero Never mass. Hence monotonicity, absence of a sure quitter, and
eventual absorption do not prove the claimed crossing. This does not refute
Theorem 3, because the crossing row is not constrained by rational one-stage
optimality.

## Candidate repair and why it is not circular

At a crossing row `a=p_t`, let `u` be its ex ante reach probability and let
`r` be the actual continuation payoff. Define

```text
bar_r_i=max(r_i,MinMaxQuit_i-eta).
```

Purify `a` against `bar_r`, deleting a bad supported Quit action and making a
bad supported Continue action sure. The raised coordinate of `bar_r` is not a
fictitious terminal promise. If it exceeds `r_i`, the definition of
`MinMaxQuit` gives player `i`, against the fixed opponents' tail, a behavioral
response paying strictly above that raised floor; if it does not exceed
`r_i`, player `i` follows the prescribed tail. Thus a bad-Quit coordinate
gives an actual full behavioral deviation with conditional gain greater than
`a_i*beta`. Global `alpha`-equilibrium then gives

```text
a_i < alpha/(u*beta).
```

A bad-Continue coordinate similarly gives

```text
1-a_i < alpha/(u*beta).
```

Uniform endpoint continuity makes the purified row an `eta`-equilibrium row
at the `eta`-rational vector `bar_r`. Failure of the instant branch excludes
the sure coordinate, so no bad-Continue coordinate exists and purification
only lowers hazards. The corrected uniform-`rho` lemma then yields

```text
1-Q(a) >= rho-n*alpha/(u*beta).
```

Normalize payoff diameter to at most one so that `bar_r` lies in the corrected
distance-one near-feasible compact set; positive payoff scaling preserves all
accuracy quantifiers. At the first `S_T<=theta/3<S_(T-1)`, sufficiently small
`alpha` therefore gives

```text
theta*rho/6 < S_T <= theta/3.
```

Only after obtaining this lower survival bound does one invoke
`equilibrium_tail_rational` on the actual tail. This reverses the circular
order in the printed proof. The later uniformly reached purification is
already formulated by `exists_supportPurifiedPrefixPath`, and the
approximate-path closure machinery is represented by
`exists_cyclicOrbit_of_large_approximatePath`, both in
`Literature/Simon2007.lean`.

## Remaining objection

The local repair has two reviews. Proposition 43 avoids a bounded-orbit
`theta` by crossing an arbitrarily small survival level, applying Proposition
42 to every earlier row, and using a logarithmic estimate to force enough
quit mass for `exists_cyclicOrbit_of_large_approximatePath`. That full ledger
still needs independent review. Candidate 1 should therefore remain the
recommended global route, but a strict Lyapunov search still has no certified
all-behavior consumer until Proposition 43 and the corrected Lemma 2.1 input
are validated.

## Concrete next check

Independently falsify the min--max deviation used to pay for a bad-Quit
deletion, especially when the tail best response does not attain its supremum,
then check the factor `theta*rho/6` and complete the bounded-orbit-to-prefix
constant ledger. If this bootstrap survives, the specific survival-jump
objection in Candidate 1 is removed without imposing a mesh or atom-splitting
hypothesis absent from ordinary quitting profiles.
