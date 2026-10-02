# Round 10 review of `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION`

Reviewer: `CODEX_CEDAR`

Scope: only Section 45, Proposition 42 and its first-crossing corollary.  I
checked the clipped min--max response, global deviation attainability,
purification constants, no-sure and uniform-rho dispatches, and survival
indices.  I did not audit the later Simon orbit/purification assembly.

## Verdict

**VALID ordinary mathematics**, with the author's corrected weak general
survival inequality

```text
1-Q(a) >= rho - n alpha/(u beta).
```

The first-crossing consequence is strictly `>rho/2` under the stated global
constant because the pre-crossing survival is strictly `u>theta/3`.

This does repair the monotonicity/first-crossing circularity: the corrected
uniform-rho lemma is applied first to an attainable floor-clipped row, and
only the resulting lower survival bound is used to infer rationality of the
actual reached tails.  It does not prove the full corrected Simon Theorem 3.
In particular, `lemma5_corrected_2012` and the later source assembly remain
non-built `sorry` declarations in `Literature/Simon2007.lean`, so no new Lean
or integration status follows from this review.

## 1. Fixed-opponent min--max quantifier

For player `i`, write

```text
U_i(qOpp) = sup over i's tail responses of the tail payoff,
chi_i      = inf over opponent profiles of U_i.
```

For the actual prescribed opponents after the crossing row,
`U_i>=chi_i`.  If `r_i<chi_i-eta`, then `eta>0` (because `beta,e>0` and
`beta+2e<=eta`), so

```text
chi_i-eta < U_i.
```

The supremum need not be attained: strict inequality below a bounded,
nonempty supremum still supplies one behavioral tail response with payoff
strictly above `chi_i-eta`.  This is exactly the quantifier needed.  It does
not require a min--max optimizer or a globally selected best response.

After forcing Continue at date `t`, the deviator uses that response from
`t+1` onward.  Conditional on opponents also continuing at `t`, it raises the
tail coordinate to more than `bar_r_i`; on absorption by opponents at `t`,
the payoff is unchanged.  Hence its conditional current payoff is at least
`ForcedContinuePayoff(bar_r,a,i)`.  If the opponent continuation probability
is zero, the inequality is equality, which is still enough because the
bad-Quit endpoint gap is strict.

## 2. Bad-Quit and bad-Continue charges

Let `C_r`, `C_bar`, and `Q` be the actual Continue, clipped Continue, and Quit
endpoints for one coordinate.  Monotonicity gives `C_bar>=C_r`, while the
prescribed conditional payoff is

```text
a_i Q + (1-a_i) C_r.
```

At a bad-Quit coordinate, `Q<C_bar-beta`; forcing Continue and using the
attainable tail response therefore gains strictly more than

```text
C_bar - [a_i Q+(1-a_i)C_r] > a_i beta.
```

Splicing this deviation after the prescribed prehistory multiplies the gain
by the exact reach probability `u`.  Global `alpha`-equilibrium yields

```text
a_i < alpha/(u beta).
```

At a bad-Continue coordinate, `C_bar<Q-beta` implies the stronger actual
comparison `C_r<Q-beta`; forcing Quit gains more than `(1-a_i)beta`, giving

```text
1-a_i < alpha/(u beta).
```

These are global behavioral deviations, not fictitious one-stage terminal
tests.  Their pre-crossing actions agree with the prescribed profile and
their post-crossing behavior is explicitly available.

## 3. Purification and scale dispatches

Under the standard finite-product sup metric on quit rows, every changed
coordinate moves by less than `alpha/(u beta)<d`, hence
`dist(aSharp,a)<d`.  If another norm is used, its finite-dimensional
equivalence factor must be absorbed into `d`; the ordinary statement and the
Pi/sup convention used by the transcription have the displayed constant.

Uniform endpoint continuity moves each of Quit and Continue by less than
`e`.  Unchanged coordinates had both endpoint gaps at most `beta`; the
simultaneous row change enlarges either gap by at most `2e`.  Coordinates set
to `0` or `1` retain only the appropriate supported inequality.  Thus
`beta+2e<=eta` gives `aSharp in E_eta(bar_r)`.

The clipped vector is `eta`-rational coordinatewise.  It is also
`NearFeasible G 1`: the actual tail `r` is a convex mixture of zero and the
finitely many terminal payoff rows, while normalization puts `r`, every
min--max coordinate, and zero in a common coordinate interval of diameter at
most one, so `||bar_r-r||<=1`.

If a bad-Continue coordinate existed, `aSharp_i=1`.  Since `eta<=sigma`,
monotonicity upgrades both rationality and row error from `eta` to the
no-sure scale `sigma`, contradicting
`exists_scale_without_sure_quitter_of_not_instant`.  Therefore no such
coordinate exists and `aSharp<=a` coordinatewise.

Likewise `eta<=rho` upgrades the clipped data to the corrected uniform-rho
hypotheses.  The `NearFeasible G 1` condition is present, so the corrected
lemma gives `Q(aSharp)<=1-rho`; no application is made to the not-yet-known
rational actual tail.

## 4. Absorption and first-crossing constants

Only bad-Quit coordinates are deleted.  The elementary product Lipschitz
bound for coordinatewise `aSharp<=a` gives

```text
Q(a)-Q(aSharp)
  <= sum_i (a_i-aSharp_i)
  <= n alpha/(u beta).
```

Combining this with `Q(aSharp)<=1-rho` proves the weak inequality in the
verdict.

At the first crossing,

```text
S_T<=theta/3<S_(T-1)=u.
```

If `alpha<=rho theta beta/(6n)`, then strict `u>theta/3` yields

```text
n alpha/(u beta) < rho/2,
1-Q(a) > rho/2,
S_T=u(1-Q(a)) > theta rho/6.
```

Thus the repaired interval is exactly
`(theta rho/6,theta/3]`.  If the global error is also at most
`eta theta rho/6`, every tail through the crossing has reach probability at
least this lower endpoint and `equilibrium_tail_rational` supplies actual
`eta`-rationality.  The additional bootstrap condition
`alpha<u beta d` can be imposed uniformly using `u>theta/3`, for example by
also requiring `alpha<theta beta d/3`; it belongs in the eventual full
constant ledger, as the note acknowledges.

## 5. Exact remaining scope

Proposition 42 is a universal conditional no-jump lemma and materially fixes
the source proof's first-crossing seam.  It still assumes the two structural
scales obtained after excluding instant and stationarily generated branches,
and the corrected uniform-rho source declaration is not proved in Lean here.
The later conversion from the rational prefix to an unbounded approximate
orbit/cycle also remains to be assembled.  Therefore the valid conclusion is
the survival-jump repair, not the full Simon necessity theorem and not the
finite-quitting uniform-equilibrium conjecture.

