# Round 7 Feedback on Curl-Free Toggle Potential

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`

Scope: only Section 29, Propositions 37--38. I refreshed and read the current
file before checking them. This is an ordinary-mathematics audit, not an
export or Lean claim.

Status: `VALID; EXACT POLARITY BOUNDARY`.

## Proposition 37

The strengthened all-finite-leakage ledger is correct. For a member `i` of
`A`, replacing `i` by pure Never has the following exact pointwise effects.

- An outcome excluding `i` is preserved and continues to pay one.
- `A` becomes the partner singleton, so payoff falls from two to one.
- Every other containing coalition of size at least two becomes a nonempty
  coalition excluding `i`, so payoff rises from zero to one.
- The own singleton pays `-2`; after deletion the payoff is either zero at
  all-Never or one at a later opponent coalition, so the gain is at least two.

Thus the deviation gain is bounded below by exactly the displayed ledger

```text
2*p_{ {i} } + sum_{U: i in U, |U|>=2, U!=A} p_U - a.
```

The same statement holds for a member of `B`. On summing the four Nash
inequalities, each singleton is counted once with coefficient two and each
multi-coalition leakage outcome is counted `|U|>=2` times. Neither `A` nor
`B` leaks into the other pair's containing-coordinate sum. Division by two
therefore gives

```text
a+b >= ell_single+ell_multi-2*epsilon.
```

The coefficient statement is also right: replacing `-2` by `-K` gives total
singleton coefficient `K`, which becomes `K/2` after the summed inequality is
divided by two. The common unit coefficient occurs at `K=2`.

Boundary falsifiers behave as claimed. At pure `A` (and symmetrically `B`),
members lose by leaving and outsiders lose by joining. At all-Never, every
finite unilateral quit time earns the negative own singleton reward, while
Never earns zero. All three profiles are exact terminal Nash, so Proposition
37 is a ledger strengthening rather than a counterexample.

## Proposition 38

The pointwise polarity no-go is exact. Test the asserted singleton-deletion
gain on the realization where player `i` quits at the first date and every
opponent Never. Deleting `i` changes payoff from `r({i})_i` to the terminal
all-Never payoff zero, hence

```text
r({i})_i <= -kappa_i < 0.
```

Against all-Never opponents every finite pure quit time then earns that same
negative solo reward and pure Never earns zero. Mixtures cannot improve on
zero, so all-Never is exact terminal Nash. The proposition correctly limits
itself to pointwise singleton charging; it does not exclude a cross-history
profile-dependent account.

## Verdict

Both propositions survive falsification. Proposition 37 sharpens Cedar's
multi-leakage ledger to every finite leakage outcome. Proposition 38 shows
why this clean deletion architecture cannot also remove the remaining Never
mass: uniform positive pointwise singleton charges force every own solo
negative and restore all-Never. The live repair must use cross-history or
multi-owner compensation, not another exact indicator deletion.
