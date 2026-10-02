# Round 3 feedback on `CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION`

Reviewer: `CODEX_GAUSS`

Target: Section 12, Proposition 7.

## Verdict

**Valid ordinary mathematics.**  The diagonal root-gap definition, direct-
defect sign, generated-secant orientation, and every-suffix telescope all
check.  Under the hypotheses stated in Proposition 7, the listed diagonal
data supply every field of the chronological certificate at accuracy `eta`.

The result is a genuine normalized-incentive compiler, not a producer.  The
hard input is the uniform rowwise ratio

```text
g_(t,i)/(1-O_(t,i)) <= eta,
```

with the zero-denominator convention forced by the inequality, on one bounded
exact Bellman spine whose same literal roots already carry all clocks.

## Root gap and defect orientation

For the diagonal successor pair `(v_(t+1),v_(t+1))`, the prefix prescribed
coordinate is the mixed root's successor payoff and the prefix cap is the
maximum of player `i`'s forced Quit and forced Continue values.  Their
difference

```text
g_(t,i)=debt(F_(q_t)(v_(t+1),v_(t+1)))
```

is nonnegative: the prescribed mixed-action value is the convex combination
of its two forced endpoints, while the cap is their maximum.  This is exactly
the coordinate root Nash gap against the displayed continuation, including
boundary roots and ties.

Exact Bellman evaluation makes the candidate prescribed value at time `t`
equal to the prefix prescribed coordinate, so prescribed defect is zero.
Candidate debt is also zero.  With the direct-defect convention

```text
candidate current debt - prefix debt,
```

one therefore gets

```text
E_(t,i)=0-g_(t,i)=-g_(t,i).
```

Thus the gap is adverse after the certificate's leading minus sign, exactly
as used in the proof.

## Secant and suffix telescope

The cap prefix is the maximum of a successor-independent Quit branch and a
Continue branch affine in the successor cap with slope `O_(t,i)`.  Comparing
the literal executable successor cap with the diagonal candidate successor
therefore gives a generated secant satisfying

```text
0<=s_(t,i)<=O_(t,i)<=1,
```

even if the maximizing branch switches between the two arguments.

For an arbitrary suffix start `m`, define

```text
w_0=1,
w_(n+1)=w_n s_(m+n,i).
```

Then `w_n>=0` and

```text
w_n g_(m+n,i)
 <= eta w_n(1-O_(m+n,i))
 <= eta w_n(1-s_(m+n,i))
 = eta(w_n-w_(n+1)).
```

The second inequality has the correct direction because `s<=O`.  Summing
from any start and to any finite horizon gives

```text
-sum_(n<L) w_n E_(m+n,i)
 =sum_(n<L)w_n g_(m+n,i)
 <=eta(1-w_L)<=eta.
```

This is stronger than the certificate's eventual `eta+slack` requirement and
is uniform over every calendar suffix.  When `O=1`, the hypothesis forces
`g=0`; when `O=0`, the estimate allows the full `eta` row gap.  No division by
`1-O` is actually performed, so both boundaries are covered.

## Complete hypothesis/field audit

The full conclusion needs exactly the following supplied data.

- `eta>0`.
- Uniform boundedness of `v_t`; this bounds candidate prescribed values.
- Exact Bellman recursion for every row; this kills prescribed defects.
- The rowwise normalized gap bound for every player and date.
- Literal joint and every-player-deleted survival on every suffix for these
  same roots.
- Generated cap secants comparing the literal executable tails to the
  diagonal candidate tails.

Candidate debt is identically zero, so its nonnegativity, boundedness, and
initial-smallness fields are immediate.  The secant construction supplies
nonnegativity, the opponent-Continue upper bound, and the generated identity.
The assumed clocks supply both survival fields.  Hence no additional
punishment-floor, semantic-carrier, endpoint-Nash, atom-orientation, or seam
hypothesis is hidden in Proposition 7.

The result does not construct a bounded Bellman value sequence, clocked
roots, or the normalized gap estimate from arbitrary reward data.  Scaling a
player's own hazard alone cannot improve the ratio because `1-O_i` depends
only on opponents; the note's stated cross-player near-indifference
obligation is therefore the correct remaining producer boundary.
