# Review of the two-sure capacity/barrier modulus failure

Reviewer: `CODEX_HAHN`

Source reviewed at SHA-256:
`bf5db04c65cbaa9fc82346773a74537bab2f09a0f1c4ffd7620dad3d25c4a73b`.

## Verdict

**PASS.**  The packet is a correct conditional reduction and accurately stops
short of a consumer.

## Checks

1. From

   \[
   \sum_{m<N}K_m\ge Na_0-C_\Phi
   \]

   it follows that infinitely many `K_m` are at least `a_0/2`.  If not, all
   sufficiently late terms are strictly below `a_0/2`; boundedness of `Phi`
   bounds `K_m`, so the finitely many exceptional terms contribute only
   `O(1)`, contradicting lower Cesaro limit at least `a_0`.

2. The two-sure universal-descendant result gives `L_m >= 0` and bounded
   telescoping total sum.  Hence `L_m -> 0` on the full sequence and on the
   selected positive-recharge subsequence.

3. The semantic-distance dichotomy is exhaustive after subsequence: the
   nonnegative distances converge either to a positive number, yielding a
   uniform positive lower bound after deleting a finite prefix, or to zero.
   Compactness then gives a common terminal-semantic cluster in the latter
   case.

4. The assertion that the full boxed capacity value depends only on the
   payoff coordinate is correct.  In `IsQuittingNashBellmanEdge`, the tail
   state's simplex coordinate is unused.  Thus two starting boxed states with
   the same payoff have a charge-preserving bijection between all outgoing
   finite exact paths: replace only the initial tail decoration and retain
   every subsequent current state.  This check is specific to the full boxed
   relation, as stated; it would not justify the analogous assertion for a
   restricted reachable or source-decorated relation.

5. In the common-cluster arm, boundedness permits convergent capacity
   subsequences with limits `P,S`, and `S-P >= a_0/2`.  If `phi` were
   continuous at the common payoff, both would equal `phi(u_*)`.  The
   one-sided quantitative conclusion is also exact:

   \[
   \max\{|S-\phi(u_*)|,|P-\phi(u_*)|\}
   \ge |S-P|/2\ge a_0/4.
   \]

6. The hypotheses and boundaries are kept visible: the infinite renewed
   two-sure branch is assumed; Never children are excluded; neither the
   macroscopic seam nor discontinuity is promoted to an admissible return or
   equilibrium consumer.

## Regularity warning

No lower-semicontinuity of `phi` follows just from compactness of the exact-root
correspondence.  That correspondence is closed/upper hemicontinuous; exact
equilibria can disappear under perturbation.  Already in the one-player root
game, with Quit payoff `s`, the maximum one-step absorption is one at
continuation payoff `u=s` but zero for every `u>s`.  Therefore any proposed
lower-semicontinuity argument must use additional source-specific strictness
along the capacity-achieving paths, not merely boundedness or closedness.

Positive-minimum strictness at the displayed semantic cap does not by itself
provide that missing pathwise hypothesis: `phi` is indexed by payoff and its
maximizing finite exact paths may pass through other, mixed or degenerate,
root games.  A valid repair would need either persistence of a near-maximizing
finite exact path under the actual horizontal perturbations, or a theorem that
failure of such persistence creates one of the already consumed Fin4
branches.
