# Review of Propositions 9--10 in `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL`

Reviewer: `CODEX_CEDAR`
Scope: only Sections 18--19, especially the endogenous-target theorem, the
conditional face-gap criterion, and the four-player standard-Q-side witness.
Status: `VALID_ORDINARY_MATHEMATICS_WITH_ADAPTER_QUALIFICATION`

## Claim reviewed

For a fixed-point-free permutation `pi` and a closed probability box
`[alpha,beta]^I`, `0 < alpha < beta <= 1`, define for player `i`:

- `R_i`, the pure-Quit endpoint reward against the opponents' product root;
- `W_i`, the unconditional contribution when `i` Continues and at least one
  opponent Quits;
- `c_i = product_(j != i)(1-p_j)`;
- `V_i = W_i/(1-c_i)`; and
- `G_i = R_i-V_i`.

Proposition 9 derives strict blocker-face signs from literal reward extrema.
Proposition 10 assumes those signs directly.  Both claim an interior zero of
all `G_i`, an exact stationary fixed point with target `V`, and hence a uniform
equilibrium payoff against unrestricted behavioral deviations.  Section 19
also claims a finite tensor-Bernstein sufficient test and an explicit
four-player reward table `r*` whose singleton matrix is the checked
`fourMatrix` but whose multi-quitter rows satisfy the face signs.

## Findings

### 1. Conditional normalization and closed-box continuity are correct

The lower margin `alpha>0` is sufficient on the entire closed box.  Since the
designated opponent `pi(i)` has Quit probability at least `alpha`,

`c_i <= 1-alpha < 1`.

Thus `1-c_i` never vanishes and `V_i=W_i/(1-c_i)` is continuous.  Conditional
on `i` continuing and some opponent quitting, `V_i` is exactly a convex
combination of the actual continuer rewards `r(S)_i` for nonempty
`S subset I-{i}`.  No assumption `beta<1` is needed.

At a zero `R_i=V_i`, the pure-Continue endpoint is

`W_i+c_i V_i=(1-c_i)V_i+c_iV_i=V_i`.

Hence both pure endpoints equal `V_i`.  Because the produced `p_i` is strictly
between `alpha` and `beta`, each player genuinely mixes, but equality of the
two endpoints is already enough for exact endpoint Nash.

### 2. Proposition 9's range-to-face estimates have the right orientation

On the lower blocker face, conditioning first on the quitting subset
`T subset K_i` gives the quitter value

`(1-alpha) r(T union {i})_i + alpha r(T union {i,pi(i)})_i`.

It is bounded below by `(1-alpha)H_i^-+alpha L_i^-`, while `V_i<=C_i^+`.
The first displayed strict inequality therefore gives `G_i>0`.  The analogous
upper bounds give `G_i<0` on the upper face.  This remains valid when `T` is
empty; the quitter coalition still contains `i`.

### 3. Reindexing and the Brouwer step are valid

Because `pi` is a permutation,

`F_j=G_(pi^{-1}(j))`

places the positive/negative signs on the lower/upper face of coordinate `j`.
For any fixed `lambda>0`, the clamped map

`Phi_j(p)=clamp(p_j+lambda F_j(p))`

is continuous.  At a fixed point, a lower-face coordinate with `F_j>0` and an
upper-face coordinate with `F_j<0` are impossible, so every coordinate is
interior.  At an interior fixed coordinate the clamp cannot hide a nonzero
increment; hence `F_j=0`.  Bijectivity is genuinely used here, exactly as the
note states.

### 4. The stationary semantic compilation is complete

Let `v=V(p)`.  Equality of both pure endpoints to `v_i` implies both exact
root endpoint Nash and

`v = quittingRootSuccessorPayoff reward v root`.

Every `p_i>=alpha>0`, so joint Continue mass is below one.  For every player
`i`, the designated opponent `pi(i)` Quits with positive probability, so the
player-deleted Continue mass is also below one.  These are exactly the
absorption and contraction inputs of
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
(`EndpointCompiler.lean`).  That checked theorem concludes the fixed target is
a uniform-equilibrium payoff against all unilateral behavioral strategies,
not merely stationary or one-shot deviations.

### 5. The division-free and tensor-Bernstein adapter is sound

With

`N_i=(1-c_i)R_i-W_i=(1-c_i)G_i`,

the factor `1-c_i` is strictly positive, so `N_i` and `G_i` have the same sign.
After fixing a blocker face, `R_i`, `W_i`, and `c_i` are multilinear in the
`|I|-2` remaining opponent probabilities.  The product `(1-c_i)R_i` therefore
has degree at most two in each such variable.  Rescaling the box to the unit
cube and using the tensor Bernstein basis of multidegree two gives exactly
`3^(|I|-2)` coefficients.  Strict positivity, respectively negativity, of all
coefficients is a valid finite exact-arithmetic sufficient test by the
nonnegative partition of unity.  It is not necessary, as the note correctly
states.

### 6. The four-player `r*` estimates check exactly

Under the order `(d,0,1,2)`, the checked `fourMatrix` is exactly

```
[ 0  1  1  1
  1  0 -1  2
  1  2  0 -1
  1 -1  2  0 ].
```

For the proposed `r*`, every own singleton reward is the diagonal entry zero.
Therefore its normalized singleton entry is

`r*({owner})_i-r*({i})_i=M_(i,owner)`.

This establishes, in ordinary mathematics, that the normalized singleton
matrix is `fourMatrix`.  The named Lean declarations
`fourMatrix_hasNormalPlayers`, `fourMatrix_normal_noHomogeneous`, and
`fourMatrix_normal_standardQ` then supply the three matrix facts once that
adapter equality is formalized.

Fix `i` and let `z` be the probability that at least one of the two
nondesignated background opponents Quits.  With both probabilities in
`[1/4,3/4]`,

`7/16 <= z <= 15/16`.

The quitter endpoint is exactly

`R_i=64((1-p_(pi(i)))z-p_(pi(i)))`.

At the lower blocker face its minimum is

`64((3/4)(7/16)-1/4)=5`,

and at the upper face its maximum is

`64((1/4)(15/16)-3/4)=-33`.

When `i` Continues, any multi-quitter opponent coalition pays zero to `i`, and
singleton opponent coalitions pay entries of `M`, all in `[-1,2]`.  Thus
`-1<=V_i<=2`, giving exactly `G_i>=3` on lower faces and `G_i<=-32` on upper
faces.  These are uniform closed-face bounds, not a numerical-root experiment.

## Qualification and novelty boundary

Propositions 9 and 10 are valid strict special-case producers in ordinary
mathematics.  The exact `r*` reward-table definition, its normalized-matrix
equality, and the finite Bernstein coefficient checker are not named checked
Lean declarations.  They must not inherit an `L` or actual-data adapter seal
from the checked matrix facts alone.

The result is genuinely distinct from the *strategic conclusion* of the
standard-Q/LCP gate.  `StandardQMatrixSide` records only the normal-core matrix
regime, and the checked gate explicitly supplies no stationary strategy in
that branch.  Proposition 10 uses the multi-quitter rows, which the singleton
matrix forgets, to construct a stationary fixed point.  This establishes a
new positive subclass inside the standard-Q side; it does not refute or solve
the remaining standard-Q class as a whole.

I found no counterexample to either proposition.  The approximate numerical
root is unnecessary for validity and was not used in this review.

## Concrete next check

Formalize the literal four-player table and prove its normalized singleton
matrix equality plus the two face bounds directly.  Separately formalize the
general face-gap Brouwer theorem; the tensor-Bernstein checker can remain a
sufficient adapter layered on top.
