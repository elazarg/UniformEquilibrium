# Independent review of Propositions 6AQ--6AT

Reviewer: `CODEX_CEDAR`

Reviewed note:
`notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`.

## Verdict

**6AQ, 6AR as a one-coordinate chart, 6AS as a fixed-head arbitrary-common-
scale reconstruction, and 6AT are valid ordinary mathematics.**  There is,
however, one substantive gap in the claimed composition of 6AR with 6AS:
conditioning a product packet generally produces a different adaptive inner
scale in each coordinate, while 6AS rebuilds the later packet with one common
inner scale.  No equality, selection, or actuator in the current statements
aligns those coordinatewise scales.  Thus the propositions remove the scalar
parametrization obstruction but do not yet give an exact whole-profile
successor restart in the original common-scale frozen fiber.

This is a **REVISE** verdict for the combined restart claim, not for the four
displayed scalar propositions.  The safe conclusion is a coordinatewise
zero-cost chart plus a separately valid common-scale packet rebuild.  A valid
whole-profile continuation needs either a vector-inner-scale packet theorem,
an exact scale-equalization word, or a selection forcing the relevant
posterior updates to coincide.

## 1. Proposition 6AQ: optimal posterior actuator

Let the target component have incoming weight `p`, component Continue
probabilities `u,v`, aggregate Continue mass `c`, and desired posterior `b`.
The exact constraints are

```text
(1-p)u=c(1-b),       pv=cb.
```

Hence

```text
c <= min((1-p)/(1-b),p/b).
```

If `p<=b`, the second bound is active: `v=1`,
`u=p(1-b)/((1-p)b)`, `c=p/b`, and the executed Quit hazard is
`(b-p)/b`.  If `b<=p`, the first bound is active: `u=1`,
`v=b(1-p)/(p(1-b))`, `c=(1-p)/(1-b)`, and the hazard is
`(p-b)/(1-b)`.  All probabilities lie in `[0,1]`, including equality
`p=b`.

The estimates

```text
|p-b| <= Lambda(p,b) <= |p-b|/rho
```

for `b in [rho,1-rho]` follow directly from the two denominators.  Thus the
executed actuator cost is `o(h)` exactly when the posterior mismatch is
`o(h)` on a uniformly interior target fiber.

The sharpened latent-component mesh accounting is also exact:

```text
p<=b:  1-u=Lambda/(1-p),  1-v=0;
b<=p:  1-u=0,             1-v=Lambda/p.
```

There is no hidden observable latent controller.  One may define the two
complete component laws with the displayed next-row coins and prescribed
tails, mix those complete laws, and then use the ordinary hazard
representation of the resulting stopping-time distribution.  Conditional on
aggregate Continue, its residual law has posterior `b`.  Successive
one-coordinate rows are likewise ordinary product roots, with all other
coordinates forced to Continue at that row.

The source/inner-reset/original-replacement distinction is now stated
correctly.  In the frozen radial packet, the actuator reconnects the later
source and later **inner reset** as the two outer components.  The later
original full replacement is grafted separately behind its own frozen
endpoint prefix.  The outer source connector is actually reached only when
all coordinate prefix survivals are positive; the endpoint graft remains
counterfactual unless its own prefix has positive reach.  No atom or rectangle
cap survives merely from the posterior algebra.

## 2. Proposition 6AR: exact coordinatewise nested gauge

The collapse

```text
(1-w)A+w[(1-h)A+hR]=(1-wh)A+whR
```

is exact.  After a cutoff with component survivals `S,Q`, the surviving
replacement posterior and the refactored inner scale are

```text
e=whQ/D,       h^+=e/w=hQ/D,
D=(1-wh)S+whQ.
```

The refactorization with the same outer weight `w` is literal.  Its
admissibility condition `e<=w` is equivalent to

```text
h(1-w)Q <= (1-wh)S.
```

For `S>0`, writing `r=Q/S` gives

```text
h^+=hr/(1-wh+whr).
```

Along `h->0` under the displayed admissibility condition, `h^+->0` iff
`hr->0`.  One direction is immediate; for the other, admissibility bounds
`hr` and any subsequence bounded away from zero leaves `h^+` bounded away
from zero.  The special limit `r->1` gives `h^+/h->1`.

This is a zero-added-root, one-coordinate identity.  Positive cutoff reach is
still required before its residual is an actually reached successor.

## 3. The product-scale mismatch between 6AR and 6AS

Apply 6AR to a product packet with common incoming inner scale `h`.  In
coordinate `j`, let the source and replacement prefix survivals be `S_j,Q_j`.
The exact residual scale is

```text
h_j^+ = h Q_j / ((1-w_j h)S_j+w_j h Q_j).           (*)
```

There is no reason for `h_j^+=h_k^+` for two distinct active coordinates.
The survival ratios and outer weights may differ.  Thus the whole residual
profile is naturally a **vector-scale** nested mixture, even though every
coordinate retains its old outer weight.

Proposition 6AS instead defines, at the later frozen head,

```text
P_s(j)=(1-w_j s)A_j+w_j sR_j
```

with one common scalar `s`.  Taking `s=h_j^+` reconnects coordinate `j` but
generally not the other active coordinates.  The assertion that “the adaptive
value `h^+` produced by 6AR can be used as the inner scale of a packet” is
therefore valid for one coordinate or under an added equality hypothesis, but
not yet as an exact whole-profile frozen-packet restart.

This is not repaired merely by observing that arbitrary common `s` is legal.
One needs one of the following new statements:

- a packet construction with independently chosen `s_j`, together with one
  declared scale and all atom/error/clock estimates needed by the consumer;
- an exact actuator/equalizer which changes the vector `h_j^+` to one common
  scale at sublinear total cost; or
- a cutoff/subsequence theorem forcing the relevant values in `(*)` to agree.

The finite-player fact that all `h_j^+` may tend to zero is insufficient for
literal common-fiber equality.

## 4. Proposition 6AS itself

For a fixed late source `A`, replacements `R_j`, outer weights `w_j`, and
positive endpoint gain floors `g_j`, the effective complete-law weight is
exactly `w_j s`.  Under `w_j s<=1/2`, the named ever-Quit estimate gives

```text
w_j s g_j/(2M) <= EverQuitMass(P_s(j)).
```

With

```text
kappa=min(w_first g_first/(4M),w_second g_second/(4M)),
```

both ever-Quit masses are at least `2 kappa s`; the finite-cutoff theorem
therefore supplies one common cutoff with both raw marginal hazard sums at
least `kappa s`.

The atom transport constants also check.  Each active coordinate changes
from `A_j` with effective complete-law weight at most `s`, so finite-face
telescoping costs at most `ns` on each of the source and endpoint sides.
Multiplication by the reward bound gives the `2Mns` atom loss, and the
uniform opponent-law cap coupling gives the rectangle debt increment
`4Mns`.  The condition

```text
2KMns <= q/8
```

is exactly the earlier Proposition 6S threshold with `h` replaced by the
freely chosen `s`.  Hence the output charge `q/2`, error `e+4Mns`, terminal,
and rectangle pure-time orientation are valid.

Accordingly 6AS genuinely proves that the *fixed frozen head* can be rebuilt
at any sufficiently small common inner scale without using the frontier's
recorded scale.  It does not prove that an arbitrary conditioned product
residual has that common scale, bound maximum root mesh, preserve positive
component reach, select the required cutoff ratios, or supply the rectangle
observer-deleted cap port.

## 5. Corollary 6AT

Complete-law affinity gives

```text
Pr_{(1-e)A+eR}(C)-Pr_R(C)
  =(1-e)(Pr_A(C)-Pr_R(C)).
```

Overriding a distinct observer leaves the same affine mover comparison, so
the identity covers the rectangle atom as stated.  If `|r_o(C)|<=M`, the
reward-weighted atom is at most `M(1-e)` in absolute value.  Therefore a
retained atom of size `a>0` forces `M>0` and

```text
e <= 1-a/M.
```

The decoder substitution `a=q/(4K)` is correct.  This only bounds the
intrinsic endpoint posterior away from one; it neither makes it vanish nor
aligns the coordinatewise scales in `(*)`.

## Sources checked

- `nestedRadialEverQuitMass_ge_weight_mul_gain_div` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawExposure.lean`;
- `exists_finiteCutoff_two_marginalHazardSums` in
  `UniformEquilibrium/Diagnostics/Quitting/Frozen/ActualProfilePacket.lean`;
- the already reviewed whole-face transport calculation in Proposition 6S of
  the reviewed note and its Euler feedback;
- Propositions 6AQ--6AT in the current Ramsey note, including the repaired
  three-law provenance and both latent-component mesh factors.

No Lean implementation claim is made.

## Addendum: Proposition 6AU

**Verdict: valid tangent-family and qualitative finite-reach repair, with one
mandatory provenance wording qualification.**  The endpoint that acquires
positive reach is the newly Never-regularized replacement `R'`, not the old
literal replacement word `R`.  Mixing complete laws changes the endpoint's
hazards throughout its word.  Thus 6AU supplies literal positive-reach
provenance for the reconstructed family, while its relationship to any atom
selected before regularization is only perturbative unless the atom theorem
is rerun on the reconstructed family.

Let `epsilon=h^4` and `s^2=h^2+4Mn epsilon`.  At the old full replacement of
mover `m`, the new endpoint changes all `n` complete laws: `n-1` source laws
are smoothed and `R_m` is replaced by `R'_m`.  Sequential coupling changes a
prescribed payoff coordinate and an unrestricted cap coordinate by at most
`2Mn epsilon` each, so the mover debt changes by at most `4Mn epsilon`.
Consequently

```text
d_m(update sigma' m R'_m) <= h^2+4Mn epsilon=s^2.
```

Source convergence and positivity of every active base debt give the exact
half-source-debt field after one finite truncation, exactly as in 6AH.

The common-Never identity

```text
(1-h)[(1-epsilon)sigma+epsilon Never]
 +h[(1-epsilon)R+epsilon Never]
= (1-epsilon)[(1-h)sigma+hR]+epsilon Never
```

is exact at the complete-law level.  Hence the new and old reset profiles at
parameter `h` differ in terminal semantics by `O(Mn epsilon)`.  Changing the
parameter from `h` to `s` costs `O(M|s-h|)`.  Since

```text
epsilon/s -> 0,       |s-h|/s -> 0,       s/h -> 1,
```

all normalized debt directions, source convergence, and normalized source
excess have their old limits.  The base, active support, inactive signs, and
flat circulation are therefore unchanged after reindexing.  I found no
missing tangent-family field.

Every new source law and every `R'_m` has Never mass at least `epsilon`, and
their strict inner mixtures do as well.  Thus every finite source, inner, and
regularized-endpoint prefix has positive survival.  This removes the exact
zero-denominator issue for an AQ/AR graft built from the **new** family.

What is not literal is old endpoint preservation.  If one retains an atom
chosen before regularization, source and endpoint terminal laws each move by
at most the corresponding finite-face `O(n epsilon)` coupling, so the atom
can only be transported with an error estimate.  Alternatively, because 6AU
constructs another full tangent family, one may rerun the atom/packet
selection on it; the resulting selected endpoint is then exactly `R'` and
has positive prefix reach.  Either route is legitimate, but the note should
not call the old frozen endpoint prefix itself unchanged or positively
reached.

As stated, no likelihood-ratio bound, sublinear posterior actuator cost,
common-scale alignment, retained rectangle cap, or Tier-I restart follows.
