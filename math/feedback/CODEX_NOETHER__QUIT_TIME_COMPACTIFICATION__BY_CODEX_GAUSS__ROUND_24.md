# Active-Packet Normality and Homogeneous-Vertex Dispatch Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.8, Proposition 63.  I independently checked the packet-floor
adapter, the homogeneous-support split, the no-harm singleton-owner decoder,
and the finite-support passage from row hazards to a cumulative-hazard limit.
This is ordinary mathematics, not Lean-checked.

## Verdict

**Proposition 63 is VALID ordinary mathematics as stated.**  It closes the
pure first-layer-abnormal vertex escape for returned rows whose positive Quit
hazards come from positive masses of charge-tangent data.  It does not create
or reproject the next packet and does not apply to arbitrary ambient product
rows.

## 1. Positive packet mass forces production normality

For `packet : QuittingChargeTangentData reward`, the checked data fields give

```text
0 < packet.mass i
  -> packet.boundary i = reward({i})_i,
quittingPunishmentValue reward i <= packet.boundary i.
```

Their combination is exactly

```text
quittingPunishmentValue reward i <= quittingSoloSelfPayoff reward i,
```

namely `IsQuittingNormalPlayer reward i` as defined in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`.  No limit,
strictness, or equality in the punishment bound is being assumed.

## 2. The homogeneous support split is exhaustive

Let `M=normalizedSoloMatrix reward` and let `mu` be a full homogeneous
simplex witness.  If `mu` has at least two positive coordinates, Proposition
62 places its support in every recursive normal layer and restricts it to a
homogeneous witness for `normalPlayerMatrix M`.  This contradicts `(N61)`.

The simplex normalization therefore leaves exactly one positive coordinate,
so `mu=e_j`.  Its homogeneous residual is the `j`-th column:

```text
(M mu)_i=M_i,j>=0.
```

By the definition of the normalized singleton matrix this is precisely

```text
reward({i})_i <= reward({j})_i
```

for every receiver `i`.  If the positive support coordinate `j` is
production-normal, its punishment value is also at most `reward({j})_j`.
These are exactly the two fields of
`QuittingNormalNoHarmSingletonOwner reward` with owner `j`.

The checked theorem
`exists_uniformEquilibriumPayoff_of_normalNoHarmSingletonOwner`
(`UniformEquilibrium/Quitting/Classification/LCP/ProjectiveQBarBehavioralDecoder.lean`)
then supplies a uniform-equilibrium payoff against unrestricted behavioral
deviations.  Thus the vertex contradicts the no-uniform-payoff hypothesis; no
sign assumption on the owner's solo reward is needed here because the checked
decoder uses the actual punishment value.

## 3. Passage from packet rows to the limiting owner distribution

In a Proposition 61 row,

```text
h_i=t*scale*packet.mass i
```

with `t,scale>0`, so `h_i>0` implies `packet.mass i>0` and hence production
normality of `i`.  The set of production-normal players depends only on the
fixed finite reward table.  Therefore every cumulative owner measure made
from such rows is identically zero outside that fixed set.  Normalizing a
nonzero cumulative measure and taking a subsequential limit preserve those
zero coordinates.  Every positive coordinate of the homogeneous limit is
therefore production-normal, exactly the support hypothesis used above.

This remains valid when different rows use different packets.  It would not
be valid merely from approximate floor inequalities with an error that does
not vanish before support is taken; Proposition 63 does not make that weaker
claim.

## 4. Exact scope

The result is a semantic dispatch for one limiting support pattern, not a
chronological producer.  Proposition 61 still changes the tail from `b` to
`b-scale*t*z`; Proposition 63 supplies no charge-tangent packet at that new
tail, no punishment-floor-preserving connector, and no returned loop.  It
also does not extend the returned-block modulus to arbitrary ambient product
rows, because a positive hazard in such a row need not be supported by a
production-normal packet owner.

Within the packet-supported regime, however, the two homogeneous cases are
now exhaustive and both are dispatched: a nonvertex contradicts recursive-
core no-homogeneous, while a vertex is a checked production-normal no-harm
singleton owner.  The remaining conjecture-facing obligation is precisely
moving-source packet reprojection or an alternative charged chronology.
