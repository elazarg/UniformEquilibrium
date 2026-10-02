# Review of `CODEX_CEDAR__DISCOUNTED_RADIAL_DEBIASING`, Propositions 5--6

Reviewer: `CODEX_GAUSS`

Status: independent falsification audit.  **Propositions 5 and 6 are valid
ordinary mathematics in their stated scope.**  I found no counterexample or
missing analytic-order branch.  The conclusions are not asserted to be proved
in Lean here.

## Scope reviewed

I checked the uniqueness of the normalized matching packet for the literal
four-player `SolanVieilleBoundary.boundaryReward`, and the claim that every
analytic Bellman germ of this table lies in the matching order regime and
therefore has the same limiting stationary refusal defect `1/12`.

The named declarations inspected were:

- `periodTwo_singletonMatrix` and `normalizedSoloMatrix_periodTwo` in the
  four-player paired-singleton example files;
- `pairedSingletonMatrix_noHomogeneous` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`;
- `quittingGerm_endpoint_fixedPoint` and
  `quittingGerm_endpoint_endpointNash` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`;
- `quittingGermLeadingOrderNormalization_of_not_isQuittingZeroSolo` in
  `UniformEquilibrium/Quitting/Boundary/Analytic/GermNondegeneracy.lean`;
- `QuittingGermFastLeadingData.toProjectiveSingletonPacket`,
  `quittingGermValue_zero_eq_zero_of_discount_dominates`, and
  `quittingGerm_endpointValue_eq_solo_of_positive_leadingShare` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AnalyticPacket.lean`;
- `QuittingGermMatchingLeadingData.value_eq_singleton_mix`,
  `positive_singleton_pins`, and `toProjectiveSingletonPacket` in
  `UniformEquilibrium/Quitting/Projective/AnalyticPacket.lean`; and
- `periodTwo_no_stationary_exactTerminalNash` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwoStationary.lean`.

The declarations in the `ThreePlayer` directory used here are polymorphic in
the finite player type, so their application to the four-player table is not
a hidden three-player assumption.

## Proposition 5: unique matching packet

The literal normalized singleton matrix is

```text
M = [ 0  3 -1 -1
      3  0 -1 -1
     -1 -1  0  3
     -1 -1  3  0 ].
```

Every own singleton payoff is one, so the cemetery direction is `-1` in
every coordinate.  For a normalized packet `(c,z,w)`, the four residuals are
exactly

```text
w0=-c+3z1-z2-z3,   w1=-c+3z0-z2-z3,
w2=-c-z0-z1+3z3,   w3=-c-z0-z1+3z2,
```

with `c,z,w>=0`, `z_i w_i=0`, and `c+sum z=1`.

The proof that `c>0` is sound.  If `c=0`, then `sum z=1`, `Mz=w>=0`, and
complementarity is exactly a homogeneous simplex-LCP solution, contradicting
`pairedSingletonMatrix_noHomogeneous`.

With `c>0`, `w0>=0` forces `z1>0`, `w1>=0` forces `z0>0`, and the other two
rows force `z3,z2>0`.  Thus complementarity makes all four `w_i` zero.
Subtracting paired equations gives

```text
z0=z1=x,   z2=z3=y,
c=3x-2y=3y-2x.
```

Hence `x=y=c`, and normalization gives `5c=1`.  This proves
`c=z0=z1=z2=z3=1/5` without an omitted support case.

The matching-packet normalization

```text
c=1/(1+sum a),   z_i=a_i/(1+sum a)
```

then gives `a_i=1` for all four owners.  The checked singleton-mixture formula
uses the normalized weights `z_i=1/5` (not the conditional weights `1/4`), so
the endpoint value is indeed `(1,1,1,1)`.  Proposition 3's formula therefore
gives

```text
(a_i/(A-a_i))*(v_i/A) = (1/3)*(1/4)=1/12.
```

The uniqueness conclusion is correctly limited to normalized first-order
packet data; it says nothing about higher analytic jets.

## Proposition 6: all analytic germs are matching

### Absorbing analytic endpoint

Suppose the endpoint root has joint Continue mass below one.  The two checked
endpoint declarations make its endpoint value an exact stationary fixed point
and its root exact endpoint Nash.

- If at least two coordinates have positive Quit probability, every player
  has an opponent with a positive Quit clock.  Thus every opponent-only clock
  contracts.  With the endpoint value already a fixed point, the exact
  stationary pure-Quit/`Never` cap gives zero behavioral regret.
- If exactly one owner `i` has positive Quit probability, every outsider's
  opponent clock still contracts.  For `i`, all opponents Never quit.  The
  fixed-point equation with positive own hazard forces its value to the own
  singleton payoff `1`.  Its arbitrary stopping-clock payoff is at most one:
  quitting eventually pays one and pure Never pays zero.  This includes both
  `0<p_i<1` and the saturated `p_i=1` boundary.

Thus the endpoint root would be an exact terminal stationary Nash profile
against unrestricted behavioral deviations, contradicting
`periodTwo_no_stationary_exactTerminalNash`.  The endpoint must therefore be
all Continue.  No `q_i=1` case is silently fed into a formula requiring
opponent contraction.

### Analytic order trichotomy

Because all own singleton payoffs are one, the table is not zero-solo.  The
checked normalization supplies a nonzero leading order `m`, nonnegative
leading vector with positive total mass, and the exact comparison with the
positive discount ramification `q`.

- If `m<q`, real absorption is faster than discount.  The checked fast-data
  decoder gives a cemetery-zero projective singleton packet.  Its singleton
  vector is a homogeneous simplex-LCP solution for the literal normalized
  matrix, contradicting `pairedSingletonMatrix_noHomogeneous`.
- If `q<m`, discount is faster than real absorption.  The checked dominant-
  cemetery theorem gives endpoint value zero.  Some normalized leading share
  is positive, while the checked pinning theorem makes that owner's endpoint
  coordinate its singleton payoff one, a contradiction.

The trichotomy leaves only `m=q`.  Proposition 5 then fixes every leading
coefficient at one, and the refusal calculation gives `1/12` for every germ.

## Exact scope and consequence

The audit confirms the intended route-killing statement: asymmetric or
branch-varying *local analytic germs* cannot cancel the radial stationary
defect on this table.  It does not exclude a nonanalytic selection, a finite
macroscopic continuation jump, or the known exact period-two construction.
Indeed the checked period-two equilibrium is the concrete evidence that the
remaining repair is nonstationary and nonlocal rather than nonexistent.

No export or full-conjecture claim follows from these two propositions.  Their
useful portfolio conclusion is that future positive-tail work should seek an
executable return/punishment attachment, not another perturbative stationary
analytic branch.
