# Approximate forward packets bypass exact connector Nashification

Author: `CODEX_ROOT`

## Status

Source synthesis of checked compiler interfaces and reviewed ordinary-mathematics
producer boundaries.  This note does not prove the Fin4 conjecture and contains
no new Lean theorem.  Its point is to state the weakest currently checked
chronological target: the missing connector need not be exactly Nash at every
row.

## Checked sufficient object

Fix a quitting reward table and one compact set `K` of payoff vectors.  Suppose
that for every `delta>0` and every finite charge target `Q>=0` there is a finite
forward packet

\[
 (v_0,q_0),(v_1,q_1),\ldots,(v_H,q_H)
\]

with the following properties:

1. every `v_t` lies in `K`;
2. Bellman evaluation is exact,
   \[
   v_{t+1}=F(q_t,v_t)\qquad(t<H);
   \]
3. `q_t` is support-approximately Nash against `v_t`, with common error at
   most `delta`;
4. every coordinate of every `v_t` is at least its punishment value minus
   `delta`; and
5. the raw absorption charge satisfies
   \[
   Q\le \sum_{t<H}\operatorname{Abs}(q_t).
   \]

Then the quitting game has a uniform-equilibrium payoff against unrestricted
behavioral deviations.

This is exactly the public checked interface
`QuittingFiniteForwardPacket` and the theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets` in
`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`.
Compact charged recurrence selects a close pair of packet values.  Reversing
the intervening forward block gives a chronological lasso.  Exact Bellman
evaluation pays every nonclosing policy equation, while the common support
error and the one endpoint seam form the lasso error budget.

Thus the current research target is strictly weaker than a finite path of
exact punishment-floor Nash--Bellman edges.

## Why this matters for the current Fin4 seam

The recent local no-go results rule out exactifying the retained paid row while
preserving its literal root and tail.  They also rule out infinitesimally
descreening that row: its paid mover retains a fixed root defect against every
bounded continuation.  Those results do not rule out a different forward
orbit whose rows have defects tending uniformly to zero.

The analytic tangent machinery supplies the right local scale in a qualified
chamber.  A charge-tangent row of size `t` can have

\[
 \operatorname{Abs}(q_t)=\Theta(t),\qquad
 \text{support error}=O(t^2),\qquad
 \text{Bellman target error}=O(t^2).
\]

After defining the next payoff by the literal Bellman successor, the Bellman
equation is exact and the `O(t^2)` discrepancy becomes source drift.  Repeating
`O(1/t)` such rows would accumulate order-one charge while the common
support-Nash tolerance still tends to zero.  Repeating long enough would meet
any prescribed finite charge target.

The unresolved point is renewal at the moving payoff.  The existing packet is
extracted at one boundary and does not prove that the same subcompatible
tangent row can be reconstructed at each exact Bellman successor.  Freezing
the boundary is invalid: the checked moving-source calculation shows an
order-`t` radial displacement on active coordinates.  Consequently the exact
remaining producer is an indefinitely iterable moving-source approximate
circulation, not local exact Nashification.

## Existing complete special case

`FaceCirculationCertificate` in
`UniformEquilibrium/Quitting/Circulation/SingletonFaceCirculation.lean`
is a finite certificate which supplies precisely such an orbit.  The checked
modules

- `MultiOwnerFaceCirculationPath.lean`,
- `MultiOwnerFaceCirculationFiniteClosing.lean`, and
- `MultiOwnerFaceCirculationCompactPath.lean`

turn it into uniformly accurate forward packets of arbitrarily large charge
and hence a uniform-equilibrium payoff.

The Fin4 hard source does not currently produce a face-circulation
certificate.  In particular, the checked preference-lasso obstruction in
`SingletonPacketPreferenceLassoCirculation.lean` proves that no phase may
simply reuse the full normalized singleton-packet mass vector: the required
target-pinning equality fails strictly at the lasso entrance.  A successful
producer therefore needs genuinely phase-varying weights or a broader
moving-source packet than the present face-circulation structure.

## Relation to bounded exact capacity

Under no Fin4 uniform payoff, checked results bound the total hazard of every
finite **exact-Nash** Bellman block.  That statement does not by itself bound
approximate forward packets at a tolerance tending to zero.  Conversely, the
checked forward-packet compiler proves that a counterexample must prevent
arbitrarily charged approximate packets for at least one positive accuracy
at every proposed compact carrier.

This is a useful falsifiable boundary.  The contrapositive keeps the carrier
outside the accuracy choice:

\[
 \text{no UE}
 \Longrightarrow
 \forall\text{ fixed compact admissible carriers }K\ \exists\delta_K>0,
 \quad
 \sup\{\text{charge of a }\delta_K\text{-support packet in }K\}<\infty,
\]

with the quantifiers interpreted through the exact public packet structure.
In particular one may fix the canonical bounded reward/floor carrier first and
obtain one positive obstruction accuracy there.  A common `delta` for every
possible compact carrier does not follow.  This approximate obstruction is
stronger than bounded exact capacity and is the natural approximate-capacity
certificate that a putative counterexample must carry.

## Preferred concrete question

Starting from the positive-minimum Fin4 hard source, prove one of:

1. for every `delta>0` and `Q>=0`, a `QuittingFiniteForwardPacket` in one
   fixed compact payoff carrier with support error `delta` and charge at least
   `Q`;
2. a moving-source face-circulation certificate, possibly with phase-varying
   active sets, which the existing finite-closing theorem accepts;
3. terminal approximate Nash profiles or another checked terminal consumer;
4. a quantitative approximate-capacity barrier realized by an explicit
   positive-gap four-player table.

The producer must retain exact Bellman successor matching.  A sequence of
separately selected approximate rows, a static toggle cycle, or an
`O(t^2)` row at one frozen boundary is insufficient.

## Sources inspected

- `UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`;
- `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`;
- `UniformEquilibrium/Quitting/Circulation/SingletonFaceCirculation.lean`;
- `UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationPath.lean`;
- `UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationFiniteClosing.lean`;
- `UniformEquilibrium/Quitting/Classification/SingletonPacketPreferenceLassoCirculation.lean`;
- `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`, especially the
  quadratic-error tangent row and moving-source readout; and
- `notes/CODEX_ADVERSARY__QUANTITATIVE_DESCREENING_COMPLEMENTARITY_BARRIER.md`.

## Nonclaims

- No moving-source approximate circulation is constructed here.
- The canonical paid mixed row has fixed, not vanishing, support error and is
  not an instance of this route.
- A local tangent row does not imply renewable packet extraction.
- The checked exact-capacity bound is not asserted to extend automatically to
  approximate roots.
