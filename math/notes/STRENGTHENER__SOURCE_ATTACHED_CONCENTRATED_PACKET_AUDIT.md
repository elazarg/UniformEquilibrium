# Source-attached audit of exact concentrated packetization

Author: `STRENGTHENER`

## Status

The exact best-endpoint packet producer is universal and therefore cannot by
itself consume a Fin4 atlas leaf. I checked the two exact routing modes against
the additional data retained by each atlas origin. The reached low-tail
origins recover an already-known fixed-gain horizontal toggle. The
minimum-law owner-clock origin retains no target-side minimum or low-tail
estimate, and neither routing mode repairs that loss. No new uniform-payoff or
well-founded descent theorem is obtained.

## Question

Start from `FinFourAtlasWeakConcentratedSingletonCore source`, unpack its
singleton as `{j}`, and apply the exact one-date best-endpoint update to a
player `o != j`. The target has the same literal post-date tail, exact zero
marked defect for `o`, and terminal `{j}` or `{j,o}` with no mass loss. Which
of these facts remains nonvacuous after retaining the positive-minimum source?

## 1. Packet existence is not source information

For any finite game with at least two players, a pure nonempty coalition at
date zero and one best-endpoint update produce the same constant
`QuittingReprojectionConcentratedPacket`. Thus the following data are all
universal:

- a fixed positive marked atom;
- a literal post-date tail;
- exact zero defect for the selected marked coordinate;
- constant profiles and a vanishing normalization scale.

Any downstream implication using only those fields would be a theorem for
every finite quitting game, not an atlas contraction.

## 2. Reached low-tail origins: the Quit mode is forced for a hard collider

For `.reached endpoint`, the marked root is a literal pure singleton `{j}`.
The hard residual supplies a fixed collider `o != j` with

\[
 r_o(\{j,o\})-r_o(\{j\})\ge\gamma>0.
\]

Against a pure singleton root, the tail is never reached under either action
of `o`; hence its exact endpoint difference is precisely this table edge.
The best endpoint is therefore Quit. The local construction gives the pure
pair `{j,o}`, preserves the past and tail, and has exact payoff gain

\[
 U_o(\rho_{\{j,o\}})-U_o(\rho_{\{j\}})
 =L\,[r_o(\{j,o\})-r_o(\{j\})]
 \ge \lambda\gamma,
\]

where `L` is the marked live mass and `L >= lambda` because the source pure
singleton has root mass one.

This is nonvacuous source-attached content, but it is not new: it is exactly
the first edge of the checked/maintained same-stage full-gap toggle handoff.
Iterating full-gap pure toggles produces the known horizontal cycle or
singleton route, not a Bellman chronology. The stronger constant packet adds
no vertical information.

## 3. Owner-clock origin: both exact modes remain possible

For `.ownerClock producer endpoint`, the owner `j` is pure Quit at the marked
date, but the three opponents retain their mixed source actions. Positive
singleton mass only says that they jointly Continue with positive
probability. A positive table edge on `{j}` can be canceled in the endpoint
average by:

- the prescribed continuation payoff when all opponents Continue; or
- other opponent coalitions at the same mixed row.

Consequently the selected action of a hard collider can be Continue or Quit.

- In the Continue mode, the singleton is retained and the exact endpoint
  difference is nonpositive. This is the exact, constant-profile version of
  the existing owner-cancellation arm; literal tail equality does not remove
  the cancellation terms.
- In the Quit mode, the atom routes to `{j,o}` and the local defect becomes
  zero, but the payoff gain need not have a source-independent lower bound.
  It can approach zero while the singleton table edge remains fixed, because
  the same cancellation terms may approach equality from the other side.

The retained cap-root stack is exact only over `endpoint.suffixProfile`, and
`endpoint.referenceProfile` is its literal prefix. Replacing `j` at the
marked suffix date changes the continuation caps seen by the copied roots.
The checked interface explicitly does not assert that the stack is cap--Nash
for `endpoint.targetProfile`; the later update of `o` cannot restore this.

Nor does the owner-clock endpoint have a target-side low-tail or near-minimum
field. Its reference profiles approach the minimum through the retained
chronology, but a fixed-mass owner completion can move the terminal semantic
pair by order one. Global minimality supplies only a lower bound on the
target's debt.

## 4. Exact source-side square, and why it still stops

For a cofinal owner-clock endpoint define four literal profiles at the marked
date:

\[
 A=\text{reference},\quad
 B=A[j\leftarrow Q],\quad
 C=A[o\leftarrow a],\quad
 D=B[o\leftarrow a],
\]

where `a` is the best endpoint for `o` at `B`. This is an actual same-source,
same-past, same-tail response square. Because own-strategy replacement leaves
the owner's unrestricted cap fixed, the horizontal gains give exact own-debt
subtractions.

What is missing is a first-order total-debt sign. The update of `j` changes
`o`'s endpoint environment, while either update may change the other two
players' caps by order one. The source fields supply no estimate of

\[
 D(D)-D(C)-D(B)+D(A)
\]

with the sign needed for a minimum contradiction, and no no-new-support
property. This is the same source-to-horizontal-square boundary already
isolated in the rectangle work.

## 5. Checked boundaries inspected

- `FinFourAtlasWeakConcentratedSingletonCore` exposes only the origin,
  reference/target profiles, marked singleton mass, and post-date tail
  equality.
- `FinFourOwnerCompressedSingletonEndpoint.rootStack_nash` is stated for the
  unmodified `suffixProfile`, while the module documentation and fields
  explicitly deny target-side cap--Nash preservation.
- `QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch_compress`
  reduces a singleton packet only to exact deletion or
  `HasQuittingStaticAtomicToggleHandoff`.
- `FourPlayerCyclicPlateauCandidate` shows that mass-one rows, exact local
  optimality, literal horizontal cycles, and a unique all-Continue cap root
  can coexist when the global minimum is zero. It is a boundary regression,
  not a positive-gap counterexample.

## Conclusion

The smallest nonvacuous consequence presently forced by the source attachment
is the reached-origin fixed-gain singleton-to-pair edge. It is already part of
the horizontal toggle machinery. For the genuinely new owner-clock origin,
the exact packetization does not produce a target-side minimum, low tail,
cap--Nash stack, or fixed gain.

A downstream theorem must use an additional quantitative bridge not present
in the weak core: for example a bound on cross-coordinate cap leakage, a
law-preserving minimum comparison for the four-corner square, or a returned
exact chronology. Without one of those, the two exact routing modes do not
yield terminal approximation, uniform payoff, or rank descent.
