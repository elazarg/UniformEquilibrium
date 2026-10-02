# AGKRS summable endpoint return and ballistic dispatch

Authors: `CODEX_MINER`

Independent review:
[`CODEX_EULER`](../feedback/CODEX_MINER__AGKRS_SUMMABLE_ENDPOINT_PORT_BALLISTIC_DISPATCH__BY_CODEX_EULER.md)

Post-review formalization correction: throughout `(C2)`, `M` is the canonical
`quittingRewardBound(r)`, not the raw maximum absolute terminal coordinate.
Generic punishment-floor orbit annotations are certified to lie in the
canonical reward box, which can be larger than that raw maximum.  This repair
changes no branch or argument; it fixes the bound used by the signed-mass
constant.

## Exact statement

Let `I` be a finite nonempty player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game terminal reward table.  Let `O` be an exact infinite
punishment-floor Nash--Bellman orbit.  Thus `O` consists of product mixed
rows `q_t` and payoff annotations `v_t`, indexed by `t in N`, such that:

1. every `v_t` lies in the canonical reward box and `v_0` dominates every
   behavioral punishment value;
2. `q_t` is an exact one-row Nash root against continuation annotation `v_t`;
3. the forward policy identity is

   \[
   v_{t+1}=F_r(q_t,v_t);
   \]

4. every later `v_t` remains above the behavioral punishment floor.

Write

\[
 a_t=1-\prod_{i\in I}q_t^i(C),\qquad
 C(s,N)=\sum_{t=s}^{s+N-1}a_t,
\]

and

\[
 D(s,N)=\max_{i\in I}|v_{s+N}^i-v_s^i|.
\]

Here `a_t` is the probability that at least one player quits in row `q_t`.

### Theorem A: finite-segment ballisticity under failure of S.3

If the game does not have the well-supported absorbing form of AGKRS branch
S.3, then there is `e>0` such that for every `s,N in N`,

\[
 C(s,N)>0
 \quad\Longrightarrow\quad
 D(s,N)>e\frac{C(s,N)}{1+C(s,N)}.                 \tag{A}
\]

The same `e` works for every segment of the supplied orbit.

### Theorem B: a returned positive-charge summable port gives S.3

Suppose in addition that `O` has a summable all-Continue port: the series

\[
 A=\sum_{t=0}^{\infty}a_t
\]

is finite, `v_t` converges coordinatewise to a vector `L`, every marginal
Quit probability tends to zero, and `L` is a floor-safe exact all-Continue
Nash--Bellman self-loop.  Put `E=v_0`.

If

\[
 A>0\qquad\text{and}\qquad L=E,                 \tag{B}
\]

then the game has literal well-supported branch S.3: for every `delta>0`
there is a completely absorbing root sequence whose used actions are
support-locally `delta`-optimal against its actual continuation payoffs.

### Theorem C: exact summable-port boundary under failure of S.3

Under failure of S.3, the same `e` as in Theorem A gives

\[
 \max_{i\in I}|L_i-E_i|
 \ge e\frac{A}{1+A}.                              \tag{C1}
\]

Consequently exactly one of the following two cases holds.

1. `A=0`.  Then every `a_t=0`, every `q_t` is literally all Continue, and
   every `v_t=E=L`.
2. `A>0`.  Put

   \[
   \rho=e\frac A{1+A}>0,
   \qquad M=\operatorname{quittingRewardBound}(r).
   \]

   Then `M>0`, some coordinate moves by at least `rho`, and the checked
   finite-label decomposition supplies one fixed player `i`, sign
   `sigma in {1,-1}`, and nonempty coalition `T` such that

   \[
   \frac{\rho}{2M(2^{|I|}-1)}
   \le \sum_{t=0}^{\infty}\Pr_{q_t}(\text{the quitting set is }T). \tag{C2}
   \]

   The corresponding signed terminal contribution has lower bound
   `rho/(2^{|I|}-1)`.

### Source-matched AGKRS specialization

For an actual
`QuittingPositiveJointPrefixReachNoSureExitResidual r`, the checked endpoint
adapter gives S.3 immediately unless it returns an actual reached punishment
endpoint `z`, the proof that `z` has no exact sure-exit Nash prefix, and a
summable port on `z.exactPrefixOrbit`.  Applying Theorems B and C to that
literal orbit gives the following strict narrowing:

- a positive-total-charge port which returns to the endpoint is closed by
  S.3;
- under failure of S.3, only a literal zero-charge constant all-Continue
  phantom or a quantitatively displaced signed port can remain.

The endpoint and its no-sure-exit provenance are retained in both surviving
arms.

## Conjecture-facing change

The named open obligation is the second source class in
[`AGKRS_THEOREM_3_4_SOURCE_CLOSURE.md`](../questions/AGKRS_THEOREM_3_4_SOURCE_CLOSURE.md):
an actual reached no-sure-exit endpoint whose canonical exact-prefix orbit has
a summable all-Continue port.

Before this result, every summable port remained a single unresolved arm.
Theorem B closes its positive-charge returned subarm through literal S.3.
Theorem C then replaces failure of that closure by the exhaustive and
quantitative boundary

```text
zero charge and literal constant all Continue
  or
positive charge and endpoint displacement with a fixed signed terminal label.
```

This does not close the full positive-joint source class.  It is a strict
reduction of its maintained summable-port obligation.

## Definitions and assumptions

At each live date all players observe that the game has not yet stopped and
independently sample Quit/Continue from the displayed product row.  The first
nonempty quitting set stops the game and receives `r(S)`.  The orbit is a
deterministic sequence of such product rows; the result adds no public
randomization and no hidden controller.

The exact-Nash premise on each orbit row is a one-stage Bellman condition
against the displayed continuation annotation.  The conclusion S.3 is not
obtained by treating those annotations as executable terminal payoffs.
Instead, finite exact orbit segments are reversed into single-seam
projective lassos.  Their divergent paths use their own actual tail
continuation values.

The support-local S.3 certificate compares both pure actions at every live
row and requires every used action to be nearly optimal.  The checked
`quittingRowεPerfect_of_supportApproxNash` adapter converts this to the
paper's sequential epsilon-perfect row predicate.  The branch is completely
absorbing, so Never has probability zero in its actual payoff law.  The
comparison is made against the row's actual continuation payoff and is not a
restriction to stationary deviations or pure stopping times.  However S.3 is
the paper's rowwise sequential-perfect predicate, not by definition a new
terminal-Nash theorem against every behavioral deviation.  This packet claims
exactly S.3 and relies only on the checked paper adapter from the
well-supported formulation.

The upstream positive-joint endpoint is extracted from profiles satisfying
the repository's unrestricted behavioral Nash inequalities, and its semantic
debt/envelope coordinates use suprema over all unilateral behavioral
strategies.  The new ballistic proof does not weaken or re-prove that audit;
after reaching the endpoint it uses only the exact Bellman orbit fields.  No
bounded-controller or stationary-deviation replacement is made.

The port limit `L` is only a formal Bellman self-loop.  The proof never
identifies it with the terminal payoff of the literal all-Never profile.

## Source correspondence

The exact maintained source declarations are:

- `QuittingPunishmentFloorInfiniteOrbit`, `toFinitePrefix`, and
  `toFiniteSegment` in
  `UniformEquilibrium/Quitting/Bellman/Finite/`;
- `SummableChargeAllContinuePort` in
  `PunishmentFloorInfiniteOrbitChargeDichotomy.lean`;
- `exists_singleSeamProjectiveLasso_of_floorPrefix_`
  `cumulativePayoffNearReturn` in
  `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`;
- `QuittingFiniteSingleSeamProjectiveLasso.`
  `exists_supportRationalDivergentPath`;
- `quittingWellSupportedAbsorbingSequenceExistence_`
  `of_singleSeamProjectiveLassos` and
  `QuittingPositiveJointPrefixReachNoSureExitResidual.`
  `wellSupported_or_summableExactPrefixPort` in
  `PositiveJointEndpointSequentialReduction.lean`;
- `nonempty_summableChargeSignedTerminalPort_of_displacement` in
  `PunishmentFloorSummablePortLabel.lean`; and
- `theorem3_4_of_prioritizedAndSummablePortClosures` in
  `Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`.

The current checked
`PositiveJointSummablePortPhantomReduction.lean` proves, in a different
direction, that every summable positive-joint port yields S.1 or the existing
positive-singleton/all-Continue phantom after the nonsummable S.3 arm is
removed.  It does not prove the positive-charge returned-port S.3 consumer,
inequality `(A)`, modulus `(C1)`, or the source-native signed mass scale
`(C2)`.  In the hard no-S.1/no-S.3 branch its phantom reduction and Theorem C
hold simultaneously.  The signed label is not claimed to consume the
positive-singleton phantom.

The original AGKRS Theorem 3.4 asks for the S.1/S.2/S.3 classification.  The
paper does not contain this summable-port ballistic estimate; the port and
the lasso compiler are repository corrections/refinements of the incomplete
paper-facing route.

## Proof

Assume first that S.3 fails.  Negating
`QuittingWellSupportedAbsorbingSequenceExistence r` gives a number
`delta>0` for which there is no completely absorbing root sequence which is
support-locally `delta`-Nash at every tail.  Set

\[
 e=\delta/2>0.                                      \tag{1}
\]

Fix `s,N` and abbreviate `C=C(s,N)`, `D=D(s,N)`.  Suppose `C>0` and, contrary
to `(A)`,

\[
 D\le e\frac C{1+C}.                               \tag{2}
\]

The literal segment `O.toFiniteSegment s N` is an exact punishment-floor
finite prefix.  Its charge is exactly `C`, and every endpoint coordinate seam
is at most `D`.  Apply the cumulative-charge lasso compiler with

```text
chargeFloor = C,
seamError   = D,
error       = e.
```

Condition `(2)` is exactly its seam-scale premise.  The returned lasso has a
support-rational divergent path with support error `2e=delta`.  Its absorption
series is nonsummable, so the standard survival-product theorem makes the path
completely absorbing.  This contradicts the choice of `delta`, proving
Theorem A.

Now assume the summable-port hypotheses, `A>0`, and `L=E`.  Given arbitrary
`epsilon>0`, put `c=A/2>0`.  Long enough initial segments have charge at least
`c`, while finite-coordinate convergence `v_N -> L=E` makes their endpoint
seams at most

\[
 \epsilon\frac c{1+c}.
\]

The same compiler gives a lasso at the arbitrary accuracy `epsilon`.
`quittingWellSupportedAbsorbingSequenceExistence_`
`of_singleSeamProjectiveLassos` therefore gives S.3.  This proves Theorem B
with all positive tolerances, not only one selected scale.

Return to failure of S.3.  If `A>0`, the initial partial sums are eventually
positive.  Applying `(A)` to initial segments and passing to the limit gives

\[
 \max_i|L_i-E_i|\ge e\frac A{1+A},
\]

where finiteness of `I` permits the maximum to pass through coordinatewise
convergence.  This is `(C1)`.

If `A=0`, nonnegativity of every `a_t` forces every term to vanish.  A finite
product root has zero absorption exactly when every player Continues surely.
The Bellman policy then gives `v_{t+1}=v_t`, proving literal rigidity.

If `A>0`, define `rho` as in Theorem C.  Finiteness selects a coordinate with
displacement at least `rho`.  Both endpoint vectors lie in the canonical
`quittingRewardBound` box; this is the bound required by the checked
signed-terminal-port theorem and must not be replaced by the possibly smaller
maximum absolute terminal reward coordinate.  The checked signed-terminal-port
theorem then gives one fixed player, sign, and nonempty terminal coalition,
with exactly the contribution and mass bounds stated in `(C2)`.  This proves
Theorem C and the source-matched specialization.

## Boundary tests

1. **Returned positive charge is nonvacuous.**  In the one-player zero-reward
   game, take `v_t=0`, let the first root Quit with any probability
   `h in (0,1]`, and let every later root be all Continue.  Every row is exact
   Nash, `A=h>0`, and `L=E=0`.  Repeating the first root gives exact S.3, as
   Theorem B predicts.
2. **The positive-charge hypothesis is necessary for the return consumer.**
   In the one-player game with solo reward `1`, the constant annotation
   `v_t=1` and all-Continue roots form an exact floor-safe port with `A=0` and
   `L=E`.  The port chronology itself contains no absorption.  The game has a
   separate stationary/sure-Quit solution, but that does not turn this port
   into the claimed charged-return lasso.
3. **The return hypothesis cannot be dropped from this mechanism.**  In a
   two-player zero-Never game set

   \[
   r(\{p\})=(-1,0),\quad r(\{q\})=(0,-1),\quad
   r(\{p,q\})=(0,0).
   \]

   Put `v_0=(1,1)`, let both players surely Quit at time zero, put `v_t=0`
   thereafter, and use all-Continue roots thereafter.  This is an exact
   punishment-floor orbit: the punishment values are zero, the sure collision
   root is exact against `v_0`, and all Continue is exact against zero.  It has
   `A=1` and `L=(0,0) != E`.  It satisfies the displaced alternative rather
   than the returned-port premise.  The game separately has an exact sure-exit
   solution; the test isolates the logical need for `L=E`, not failure of S.3.
4. **The limiting inequality must be non-strict.**  The finite inequalities
   are strict, but passage to the limit can attain equality.  Theorem C states
   `>=`, not `>`.

## Adapter and consumer

The actual-data adapter is checked:

```text
QuittingPositiveJointPrefixReachNoSureExitResidual
  -> actual reached punishment endpoint with retained no-sure-exit proof
  -> endpoint.exactPrefixOrbit
  -> S.3 or SummableChargeAllContinuePort.
```

The new consumer is complete on the returned positive-charge arm:

```text
A>0 and port.limit = orbit.value 0
  -> finite charged near-return prefixes at every scale
  -> single-seam projective lassos at every scale
  -> completely absorbing well-supported sequences at every scale
  -> AGKRS S.3.
```

The displaced arm then uses the already checked signed-label adapter.  This
last adapter is a quantitative residual, not a branch consumer.

## Lean handoff

The narrow generic declarations should be added beside
`PositiveJointEndpointSequentialReduction.lean`:

1. failure of `QuittingWellSupportedAbsorbingSequenceExistence` implies the
   uniform finite-segment inequality `(A)` for every
   `QuittingPunishmentFloorInfiniteOrbit`;
2. a `SummableChargeAllContinuePort` with positive total absorption and
   `port.limit = orbit.value 0` implies
   `QuittingWellSupportedAbsorbingSequenceExistence`;
3. under branch failure, pass `(A)` to the port limit and return literal zero
   charge or a `SummableChargeSignedTerminalPort` with
   `rho=e*A/(1+A)`; and
4. specialize this theorem to the actual endpoint returned by
   `wellSupported_or_summableExactPrefixPort`.

Use `orbit.toFiniteSegment`, not a newly copied prefix structure.  When
passing to the limit, use the finite maximum or the `pi` metric consistently.
Do not replace total charge `sum a_t` by the absorbed probability
`1-product(1-a_t)`; the lasso compiler uses the checked ratio
`C/(1+C)`.  The current phantom contraction should be imported and reused,
not reproved.

Useful exact regression tests are the three rational tables in the Boundary
tests.  The handoff does not require a new source selector or a change to the
AGKRS capstone signature.

## Scope and nonclaims

- No closure of the zero-charge all-Continue phantom is claimed.
- No closure of the quantitatively displaced signed port is claimed.
- The signed label does not consume the positive-singleton phantom supplied
  by the current checked contraction.
- A strict displacement in a real-valued payoff is not a well-founded rank;
  positive displacements may shrink along later regenerations.
- The formal limit `L` is not identified with the payoff of one executable
  behavioral profile.
- The no-sure-exit field is preserved but is not used by the ballistic
  inequality.
- The result does not close every positive-joint residual, the prioritized
  corrected-pointwise residual, AGKRS Theorem 3.4, or the full finite-quitting
  uniform-equilibrium conjecture.
- It proves the literal rowwise sequential-perfect S.3 branch, not an
  additional unrestricted terminal-Nash statement for the displayed lasso
  paths.

## Checked Lean realization

The corrected packet is realized in
`UniformEquilibrium/Quitting/Classification/Existence/`
`PositiveJointSummablePortBallisticDispatch.lean`.  Its principal checked
declarations are:

- `QuittingPunishmentFloorInfiniteOrbit.`
  `nonempty_ballisticCertificate_of_not_wellSupported`, which supplies the
  uniform strict finite-segment estimate in Theorem A;
- `QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort.`
  `wellSupported_of_totalAbsorption_pos_of_return`, which consumes the
  returned positive-charge arm through literal well-supported S.3;
- `QuittingPunishmentFloorInfiniteOrbit.BallisticCertificate.`
  `limitDisplacement_lower`, which proves the non-strict limiting modulus
  in `(C1)`;
- `QuittingPunishmentFloorInfiniteOrbit.BallisticCertificate.`
  `zeroRigidity_or_positiveSignedBoundary`, which returns the exhaustive
  zero-charge rigidity or positive displaced signed-label boundary using
  the canonical `quittingRewardBound`; and
- `QuittingPositiveJointPrefixReachNoSureExitResidual.`
  `wellSupported_or_endpointBallisticBoundary`, which retains the actual
  endpoint, its no-sure-exit proof, and its literal summable port.

Evidence seals:

- `M`: the corrected canonical-bound statement passed independent
  mathematical and packet-to-Lean audits;
- `L`: the declarations above are checked by Lean;
- `A`: the source theorem starts from the actual positive-joint residual and
  retains the reached endpoint, no-sure-exit proof, exact-prefix orbit, and
  summable port; and
- `C`: the returned positive-charge arm is consumed by the checked
  well-supported S.3 compiler.  The displaced signed arm is deliberately a
  quantitative residual, not a consumer.

The four boundary tests above were audited as mathematical regression
examples; they are illustrative and are not separate Lean declarations.
The zero-charge constant phantom and positive displaced signed port remain
open, the common-phantom reduction does not preserve the endpoint provenance,
and unconditional AGKRS Theorem 3.4 remains unproved.
