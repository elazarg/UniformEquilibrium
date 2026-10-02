# AGKRS source closure: retracted endpoint consumer and an exact S.2 no-go

**Author:** CODEX_MINER  
**Status:** reviewed/REVISE.  The proposed endpoint-to-S.1 consumer is false
and retracted.  The priority audit and exact one-player S.2 no-go pass.  
**Date:** 2026-08-25  
**Head audited:** `9457ec3`

**Independent review:**
[`CODEX_EULER`](../feedback/CODEX_MINER__AGKRS_SOURCE_CLOSURE_NONPOSITIVE_ENDPOINT_CONSUMER__BY_CODEX_EULER.md).

## Question attacked

I audited the three residual inputs of
`theorem3_4_of_prioritizedSourceClosures` and looked for the shortest
residual-to-branch consumer, without replacing the theorem-level problem by
another unconsumed split.

The positive-joint-reach residual is the shortest finite-dimensional seam:
it already has a zero-debt semantic endpoint at an exact punishment floor,
and the checked sure-exit consumer has exhausted the direct route to S.2.  My
first proposed endpoint-to-S.1 consumer was false: quitting immediately can
collide with an opponent's date-zero quit, so the semantic envelope need not
dominate the singleton reward.  Section 2 records the retraction.  Section 3
gives a literal source-level one-player model proving that the no-sure-exit
condition cannot, even with all the actual-source data, be sent to S.2 alone.

This does **not** close Theorem 3.4 or any positive-source subcase.  The
positive endpoint seam, all three arms of the prioritized residual, and the
two scalar obstructions in the negative-owner residual remain open.

## Exact source audit

I read the following declarations and their defining files.

1. `QuittingPrioritizedRefinedSourceResidualAt` and
   `QuittingPayoffTable.fixedCorrectedBranches_or_cofinally_prioritizedResidual`
   in
   `UniformEquilibrium/Quitting/Classification/Existence/PrioritizedRefinedSourceBoundary.lean`.
2. `QuittingCorrectedPointwiseRefinedSourceResidualAt` and its three arms in
   `UniformEquilibrium/Quitting/Classification/Existence/PositiveRhoLandingClassificationBoundary.lean`.
3. `QuittingPositiveJointPrefixReachSource`,
   `QuittingUniqueExceptionalOwnerSource` in
   `UniformEquilibrium/Quitting/Classification/Existence/DiffuseStationaryPrefixSourceAttachments.lean`.
4. `QuittingDiffuseStationaryPrefixFamily` in
   `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedWitnessRegimes.lean`.
5. `QuittingPositiveJointPrefixReachPunishmentEndpoint`, its exact
   zero-debt/equality lemmas, `HasSureExitNashPrefix`, and
   `QuittingPositiveJointPrefixReachNoSureExitResidual` in
   `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointPrefixReachEndpoint.lean`.
6. `QuittingDivergentNegativeExceptionalOwnerResidual` and
   `stationary_or_instant_or_wellSupported_or_noSureExit_or_negativeOwner` in
   `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedNegativeOwnerBoundary.lean`.
7. `QuittingDivergentNegativeExceptionalOwnerResidual.instant_or_floorAboveSolo_or_joinGain`
   in
   `UniformEquilibrium/Quitting/Classification/Existence/NegativeExceptionalOwnerInstantObstruction.lean`.
8. The branch predicates and
   `theorem3_4_of_prioritizedSourceClosures` in
   `Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`.
9. `IsQuittingZeroSolo` and the exact all-Continue equilibrium in
   `UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`, and the
   all-Continue exact-root characterizations in
   `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.

A narrow duplicate/no-go search also found
`RefinedSourceResidualRegression.stationaryExistence_and_refinedSourceResidualAt`
and the fixed-horizon `ExceptionalOwnerSourceRegression`.  The first is important
for scope: raw corrected residuals can coexist with S.1.  The second does not
apply to the divergent negative residual.

## 1. Logical form of the three obligations

### 1.1 Prioritized corrected residual

For a fixed positive `delta`, this structure contains

* one of the three corrected source residuals;
* `not_stationary` at `delta`;
* `not_instant` at `delta`;
* `not_wellSupported` at `delta`; and
* `not_generated` at `delta`.

Consequently a branch-valued consumer with the codomain used by the capstone
is necessarily a **nonexistence theorem** for the supplied prioritized
object.  Indeed, each of the global S.1, instant S.2, or well-supported S.3
existence predicates specializes at the same positive `delta`, contradicting
the corresponding field.  There is no constructive sense in which the
object can itself output one of those three global branches while remaining
inhabited.

Thus the first obligation is exactly: rule out the cofinal prioritized
residual after using its retained source.  It is not analogous to the other
two obligations, which do not carry global branch exclusions.

The three exact arms of its `residual` field are:

* an actual positive-rho all-Continue source with a nonzero phantom value;
* a positive-absorption landing with either temporal nonrecurrence or a
  negative punishment coordinate; or
* a positive-survival support--Bellman boundary with an actual positive
  singleton and persistent unrestricted suffix-deviation defect.

No checked declaration inspected assigns a terminating finite rank to these
three arms.

### 1.2 Positive-joint no-sure-exit residual

This structure retains an actual stationary-prefix source.  Its reached
punishment suffixes are unrestricted-behavior approximate equilibria after
division by the positive reach probability.  Compactness supplies a semantic
endpoint `(U,B)` satisfying

\[
 B_i-U_i=0\quad\hbox{for every }i,
 \qquad B_p=U_p=P_p
\]

for one punished player `p`.  The checked consumer closes S.2 exactly when
some such endpoint admits an exact one-stage Nash root with a sure quitter.
The residual asserts failure of this test for **every** eligible endpoint.
It carries no exclusion of S.1 or S.3.

### 1.3 Divergent negative exceptional-owner residual

This structure retains an actual diffuse family, a unique exceptional owner,
divergent selected horizons, and strictly negative owner singleton
self-payoff.  Checked competing-clock estimates concentrate the prescribed
initial payoff on the owner's singleton vector.  The current shortest
consumer is

\[
  \mathrm{S.2}\quad\text{or}\quad
  r_o(\{o\})<P_o\quad\text{or}\quad
  \exists j\ne o:\ r_j(\{o\})<r_j(\{o,j\}).
\]

The last two alternatives are genuine strategic inequalities, not missing
probabilistic source fields.  No branch consumer or decreasing rank for them
is present in the named source.

## 2. Retraction of the proposed nonpositive-endpoint consumer

The implication

\[
  U_i\le0\ \forall i
  \quad\Longrightarrow\quad
  r_i(\{i\})\le0\ \forall i
\]

is **false** for a general zero-debt terminal semantic endpoint.  The bad
step was the assertion `r_i({i}) <= B_i`: an always-Quit deviation can collide
with opponents who also Quit at date zero, so its payoff need not be the
singleton reward.

The review gives an exact two-player diagonal endpoint `(U,B)=((0,0),(0,0))`
with `r_i({i})=1`.  It is a literal carrier point, has zero debt and an exact
punished-coordinate cap, yet is not zero-solo.  Positive reach of a preceding
prefix does not impose opponent continuation at date zero of the reached
punishment suffix, so source provenance does not repair this implication.

A valid conditional statement would additionally assume
`r_i({i}) <= B_i` for every `i`, equivalently the needed singleton domination.
That hypothesis is absent from
`QuittingPositiveJointPrefixReachNoSureExitResidual` and essentially inserts
the zero-solo gate rather than derives it.  No positive-source branch consumer
is claimed here.

## 3. Exact actual-source no-go for an S.2-only consumer

The following model shows that the all-endpoint no-sure-exit condition is not
a disguised route to S.2.

### Game

There is one player `*`.  Never quitting pays `0`, and the only nonempty
terminal set pays

\[
                         r_*(\{*\})=-1.
\]

### A literal positive-joint-reach source

For `n=0,1,2,...`, set

* `error n = 1/(n+1)`;
* `root n` equal to pure Continue;
* `horizon n = 2`;
* `punished n = *`; and
* every punishment row equal to pure Continue.

This is a `QuittingDiffuseStationaryPrefixFamily`:

* the errors are positive and tend to zero;
* the horizon is greater than one;
* the full stationary-prefix-then-punishment plan is simply all-Continue;
* its prescribed payoff is `0`, while any unrestricted behavioral deviation
  has payoff `-a\le0`, where `a` is its probability of ever quitting, so the
  plan is exact Nash;
* the punishment best-response value and punishment value are both `0`; and
* the root live mass is `1`.

Take `selected=id` and `jointLimit=1`.  Whole-prefix joint survival is
identically `1`, so this is a literal
`QuittingPositiveJointPrefixReachSource`.

### Every eligible endpoint is exactly `(0,0)`

For an arbitrary behavioral profile, let `a` be the probability that the
player ever quits.  Its prescribed payoff is `U=-a\le0`.  Its unrestricted
best-response envelope is `B=0`: all deviations have payoff at most zero and
always-Continue attains zero.  These identities/inequalities persist on the
closed semantic carrier.

An eligible punishment endpoint also satisfies `B-U\le0`; carrier
nonnegativity gives equality.  Since `B=0` and `U\le0`, it follows that
`U=B=0`.  The punishment value is also zero, so this is the only eligible
endpoint.

The only root with a sure quitter is pure Quit.  Over continuation value zero
it gives prescribed payoff `-1`, while deviation to pure Continue gives `0`.
It is not an exact one-stage Nash root.  Hence **every** eligible endpoint
fails `HasSureExitNashPrefix`, and the displayed source defines a literal
`QuittingPositiveJointPrefixReachNoSureExitResidual`.

### S.2 nevertheless genuinely fails

Any instant-punishment profile in this one-player game has the only player's
first-stage action equal to pure Quit.  It therefore pays `-1`.  Replacing the
entire behavioral strategy by always-Continue pays `0`, independently of the
declared punishment continuation.  The unrestricted gain is exactly `1`.

Thus `QuittingInstantPunishmentεEquilibriumExistence` fails (take any
`0<epsilon<1`), and so does the paper-facing small S.2 branch.  On the other
hand, all-Continue is an exact stationary equilibrium, so S.1 holds by direct
one-player analysis, not by the retracted Section 2 claim.

This is an exact no-go to

\[
 \text{positive-joint no-sure-exit residual}\Longrightarrow\mathrm{S.2}.
\]

It is stronger than merely exhibiting an endpoint without a sure root: it
constructs every field of the actual source residual and proves global S.2
failure against unrestricted behavioral deviations.

## 4. Consequences for the theorem-level attack

1. The first capstone consumer must prove emptiness of the prioritized source
   object; its branch-valued codomain cannot coexist with the object's own
   fixed-scale negations.
2. The positive residual cannot be closed by weakening or iterating the
   sure-exit S.2 test.  A cross-branch consumer is mandatory.  Even
   coordinatewise nonpositive endpoint payoff does not imply the singleton
   domination needed for all-Continue S.1.
3. A formal all-Continue semantic self-loop at an endpoint does not by itself
   realize its continuation payoff; treating it as an actual stationary
   profile would repeat the known phantom error.
4. The negative residual's shortest checked path is already the exact
   instant/floor/join trichotomy.  Closing it requires consuming the
   punishment-floor gap or the outsider join gain using the actual divergent
   source; another subdivision of those inequalities would not answer the
   question.

## Novelty and honesty audit

* The proposition originally proposed in Section 2 is false and is explicitly
  retracted.  The review's collision countermodel is decisive.
* The one-player construction in Section 3 is an explicit verifier of every
  field of the positive source residual.  It is not a counterexample to
  Theorem 3.4 because S.1 holds.
* `RefinedSourceResidualRegression` is related but concerns the corrected
  pointwise support--Bellman residual in the positive one-player unit-reward
  game.  It neither constructs this positive-joint source residual nor proves
  S.2 failure.
* No positive-endpoint case or negative scalar obstruction is claimed closed.

## Requested independent checks

1. Check every field of the one-player `QuittingDiffuseStationaryPrefixFamily`
   and `QuittingPositiveJointPrefixReachSource`.
2. Check the characterization of every eligible endpoint as `(0,0)` and the
   exact failure of `HasSureExitNashPrefix`.
3. Check the unrestricted behavioral deviation proving failure of the entire
   S.2 existence branch, not merely failure of one proposed root.

## Next question

Can the actual reached-source provenance supply either singleton domination
or a different stationary/sequential compiler at a zero-debt punishment
endpoint?  Any valid argument must price date-zero collisions explicitly and
must not treat a semantic self-loop as an executable stationary payoff.
