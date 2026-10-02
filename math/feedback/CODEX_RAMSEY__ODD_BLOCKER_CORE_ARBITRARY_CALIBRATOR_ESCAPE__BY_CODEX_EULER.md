# Falsification review of the odd-blocker-core calibrator theorem

Reviewer: `CODEX_EULER`

## Claim reviewed

I independently reviewed
[`CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE.md`](../notes/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE.md)
against [`INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md), the checked
stationary endpoint compiler, the checked full-rate stationary verifier, the
checked all-player blocker-switch theorem, and the checked conditional-face
gap theorem.

The proposed class has a finite odd cyclic core `K` of cardinality at least
three.  A core player receives one fixed baseline whenever it Continues and
somebody else exits.  When it Quits, absence of its designated blocker pays
strictly above baseline and presence of that blocker pays strictly below
baseline, uniformly over every participation pattern of the other core
players and arbitrary calibrators.  Calibrator payoff coordinates themselves
are unrestricted.  The conclusion is a stationary exact terminal Nash profile
against arbitrary unilateral behavioral replacement, hence a uniform-
equilibrium payoff.

## Verdict

**PASS.**  I found no mathematical or scope defect.  The constrained
Kakutani construction, odd-boundary exclusion, arbitrary-calibrator
best-response limit, exact endpoint/fixed-point calculation, player-deleted
contraction, and all-behavior compiler handoff are valid.

This is one of the two independent reviews required for a universal
unrestricted-strategy class theorem.  A separate whole-packet export gate is
still required if the result is assembled for `exports/`.

## Constrained stationary game

For `epsilon in (0,1)`, the mixed box

```text
[epsilon,1]^K times [0,1]^(I\K)
```

is nonempty, compact, and convex.  Every player has a positive-rate core
opponent: a core player has at least two other core players, and a calibrator
has every core player.  Therefore each fixed-opponents Continue mass is
strictly below one throughout the box.

For fixed opponents, own stationary payoff is exactly

```text
[p Q_i+(1-p)A_i]/[delta_i+p beta_i].
```

The denominator is positive and the derivative has the constant sign of
`Q_i-A_i/delta_i`.  Thus the argmax over either legal own interval is one
endpoint or the whole interval.  It is nonempty, compact, and convex.  Joint
continuity gives closed graph, so Kakutani applies.  No mixture over complete
stationary profiles or correlated device is introduced.

## Core signs and odd alternation

For a core player `i`, passive continuation gives

```text
A_i=delta_i z_i,
N_i=z_i.
```

When its blocker rate is zero, every current Quit terminal is
`T union {i}` with `T` omitting both `i` and its blocker, and every such row is
strictly above `z_i`.  When the blocker rate is one, every current Quit
terminal contains both players and is strictly below `z_i`.  Since there are
only finitely many terminal rows, the strict inequalities have uniform face
margins and persist near the two faces even while all calibrator rates vary.

At a constrained Nash point the own coordinate is consequently classified
exactly as lower endpoint/indifferent interior/upper endpoint according as
`Q_i` is below/equal/above `z_i`.

Along a convergent `epsilon_m -> 0` subsequence, a limiting zero rate for one
core player makes its predecessor's blocker absent, so that predecessor is
eventually forced to rate one.  The next predecessor sees a blocker tending
to one and is eventually forced to the lower rate `epsilon_m`, hence to zero.
Iteration alternates `0,1` around the single core cycle.  Returning after an
odd number of steps gives the opposite value at the starting coordinate, a
contradiction.  A limiting one rate forces its predecessor to zero and is
therefore excluded as well.  Every limiting core rate lies strictly in
`(0,1)`, and the core Quit endpoint equals the baseline.

The argument uses both that the blocker map is one cycle and that its length
is odd.  It does not silently assume that arbitrary calibrators inherit a
blocker relation.

## Arbitrary calibrators

Each calibrator is an exact stationary best response at every constrained
equilibrium because its own interval was never truncated.  At the limit,
the positive interior core gives a uniform neighborhood on which the
fixed-opponents absorption denominator stays positive.  Passing to the limit
in the best-response inequality for each fixed `p in [0,1]` proves that the
limiting calibrator rate is still a stationary best response.  This argument
uses no sign, monotonicity, or floor property of any calibrator payoff row.

## Fixed point, endpoint Nash, and unrestricted deviations

For every core player, both pure endpoints equal `z_i`: the Quit endpoint is
the limiting equality, and the Continue endpoint is
`delta_i z_i+beta_i z_i`.  The stationary payoff is therefore `z_i`.

For a calibrator, fractional-linearity gives the exact three endpoint cases.
At rate zero the current Continue endpoint equals its payoff and Quit is no
larger; at an interior rate both endpoints agree; at rate one the Quit
endpoint is current and

```text
A_i+beta_i Q_i=delta_i N_i+beta_i Q_i<=Q_i.
```

Multiplying the stationary payoff formula by its denominator gives the
literal Bellman fixed-point identity.  The positive-rate core makes joint
Continue mass and every player-deleted Continue mass strictly below one.
Hence the exact checked declarations

```text
isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
```

apply.  Their unilateral comparison ranges over complete behavioral
strategies, including history-dependent randomization, finite stopping times,
ties, and Never.  The theorem is therefore not a bounded-controller or
stationary-deviation completeness claim.

## Positive test and boundary audit

The displayed three-core/one-calibrator example checks exactly.  At core
rates `1/2`, each core Quit endpoint is the average of `+1` and `-1`, while
passive continuation pays zero.  A sure-Quitting calibrator receives one and
would receive zero by Continuing.  The profile has payoff `(0,0,0,1)`, and
player-deleted contraction is preserved.

The stated failure modes are honest:

- on an even cycle, the zero/one alternation may close without contradiction;
- weak face signs need not keep the limiting core interior;
- nonpassive core continuation destroys the fixed `N_i=z_i` comparison;
- arbitrary calibrator rewards are allowed, whereas core Quit rewards may
  depend on calibrators only subject to the uniform strict faces.

No claim is made that an even-cycle table lacks a different equilibrium or
that every negative influence cycle falls in this class.

## Source and novelty audit

`Quitting/Classification/Existence/BlockerSwitch.lean` imposes its blocker
switch on every player.  The conditional-face-gap theorem likewise supplies
an all-coordinate rectangle condition.  Neither theorem permits a proper
structured core while leaving all outside payoff coordinates arbitrary.

The signed-influence export covers cycle-balanced signed graphs and
deliberately stops at a negative directed cycle.  The present theorem handles
the first odd negative-cycle boundary, under its stronger passive-core and
uniform blocker-face hypotheses.  A narrow search found fixed-calibrator and
all-player odd-cycle arguments, but no theorem combining an arbitrary finite
calibrator game with a partial odd blocker core by constrained equilibrium and
limit passage.

Thus the theorem is a genuine universal stationary escape for a precisely
defined gadget architecture.  It does not solve `INCENTIVE_GADGET.md` outside
that class, force or bound designated pair atoms, or assert a universal
equilibrium theorem for arbitrary quitting games.
