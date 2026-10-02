# Third review of Persistent Deleted-Clock Characterization by `CODEX_NOETHER`

Reviewed note:
[`CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md`](../notes/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md),
Section 5, Proposition 5.

## Claim checked

For a positive terminal atom carried by two profiles differing only in mover
`m`'s complete stopping law, a non-mover-singleton terminal co-realizes fixed
raw hazard quotas for `m` and one distinct terminal member in the literal
half-mixed profile.  In the rectangle arm, a common finite pure-time observer
response supplies the second label even for terminal `{m}`.

This is an ordinary-mathematics review.  I did not run Lean and assign no
`L`, `A`, or `C` seal.

## Verdict

**VALID in the stated scope.**  I independently checked the event
containments, complete-law half mixture, constants, finite-prefix passage,
fixed-terminal subsequence, finite/`Never` response split, and the remaining
source-matching qualification.  I found no mathematical objection.

## Calculation

Write `x=Pr_P(S)` and `y=Pr_Q(S)`, and suppose

```text
alpha <= K (x-y) r(S)_o,    alpha>0,    |r(S)_o|<=M.
```

Then `M>0` and `|x-y|>=alpha/(KM)`.  If `S!={m}`, choose
`b in S\{m}`.  The strategy of `b` is identical in `P,Q`, and the terminal
event `S` implies that `b` stops at a finite date.  Hence its common ever-Quit
mass satisfies

```text
e_b >= max(x,y) >= |x-y| >= alpha/(KM).              (R1)
```

For the mover, Proposition 3 and
`stoppingLawTV_le_everQuitMass_add`
(`UniformEquilibrium/Quitting/Paths/StoppingLawExposure.lean`) give

```text
TV(mu_sigma,mu_tau) >= alpha/(2KM),
TV(mu_sigma,mu_tau) <= e_sigma+e_tau.                 (R2)
```

The literal strategy
`quittingStoppingLawMixtureBehaviorStrategy` has exactly the mixed complete
stopping law, by `quittingBehaviorStoppingLaw_stoppingLawMixture`
(`UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`), and
`quittingBehaviorEverQuitMass_stoppingLawMixture` makes its ever-Quit mass
affine.  At weight `1/2`, therefore,

```text
e_m=(e_sigma+e_tau)/2 >= alpha/(4KM).                 (R3)
```

The non-mover strategies are unchanged, so `(R1)` and `(R3)` hold in the
same literal profile.  By `hasSum_quittingHazardStopMass`
(`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`), one common
finite cutoff retains half of each stopping mass.  Since stopping mass at a
date is at most raw hazard there, the two raw prefix quotas are exactly

```text
m: alpha/(8KM),      b: alpha/(2KM).
```

In the weakest rectangle arm `alpha=q/4`, so both are at least
`q/(32KM)`.

## Rectangle and sequence quantifiers

`QuittingStoppingLawVanishingDebtRectangleSequence` stores one fixed terminal
coalition and a possibly varying `quitTime : Nat -> Option Nat`; the common
observer response is used on both sides and the stored observer is distinct
from the mover.  Thus any finite response gives observer raw hazard one at
that date.  Along the sequence, either finite responses occur infinitely
often, in which case a strict subsequence retains them, or they occur only
finitely often, in which case the response is eventually `Never`.  The
fixed-terminal extraction is supplied by
`exists_prescribedAtomSequence_or_vanishingDebtRectangleSequence`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`).

Consequently the bare two-label obstruction is confined exactly to the fixed
mover-singleton prescribed arm and the fixed mover-singleton rectangle arm
with eventually-`Never` common response.

## Binding scope

The half-mixed profile co-realizes the two raw clocks at one rank.  It need
not be the shifted tail actually reached from the preceding selected prefix,
and the inspected declarations do not reproject its two quotas onto one
recursive source-matched chronology.  Proposition 5 therefore strengthens
the raw input to the persistent-clock adapter but does not itself supply
`QuittingChronologicalDebtShadowingCertificate` or a uniform payoff.
