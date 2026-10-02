# Second review of Persistent Deleted-Clock Characterization by `CODEX_GAUSS`

Reviewed note:
[`CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md`](../notes/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md),
Section 5, Proposition 3 and Corollary 3A.

## Claim checked

A positive terminal payoff-difference atom between profiles differing only in
one mover's complete stopping law forces a quantitative ever-Quit mass on one
of the two mover laws.  The checked vanishing-debt atom alternative therefore
forces a finite prefix with a fixed raw mover-hazard quota.  If two distinct
positive-debt movers are available, independently alternating such prefixes
produces an abstract raw root schedule with two persistent labels, but not an
exact reached-tail chronology.

This is an ordinary-mathematics audit.  I did not run Lean and assign no
`L`, `A`, or `C` seal.

## Verdict

**VALID in the stated scope.**  The conditioning argument, total-variation
orientation, constants, finite-prefix truncation, and source-matching
qualification all check.  I found no mathematical objection.

In particular, the conclusion is deliberately weaker than a producer for
`QuittingChronologicalDebtShadowingCertificate`: it selects a local prefix of
either the source mover law or the replacement mover law at each rank.  It
does not say that the chosen complete profile is the reached tail of the
preceding block, that the selected side is stable with rank, or that a
reprojection error is summable.

## Independent calculation

Fix every player other than mover `m`.  In a finite quitting game, the only
live history at date `t` is the all-Continue history.  Conditional on `m`'s
pure stopping choice `T : Option Nat`, the probability of a fixed absorbing
coalition `S` is therefore one common function

```text
f(T) in [0,1]
```

for the source and replacement laws.  All other behavioral randomizations
remain identical.  Thus, writing `mu_sigma, mu_tau` for the induced stopping
laws and using the repository's factor-two convention for
`pmfGeneralTV`,

```text
|Pr_P(S) - Pr_Q(S)|
  = |E_mu_sigma f - E_mu_tau f|
  <= 2 TV(mu_sigma, mu_tau).                         (R1)
```

If

```text
alpha <= K (Pr_P(S)-Pr_Q(S)) r(S)_o,
alpha > 0,
|r(S)_o| <= M,
```

then the signed product is positive and

```text
TV(mu_sigma,mu_tau) >= alpha/(2 K M).               (R2)
```

This also proves `M>0`.  The exact checked inequality
`stoppingLawTV_le_everQuitMass_add`
(`UniformEquilibrium/Quitting/Paths/StoppingLawExposure.lean`) gives

```text
TV(mu_sigma,mu_tau) <= e(sigma)+e(tau),
```

so at least one law satisfies

```text
e >= alpha/(4 K M).                                  (R3)
```

The prescribed arm of
`HasQuittingStoppingLawVanishingDebtAtomAlternative`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`)
has `alpha=q/2`, while its common-response rectangle arm has `alpha=q/4`.
In the rectangle, the same pure-time observer response occurs on both sides,
so the two profiles still differ only in the mover law.  The uniform weaker
bound is therefore exactly

```text
e >= q/(16 K M).                                     (R4)
```

No endpoint-debt estimate is needed for this consequence.

Finally, `hasSum_quittingHazardStopMass`
(`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`) says that the
finite stopping masses sum to `e`.  Because (R4) is positive, some finite
cutoff carries at least `e/2`.  At each date,

```text
stopMass(t) = survival(t) * rawQuit(t) <= rawQuit(t),
```

so the raw marginal hazards before that cutoff sum to at least

```text
q/(32 K M).                                          (R5)
```

Replacing the coordinate maximum `M` by the larger canonical
`quittingRewardBound reward` is valid.  Positivity of the atom ensures this
canonical bound is nonzero, so Corollary 3A does not divide by zero.

## Quantifiers and boundary tests

- `QuittingVanishingDebtAtomAccess.atom_eventually` gives the alternative at
  every sufficiently large rank with one fixed positive `charge`; the chosen
  arm, side, terminal coalition, and finite cutoff may vary with rank.
- For two positive-debt movers,
  `exists_quantitativeStrongVanishingDebtAtomAlternative_of_mover` can be
  applied to each.  Intersecting the two eventual rank sets and alternating
  the selected finite prefixes gives infinitely many fixed positive hazard
  quotas for each label.  Hence both raw marginal series diverge.  This is
  enough for Propositions 1--2 on the assembled raw schedule, independently
  of what the other labels do.
- The two-player signed-atom example has the correct orientation.  Source
  mass zero, replacement mass one, and reward `-1` give atom
  `(0-1)(-1)=1`.  Choosing a sufficiently small positive charge satisfies the
  prescribed arm while only the mover has any hazard.  It correctly shows
  that one bare atom cannot yield two deleted clocks.

## Exact surviving obligation

The result removes raw one-label hazard availability as the immediate
obstruction.  It does not remove the two genuinely semantic obligations:

1. retain two distinct mover labels in the singleton-support case; and
2. convert the independently selected source/replacement prefixes into a
   reached-tail chain while keeping the necessary reprojection losses
   summable (or retaining a fixed positive hazard fraction).

