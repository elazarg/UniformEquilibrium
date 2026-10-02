# Independent review of the arbitrary-profile two-pair clock adapter

Reviewer: `CODEX_CEDAR`

Source reviewed:
[`SIX_PLAYER_ARBITRARY_PROFILE_CLOCK_ADAPTER.md`](../formalized/SIX_PLAYER_ARBITRARY_PROFILE_CLOCK_ADAPTER.md).

## Verdict

**Mathematics PASS; source/novelty audit REVISE, then PASS after one bounded
repair.**  The square-root recurrence, both squared-amplitude identities,
finite-to-infinite passage (including positive Never mass), and actual-profile
terminal-law disintegration are correct.  Before export, cite Proposition 18
of `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`, which already proves
the stronger ordinary countable-clock theorem for arbitrarily many disjoint
pairs.  The genuinely new content here is the literal repository-semantic
bridge from an arbitrary behavioral profile to the checked
`TwoPairHazardClock`, not the probability inequality as ordinary mathematics.

## Clock recurrence

At the unique live history at date `t`, put `q_i=q_i(t)` and `c_i=1-q_i`.
The checked survival recurrence is

```text
S(t+1)=S(t) * product_(i:Fin 6)c_i.
```

Every factor is nonnegative.  Thus repeated use of
`sqrt(xy)=sqrt(x)sqrt(y)` gives

```text
sqrt(S(t+1))
 =sqrt(S(t))*sqrt(c_5*c_6)*sqrt(c_1*c_2)*sqrt(c_3*c_4),
```

which is exactly the proposed `survivalRoot_step`.  The players outside the
two designated pairs are neither omitted nor treated additively; their two
Continue factors occur in the single background square root.  At `t=0`,
joint survival is one, so the clock's initial field is exact.

## Stage amplitudes

The first target amplitude is

```text
sqrt(S)*sqrt(c_5*c_6)*sqrt(q_1*q_2)*sqrt(c_3*c_4).
```

All radicands are nonnegative, so its square is exactly

```text
S*q_1*q_2*c_3*c_4*c_5*c_6,
```

the unconditional first-coalition mass of `{1,2}` at that date.  The second
amplitude analogously squares to

```text
S*c_1*c_2*q_3*q_4*c_5*c_6.
```

These are equalities, not estimates.  They retain simultaneous Quit and every
background Continue factor.

## Infinite horizon and Never mass

For each finite `N`, the checked theorem
`TwoPairHazardClock.finite_targetMass_sqrt_sum_le_one` applies to the two
amplitude-square partial sums.  Each partial sum is nonnegative and increasing.
Exact-coalition stage mass is bounded by stage absorption mass, whose total
sum is at most one, so both series are summable.  Their partial sums converge
to the two `tsum`s.  Continuity of `Real.sqrt` and closedness of `<=` therefore
pass the finite inequalities to

```text
sqrt(rootSequenceTerminalCoalitionMass roots A)
 +sqrt(rootSequenceTerminalCoalitionMass roots B)<=1.
```

No assumption that joint survival tends to zero is used.  Positive Never mass
is simply unused square-root budget.

For `roots=quittingProfileLiveRoot reward sigma`, the checked identity
`quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot` identifies the
survival prefix.  The checked stage factorization then identifies each clock
stage mass with `quittingStageCoalitionMass`.  Finally
`quittingTerminalOutcomeMass_eq_timeDisintegration` says that a nonempty
terminal coalition's actual mass is the `tsum` of those stage masses.  The
Never branch occurs only at outcome `none` and contributes zero to the exact
events `A,B`.  This proves the proposed terminal identification and the
arbitrary-profile inequality.

## Behavioral semantics

Before absorption there is only the all-Continue public history.  An arbitrary
behavioral profile may be time-dependent and use fresh private randomization,
but at each live history the simultaneous action law is the independent
product of its six marginal PMFs.  The live-root word records precisely these
conditional hazards.  No independence of one player's coins across time is
needed: the conditional hazard factorization plus survival recursion is
sufficient.  No deviation or Nash premise enters this law theorem.

## Novelty search and required repair

A narrow Lean search found the finite square-root core in
`MathUE/Probability/SquareRootCoalitionClock.lean` and the source-native root
sequence quantities in
`UniformEquilibrium/Quitting/Chronology/TwoPairClockBoundary.lean`, but no
checked theorem composing them for every behavioral profile.

However, Section 24, Proposition 18 of
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` already gives the stronger
ordinary result

```text
sum_k sqrt(a_k)<=1
```

for any finite family of disjoint pairs and arbitrary independent countable
quit-time laws.  Its backward-recursion proof includes Never mass.  Therefore
the new note must not present inequality (1) itself as new ordinary
mathematics.  After adding this source and stating that the new contribution
is the exact `BehaviorProfile -> live roots -> checked clock -> terminal law`
adapter, the novelty claim is accurate.

## Scope

The result supplies only the missing `hclock` premise for the already checked
six-player conditional ledger.  It forces neither target atom to be positive,
does not remove the pure-target equilibrium, and does not produce a terminal
exploitability gap.  The note states these nonclaims correctly.
