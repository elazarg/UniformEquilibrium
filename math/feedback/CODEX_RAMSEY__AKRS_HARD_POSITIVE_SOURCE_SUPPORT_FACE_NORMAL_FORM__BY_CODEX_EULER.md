# Review of `CODEX_RAMSEY__AGKRS_HARD_POSITIVE_SOURCE_SUPPORT_FACE_NORMAL_FORM`

Reviewer: `CODEX_EULER`

Verdict: **PASS as an internal source-native normal form; not export-ready as
an AGKRS consumer.**

## Claim reviewed

The note starts from an actual
`QuittingPositiveJointPrefixReachNoSureExitResidual reward` and assumes the
global failures of the stationary S.1 and well-supported S.3 branches (with
the instant-punishment failure retained in the hard interface).  After one
common strict subsequence and a fixed punished label it claims:

1. at fixed horizon, a limiting repeated root is exact over two consecutive
   tails attached to one eligible reached punishment endpoint, has no sure
   quitter, and has proper active-Quit support; or
2. at divergent horizon, the root tends to all Continue and the same compact
   source yields both a nonzero forward phantom and an eligible zero-debt
   reached punishment endpoint.

I checked the source selection, endpoint debt, the `H-1/H` orientation, the
stationary compiler (including the one-player boundary), the live-mass-one
argument, and the precise nonclaim about support rank.

## 1. Common source and eligible endpoint: PASS

Fixing the finite punished label and then applying the fixed-or-divergent
horizon normal form preserves one composite strict subsequence of
`source.selected`.  Along every further subsequence,

```text
family.error -> 0,
prefixJointSurvival -> jointLimit > 0,
punishmentNashError = 2 error / prefixJointSurvival -> 0.
```

The last assertion is exactly
`QuittingPositiveJointPrefixReachSource.punishmentNashError_tendsto_zero`, and
eventual positive reach permits
`punishment_nash_of_joint_pos`.  Compactifying the actual reached punishment
semantic pairs along this same selection gives a carrier point `E` with
coordinate debts at most zero.  Carrier nonnegativity makes every debt
exactly zero, hence `E.1=E.2` coordinatewise.  The fixed punished-label cap
passes to the limit and combines with the carrier punishment lower bound to
give equality at that label.  These are precisely the fields and checked
consequences of
`QuittingPositiveJointPrefixReachPunishmentEndpoint`.

The source-provenance wording is valid, with one proof-writing point worth
making explicit in formalization.  In the divergent arm,
`exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq` internally
extracts a further compact subsequence.  Its recorded `punishmentTail` is
equal to the already selected `E` by uniqueness of limits: the complete
punishment semantic sequence already tends to `E`, while the theorem's
internal subsequence tends to `limit.punishmentTail`.  The zero-debt and
punishment-label fields may equivalently be reproved directly on that internal
subsequence.  No independently selected endpoint is being identified.

## 2. Fixed horizon and the consecutive-tail orientation: PASS

The family repeats its root at times `0,...,H` and enters punishment at
`H+1`.  Thus the last repeated row, time `H`, sees the punishment payoff tail
`E.1`; the preceding row, time `H-1`, sees

```text
W = quittingRootSuccessorPayoff reward E.1 q.
```

This is the orientation claimed in the note.  Whole-prefix survival through
`H+1` is a lower bound for survival to either reached row.  Since it tends to
the positive `jointLimit`, the reached-row Nash errors at both rows tend to
zero.  Continuity therefore gives exact endpoint Nash, equivalently exact
root Nash, for `q` against both `E.1` and `W`.

If a coordinate of `q` quits surely, exact Nash over `E.1` is a literal
`HasSureExitNashPrefix` for the same eligible endpoint, contradicting the
residual's universal `noSureExitNashPrefix` field.  Hence every coordinate
continues with positive probability.

Now suppose every coordinate also quits with positive probability.  Each
player mixes both actions at both tails.  The player's Quit endpoint is
tail-independent, while its Continue endpoint changes between `E.1` and `W`
by

```text
opponentContinueMass_i(q) * (W_i - E_i).
```

The opponent Continue mass is strictly positive because no opponent quits
surely.  Exact indifference at both tails therefore gives `W_i=E_i` for every
player, or

```text
E.1 = quittingRootSuccessorPayoff reward E.1 q.
```

Full active support and nonemptiness (already witnessed by the punished
label) give positive joint absorption.  The fixed-point theorem identifies
`E.1` with the actual stationary payoff.  The exact stationary endpoint
compiler then gives unrestricted behavioral terminal Nash once its saturated
boundary is checked:

* with at least two players, every player has an opponent with positive Quit
  probability, so no opponent-Continue mass is saturated;
* with one player, mixing gives `E.1=r({i})`, while diagonal carrier membership
  gives `E.1=E.2>=0` because Never is an available unilateral response.  Hence
  `max(0,r({i}))<=E.1`.

This produces S.1, contrary to the hard hypothesis.  Therefore at least one
coordinate has zero limiting Quit probability.  Together with no sure quitter
this is exactly the claimed proper active-support face, including the
all-Continue limiting root as a permitted extreme.

## 3. Divergent horizon: PASS

For the selected one-row Continue mass `c_n`, the exact repeated-prefix
identity is

```text
prefixJointSurvival_n = c_n^(H_n+1).
```

If `H_n -> infinity` and the left side tends to `jointLimit>0`, then
`c_n -> 1`: any subsequence with `c_n<=1-eta` would have powers tending to
zero.  Applying
`exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq` at live
limit one and excluding S.3 through
`QuittingPositiveLiveStationaryPrefixLimit.wellSupported_or_phantom` gives an
exact all-Continue phantom.  The source endpoint remains the same eligible
`E` by the common-subsequence argument in Section 1.

Let `X=limit.value 0`.  The checked phantom inequality gives
`r_i({i})<=X_i` for every player.  If `X=0`, every solo self-reward is
nonpositive, so `IsQuittingZeroSolo reward`; the literal all-Continue profile
then supplies S.1 through
`quittingStationaryεEquilibriumAt_of_zeroSolo`.  Thus no S.1 forces
`X!=0`.  This is the exact claimed nonzero phantom conclusion; it does not
identify `X` with `E.1`.

## 4. Scope, novelty, and rank assessment

The result is a genuine provenance improvement over reapplying a global
diffuse classification: each arm retains one actual positive-joint source and
its reached punishment endpoint.  The fixed arm additionally places the two
last repeated rows over that endpoint; the divergent arm co-realizes the
forward phantom and escaping tail along one compact selection.

It does **not**, however, close the maintained positive-joint residual or
supply a well-founded rank:

* a proper active support of the limiting root is not a regenerated
  `QuittingPositiveJointPrefixReachNoSureExitResidual` on a smaller player
  game, and no punished-tail/deviation data are transported through deletion;
* the nonzero phantom and eligible endpoint remain different ends of an
  escaping prefix, with no closed path or ordering between them; and
* the instant-punishment negation is part of the hard interface but supplies
  no additional consumption inside these two conclusions.

Accordingly this is mathematically suitable as an internal normal form and
next-step interface.  It does not meet the question's export threshold by
itself: no S.1/S.2/S.3 branch is produced on the hard residual, and the proper
face is not a maintained strict support descent.

## Sources checked

* `UniformEquilibrium/Quitting/Classification/Existence/DiffuseStationaryPrefixSourceAttachments.lean`
* `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointPrefixReachEndpoint.lean`
* `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedWitnessRegimes.lean`
* `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedPositiveLiveLimit.lean`
* `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`
* `UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`

