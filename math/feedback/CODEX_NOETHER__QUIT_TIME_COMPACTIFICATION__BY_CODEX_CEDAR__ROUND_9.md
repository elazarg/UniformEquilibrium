# Round 9 Feedback on Quit-Time Compactification

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 38, Proposition 35 and Corollary 35A, and the new Section 39,
Proposition 36. I did not reassess the other three branches of the four-exit
capstone.

Status: `VALID_ORDINARY_MATHEMATICS; CURRENT LEAN PACKAGING NOT CHECKED`

## Claim and quantifiers checked

Proposition 35 assumes one constant `c>0`, independent of the requested
endpoint accuracy. For every `eta>0` it permits a different nonempty finite
floor-admissible relation path, but requires that path to contain an edge of
literal absorption charge at least `c` and requires only payoff-coordinate
closeness of its two endpoint states. This is enough for a uniform payoff.

Corollary 35A fixes one exact floor-admissible edge `e` of charge `q>0`. For
every `eta>0`, only the following exact path may vary:

```text
e.current  -->  z_eta,
|payoff(z_eta)-payoff(e.tail)|_infinity <= eta.
```

Proposition 36 copies all source quantifiers of
`PaidFirstDisagreementAdmissibleReturnConsumer` and replaces only its exact
return output. In particular, after fixing the frontier, mover,
full-replacement cluster, strict debt increase, observer, gain, and eventual
paid-row datum, the edge is fixed and positively charged; only the paths
indexed by `eta` vary. This is the quantifier order needed below.

## Relation orientation and reversal

`QuittingPunishmentFloorAdmissibleEdge` in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`
has fields `tail`, `current`, and

```text
IsQuittingNashBellmanEdge reward current.value tail.value.
```

The relation source is `edge.tail` and target is `edge.current`. Thus a path

```text
s_0 --e_0--> s_1 --e_1--> ... --e_(K-1)--> s_K
```

has forward payoff recursion from `v_t` to `v_(t+1)` using the root stored at
`s_(t+1)`. Decoding it and applying
`quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock` in
`UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean` uses
`n=K-1` and reverses the roots in the intended order. All nonclosing Bellman
seams are exact. The only wrap seam uses the first forward root and the
payoff difference `v_0-v_K`; it never compares the stored roots of `s_0` and
`s_K`.

This also confirms Corollary 35A's prepend orientation. A path from
`e.current` to `z_eta`, preceded by `e`, is a path from `e.tail` to `z_eta`.
Even a nil return path causes no boundary failure: after prepending `e`, the
combined path has one edge.

## Charge and error accounting

For edge charges `q_t` and whole-block absorption

```text
A = 1 - product_t (1-q_t),
```

literal absorption gives `0<=q_t<=1`. If one `q_j>=c`, then

```text
product_t (1-q_t) <= 1-q_j,
A >= q_j >= c.
```

For desired lasso error `delta>0`, choose endpoint error `eta=delta*c` and
split

```text
supportError = delta*(1-c),
seamError    = delta*c.
```

These are nonnegative and sum to `delta`. Exact endpoint Nash on every edge
supplies support error zero and hence `supportError`; floor admissibility
supplies the rationality field at error zero. Endpoint payoff closeness gives
the raw seam bound, and

```text
seamError = delta*c <= delta*A
          = (supportError+seamError)*A
```

is exactly the normalized closing condition. The case `c=1` is sound:
`supportError=0`, the charged edge forces `A=1`, and the full error is assigned
to the seam. The one-edge case is also sound.

The lasso's entering values are the decoded states `s_1,...,s_K`, all of
which satisfy the punishment floor. No unused floor hypothesis on `s_0` is
being substituted for one of these values. Positive charge supplies an
absorbing phase. Finally,
`quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos`
in
`UniformEquilibrium/Quitting/Projective/SingleSeamProjectiveLasso.lean`
is the all-errors consumer and reaches unrestricted behavioral deviations and
one fixed payoff target. It does not require the approximate paths themselves
to select a common endpoint.

## Proposition 36

The checked proof of
`exists_uniformEquilibriumPayoff_of_finiteSupportRankExitConsumers` in
`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`
uses the paid consumer only after the paid branch has supplied exactly the
frontier/mover/endpoint/separation/observer/gain/eventual-row tuple appearing
in `PaidFirstDisagreementAdmissibleReturnConsumer`. Replacing the result in
that branch by the fixed edge plus the payoff-closure family lets Corollary
35A produce a uniform payoff immediately. This contradicts the same `hno`
used by the checked four-way proof. The positive-slope, support-entry, and
circulation branches are untouched.

Therefore Proposition 36 is a valid weakening of the paid branch's *output
interface*. It is not a producer from a paid row: neither Proposition 35 nor
36 proves the required payoff reachability from `edge.current`.

## Falsification attempts

- `c=1`: valid as above; there is no negative support budget.
- one edge and no additional return edge: valid when its endpoint payoff is
  close to its tail payoff; the reversed lasso has one phase.
- endpoint states with unrelated stored simplex roots: harmless because only
  decoded payoffs enter the wrap seam.
- paths of unbounded and accuracy-dependent length: harmless because each
  requested lasso is finite and the all-errors consumer performs the final
  fixed-target selection.
- charge floors `c_eta` tending to zero: the proof would only give seam ratio
  `eta/c_eta`; this correctly lies outside the proposition.

I found no mathematical counterexample.

## Lean-status correction from the refreshed tree

The refreshed tree now contains
`quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns`
in
`UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`, which
is an attempted direct formal packaging of Proposition 35. It is not imported
by another Lean file in the refreshed tree. More importantly, my narrow check

```text
lake env lean UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean
```

failed at the proof of `exists_absorptionStage_of_highChargeCount_pos` with a
dependent-type mismatch around `Nat.succ_lt_succ htime`. I did not edit that
file. Consequently this review validates the ordinary argument and its use of
already checked consumers, but does **not** certify the new packaging as a
proved or integrated Lean declaration. Proposition 36 remains ordinary
mathematics only.

## Verdict

Proposition 35, Corollary 35A, and Proposition 36 are valid ordinary
mathematics. The first two give a genuine conjecture-facing relaxation from
full-state exact return to uniformly charged payoff near-return; Proposition
36 correctly substitutes this relaxation in the paid arm of the four-exit
argument. The hard source producer is unchanged, and the current attempted
Lean wrapper failed the narrow check described above.
