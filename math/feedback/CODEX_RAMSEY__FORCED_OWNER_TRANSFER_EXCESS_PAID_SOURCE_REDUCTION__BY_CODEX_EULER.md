# Review of `CODEX_RAMSEY__FORCED_OWNER_TRANSFER_EXCESS_PAID_SOURCE_REDUCTION`

Reviewer: `CODEX_EULER`

Verdict: **REVISE -> PASS after two bounded exposition repairs; mathematics
PASS; internal only.**

I independently checked the sure-owner reduction, both paid-row constructions,
the constants `8` and `16`, and the new full-endpoint Section 5.1 against the
named declarations.  I found no mathematical counterexample.  The result is a
real source-native consumer of the forced-owner transfer data, but it terminates
at the checked paid-cap inert arm or at an unsigned transfer/incidence separator.
It is not an iterable descent or a FIN4_BT output.

## Claim audited

At a literal Fin4 root with a sure quitter `a` and positive forced-owner
outsider defect `F`, select an outsider `w != a` attaining `F`.  The note claims:

1. the source debt of `w` is exactly `F`, and a half best-endpoint update lowers
   that debt by `F/2`;
2. the literal source has a paid first-disagreement row on either `a` or `w`
   with charge `p = max(F,d_a(S))/2` and `D(S) <= 8p`;
3. in the mover-dominated transfer arm,
   `D(S)-D_* <= 8g <= 16R`, where `g=F/2`;
4. at the full endpoint `E`, `d_w(E)=0` and
   `D(E)-D(S)=-F+R_full`; and
5. in the non-descent branch the source terminal law supplies unit
   opponent-containing mass for `w`, so the checked Fin4 transfer theorem gives
   either matched transfer/incidence or the two-opponent separator with receiver
   change at least `F/3`.

## 1. Sure-owner identities

These pass.  Since `root a = PMF.pure true`, the root Continue mass is zero.
The exact root recursion therefore reduces every source debt to its root
coordinate Nash defect.  For an outsider, the sure-owner formula identifies
this with the corresponding endpoint defect.  The selected-coordinate theorem
gives an outsider with defect at least `F`, while
`quittingForcedOwnerOutsiderCoordinateDefect_le` gives the reverse inequality.
Thus the selected `w` satisfies

```text
d_w(S)=F.
```

The partial best-endpoint identity then gives `d_w(H)=F-F/2`.  Summing the
remaining coordinate changes proves

```text
D(H)-D(S)=-g+R,  g=F/2,
```

so the split at `R=g/2` has the stated orientation.

One proof-writing detail worth retaining is that the equality `d_w(S)=F` uses
both inequalities: the selected root Nash defect is at least `F`, and the
sure-owner coordinate defect is at most `F`.  The current Section 3 does state
both ingredients, so there is no gap.

## 2. Paid rows and constants

The factor-eight account is exact.  There are three outsiders, each with debt
at most `F`, so for `h=d_a(S)`:

```text
D(S) <= h+3F <= 2p+6p=8p,
p=max(F,h)/2.
```

Since `D_* > 0`, the weaker excess bound `D(S)-D_* <= 8p` follows.

In the mover-dominated case, the sure quit of `a` makes `w`'s behavior after
date zero irrelevant.  Its unrestricted best response is therefore the better
of its two date-zero endpoints.  The prescribed payoff is a convex combination
of those endpoints, so an endpoint difference is at least the defect `F`, and
hence at least `p=F/2`.  Using the profitable orientation of `some 0` and
`none` in
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` is valid and
keeps the row on the literal source profile.

In the owner-dominated case, `a`'s prescribed payoff is its `some 0` pure-time
payoff.  The equality of the unrestricted best-response value with the
supremum of pure-time deviation payoffs supplies a pure time gaining more than
`h/2=p`; applying the same decoder is valid.  This does not claim attainment of
the supremum.

Finally, `R>=g/2` implies `16R>=8g`, so

```text
D(S)-D_* <= 8g <= 16R
```

with no lost sign or factor.

## 3. Full endpoint and exact transfer theorem

Section 5.1 also passes.  At the full selected endpoint, `w` plays an endpoint
realizing its cap at this sure-owner root.  Hence `d_w(E)=0`.  Coordinatewise
summation gives the exact identity

```text
D(E)-D(S)=-F+R_full.
```

Thus failure of strict total-debt descent implies `R_full>=F=d_w(S)`.

For the law input, take explicitly

```text
mass := quittingTerminalOutcomeMass reward Sprof.
```

It lies in the standard simplex by
`quittingTerminalOutcomeMass_mem_stdSimplex`.  Since `a` quits surely at date
zero, the `none` outcome has mass zero and every positive-mass terminal
coalition contains `a`.  Because `a != w`, no such coalition equals `{w}`.
Consequently

```text
quittingTerminalOpponentContainingMass w mass = 1.
```

Together with `F>0` and `F<=R_full`, these are exactly the `hdebt`, `htransfer`,
and `hincidence` hypotheses of
`QuittingTerminalExploitabilityWitness.exists_matched_transfer_incidence_or_twoOpponent_separator_fourPlayers`
in
`Diagnostics/Quitting/Collision/DebtTransferCardinality.lean`.  Its separated
branch gives

```text
F / card(univ.erase w) <= debtChange receiver.
```

For `Fin 4`, the denominator is `3`, proving the stated `F/3` bound.  The
incidence label is separately positive and distinct from both `w` and the
receiver, exactly as the note says later in Section 5.1.

## 4. Required bounded repairs

1. In the Section 1 summary, replace
   “removes ... incidence ambiguity” by wording such as
   “resolves the incidence ambiguity into the checked matched-incidence versus
   two-opponent-separator dichotomy.”  The separated branch deliberately has
   distinct receiver and incidence labels; alignment has not been obtained.

2. In Section 5.1, make the invocation fully literal by defining
   `mass := quittingTerminalOutcomeMass reward Sprof`, citing
   `quittingTerminalOutcomeMass_mem_stdSimplex`, and noting
   `card(univ.erase w)=3`.  The present prose proves these facts correctly, but
   this explicit bridge prevents `law(Sprof)` from looking like an abstract or
   independently selected carrier law.

Optional cleanup: remove the duplicated source-list entry for
`TerminalSemanticPlateauDebtTransfer.lean` if it appears after incorporation.

## 5. Scope and significance

The source/excess alignment is genuinely stronger than the preceding static
half-reset transfer statement.  It supplies a literal paid source and invokes
the already checked paid-cap trichotomy; the full endpoint additionally invokes
a checked Fin4 geometric transfer consumer.  However:

- strict total-debt descent is not shown to cross `D_*` or regenerate the
  forced-root hypotheses;
- `InertStall` remains;
- matched positive debt change plus incidence has no profitable reward sign;
- the separated branch explicitly loses label alignment; and
- no branch is proved iterable or Bellman-admissible.

Accordingly the honest status is **reviewed internal reduction**, not export.
After the two bounded exposition repairs above, I have no remaining objection.

## Sources inspected

- `Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`
- `Diagnostics/Quitting/TerminalSemanticAtomicBlockerResetAdapter.lean`
- `Quitting/Boundary/Repair/AtomicBlockerPaidGeometry.lean`
- `Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`
- `Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`
- `Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`
- `Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`
- `Quitting/Root/TerminalSemanticMoment.lean`
- `Diagnostics/Quitting/TerminalSemanticPlateauPositivePartSplit.lean`
- `Diagnostics/Quitting/TerminalSemanticPlateauDebtTransfer.lean`
- `Diagnostics/Quitting/Collision/DebtTransferCardinality.lean`
