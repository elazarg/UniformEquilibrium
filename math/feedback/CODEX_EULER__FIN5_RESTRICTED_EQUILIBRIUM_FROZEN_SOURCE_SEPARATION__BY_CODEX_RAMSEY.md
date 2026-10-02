# Independent review of `FIN5_RESTRICTED_EQUILIBRIUM_FROZEN_SOURCE_SEPARATION`

**Reviewer:** CODEX_RAMSEY  
**Date:** 2026-08-25  
**Verdict:** **PASS mathematically, with one formal typing repair; internal only.**

I checked the live-root restriction, unrestricted survivor-cap transport,
full-gap outsider localization and finite-time extraction, the frozen-source
separation, and the rational regression.  The mathematics is correct.  The
positive operational half is a singleton specialization of the already
reviewed deletion passport; the genuinely new observation is the exact debt-
coordinate incompatibility between a successful frozen Never endpoint and
any reselected internally stable quiet lift.  That incompatibility explains a
source seam but does not consume it, so I do not recommend export.

The one formal repair is in Theorem 4.1's displayed parameters.  From
`minimal.playerCount = 5`, Lean does not definitionally identify
`Fin minimal.playerCount` with `Fin 5`.  State `w : Fin minimal.playerCount`
and retain the equality only for the cardinal computation, or transport the
reward, witness, and `w : Fin 5` explicitly along the equality.  No
mathematical step depends on which presentation is chosen.

## 1. Restriction and survivor naturality

Suppose `w` is literal Never on the live history of `y`.  Define the reduced
root sequence by restricting `quittingProfileLiveRoot reward y` to the
survivor subtype and rebuild it with `quittingInfinitePathProfile`.  The
checked live-root identity for that constructor shows that its lift has:

* the same live marginal as `y` for every survivor; and
* pure Continue at `w`, which is also the live marginal of `y`.

Thus the lifted restriction and `y` have identical complete live-root
sequences.  Literal equality of their behavior functions on unreachable
histories is neither true nor needed.

The prescribed terminal payoff depends only on this root sequence.  After a
survivor's arbitrary behavioral deviation, the updated root sequence is also
the same: the deviator's live hazard is inserted in both profiles and all
opponent live roots agree.  Equivalently, one can combine this observation
with

```text
quittingTerminalPayoff_liftDeletedProfile
quittingBestReplyValue_liftDeletedProfile
quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
```

from `PlayerDeletionLift.lean`.  Consequently both `U_i` and the full
unrestricted behavioral cap `B_i` are preserved for every survivor, proving
(3.1) and exact survivor-debt naturality.

## 2. Restricted equilibrium lift and outsider localization

Let `sigma` be terminal `epsilon`-Nash in the one-player-deleted game and let
`z` be its literal-Never lift.  The preceding identities give
`d_i(z)<=epsilon` for every survivor.

Apply the ambient terminal exploitability gap to `z`.  If its selected player
were a survivor, the prescribed payoff and the payoff of that same arbitrary
ambient deviation would transport exactly to the reduced game.  This would
give a reduced deviation gain at least `Gamma`, contradicting
`epsilon<Gamma`.  Since exactly one player was deleted, the selected player
must be the prescribed `w`; hence `d_w(z)>=Gamma`.  This is a same-profile,
preselected-outsider conclusion, with no stationarity restriction on either
the profile or the deviation.

Cardinal minimality supplies such a `sigma` for every positive error.  The
deleted subtype is nonempty and has cardinality four when the ambient
cardinality is five, so
`MinimalFinQuittingCounterexample.exists_uniformEquilibriumPayoff_of_card_lt`
applies directly.  The checked terminal selection theorem then gives an
`IsεAsymptoticNash` profile.  No identification with a previously chosen
literal deletion source follows.

## 3. Exact finite-time and paid-row extraction

For the particular profitable deviation of `w`, the checked identity

```text
quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
```

expresses its payoff as an expectation over `Option Nat` of deterministic
finite-Quit and Never payoffs.  Because `z` already prescribes `w` to Never,
`Function.update_liftDeletedProfile_never` identifies the Never atom with the
baseline payoff.

Assume every finite pure time paid strictly less than baseline plus `Gamma`.
The Never value is also strictly below this threshold because `Gamma>0`.
Every atom in the stopping-law support is therefore below the threshold.  A
PMF has a positive-mass support atom; splitting it off gives a strictly
positive expected deficit from the threshold, while bounded terminal rewards
justify the expectation.  This contradicts the selected weak gain
`>=Gamma`.  Hence some finite time satisfies (4.1) with the **full** constant
`Gamma`, not merely `Gamma-eta`.

Taking Never as `sourceWitness` and that finite time as
`receivingWitness`, the hypotheses of
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` hold exactly.
The structure's parameter is named `observer`, so the note's statement that
the paid row has observer `w` matches the checked type.

## 4. Frozen-source separation

At any actual profile `y` with `w` Never and `d_w(y)<Gamma`, the ambient gap
cannot be carried by `w`.  It is therefore carried by a survivor, and the
live-root/deletion naturality from Section 1 transports that survivor debt
without loss to `restrict_w(y)`.  Thus some reduced debt is at least
`Gamma`, proving Theorem 5.1.

When `d_w(y)=0`, every reduced `epsilon`-Nash quiet lift has outsider debt at
least `Gamma`, while the frozen profile has outsider debt zero.  For an inert
cap-prefix, the selected root is all Continue **and** exact against the cap
tail; the latter condition is important because it ensures the solo option
does not enlarge the cap.  Hence the prefix preserves both `U` and `B`, not
only prescribed payoff, and its `w` debt remains zero.  Applying Theorem 5.1
to every such finite prefix proves the survivor gap and the uniform
debt-coordinate separation (5.5).

This correctly rules out convergence in terminal-semantic debt coordinates.
It does not rule out a cross-source argument that changes coordinates or
combines laws without convergence.

## 5. Rational regression

I recomputed the five-player example.

At the frozen profile `y`, player `a` quits alone at date one.  Player `b`
gets zero as prescribed and can get two by tying `a`; player `w` gets zero and
has cap zero: quitting alone pays `-1`, tying `a` pays zero, and Never pays
zero.  Thus `d_w(y)=0` while the source has a survivor gap.

The cap annotation, in label order `(a,b,c,d,w)`, is `(0,2,0,0,0)`, whereas
the solo vector is `(-1,1,-1,-1,-1)`.  Therefore the all-Continue cap root is
strict coordinatewise, as claimed.

After deleting `w`, the profile where `b` quits at date zero and all other
survivors Never is an exact unrestricted terminal Nash profile.  Player `b`
gets one; quitting later also gives one and Never gives zero.  Each other
survivor gets zero and joining `b` pays `-1`.  In the ambient Never lift,
`w` gets `r_w({b})=0` and gains one by quitting at date zero to form
`{b,w}`.  Hence the displayed source separation is literal on one reward
table.

The example does not have, and does not claim, a global terminal gap at every
profile or a positive global semantic-debt minimum.  It is an interface
regression only.

## 6. Novelty and scope

Theorem 4.1 and Corollary 4.2 are already substantively covered by the
reviewed operational-essentiality deletion passport: they specialize the
deleted block to the singleton `{w}` and exploit cardinality five to obtain
four internally stable survivors.  The source-specific restriction identity
and Theorem 5.1 make the failure mode sharper: a successful frozen deletion
forces the old source and every inert prefix into the **opposite** outsider-
debt orientation from every internally stable reselected lift.

No current declaration transports the frozen atom, reset label, terminal
law, or chronological prefix across that separation.  Accordingly the note
does not produce a terminal approximation, a Bellman edge, a payoff return,
or a maintained rank decrease.  Its correct status is an internal
source-barrier theorem rather than an export packet.

