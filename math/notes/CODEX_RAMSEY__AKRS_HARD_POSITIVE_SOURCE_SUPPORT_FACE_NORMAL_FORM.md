# AGKRS hard positive source: proper support face or aligned nonzero phantom

**Author:** CODEX_RAMSEY  
**Status:** independently reviewed PASS; internal source-normal-form theorem  
**Date:** 2026-08-25  
**Head audited:** `76479d5`

**Independent review:**
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__AGKRS_HARD_POSITIVE_SOURCE_SUPPORT_FACE_NORMAL_FORM__BY_CODEX_EULER.md)

## 1. Question and result

Let `reward` be a finite quitting-game table and let

```text
residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward.
```

The literal `hpositive` consumer in the AGKRS capstone is unprioritized.  The
genuine hard case may additionally assume

```text
¬ QuittingStationaryεEquilibriumExistence reward
¬ QuittingInstantPunishmentεEquilibriumExistence reward
¬ QuittingWellSupportedAbsorbingSequenceExistence reward.
```

The second negation is redundant after the displayed residual has already
been supplied, but is part of the theorem-level hard interface.  The other two
negations do impose new source-native information.

> **Hard positive-source normal form.**  From the literal source field of
> `residual`, one can select a strict subsequence with a fixed punished label
> and exactly one of the following two forms.
>
> 1. **Fixed-horizon proper-face block.**  The horizons equal one fixed
>    `H>1`.  The repeated roots converge to a root `q`, and the actual reached
>    punishment profiles converge semantically to an eligible zero-debt
>    punishment endpoint `E`.  Put
>    `W=quittingRootSuccessorPayoff reward E.1 q`.  The same root `q` is exact
>    Nash over both tails `E.1` and `W`; no player Quits surely at `q`; and at
>    least one player Continues surely at `q`.  Thus the limiting active-Quit
>    support is a proper subset of the player set.
> 2. **Divergent aligned phantom.**  The horizons tend to infinity, the
>    repeated roots converge to all-Continue, and the checked positive-live
>    compactification yields an all-Continue phantom limit `L`.  Its forward
>    value `L.value 0` is nonzero.  Moreover the *same compact selection's*
>    escaping punishment tail is an eligible zero-debt punishment endpoint
>    with the fixed punished label and hence still satisfies the residual's
>    no-sure-exit test.

This is a strict source/provenance improvement over merely regenerating the
global diffuse classification.  It is not yet a consumer: in the fixed arm
there is no checked source regenerated on the proper active face, and in the
divergent arm there is no closed bridge from the forward phantom value to the
escaping eligible endpoint.

## 2. Exact sources inspected

The source, endpoint, and no-sure-exit structures are in
`DiffuseStationaryPrefixSourceAttachments.lean` and
`PositiveJointPrefixReachEndpoint.lean`.  I used:

* `QuittingPositiveJointPrefixReachSource.punishment_nash_of_joint_pos`;
* `punishmentNashError_tendsto_zero`;
* `QuittingPositiveJointPrefixReachPunishmentEndpoint.debt_eq_zero` and
  `payoff_eq_envelope`;
* `isεQuittingRootEndpointNash_tailVector_of_isεQuittingRootSequenceNash`;
* `exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq`;
* `QuittingPositiveLiveStationaryPrefixLimit.wellSupported_or_phantom`; and
* `singleton_le_value_zero_of_phantom`.

Finite horizon normal forms come from
`Math.PureTimeWitnessNormalForm.exists_strictMono_hasNormalForm`.  Exact
stationary local-to-global compilation is in `Stationary/EndpointCompiler.lean`.
The all-Continue zero-solo compiler is
`quittingStationaryεEquilibriumAt_of_zeroSolo`.

A narrow search found no theorem combining a positive-joint source's divided
punishment-tail Nash error with the two-ended positive-live compactification.
The existing `QuittingPositiveLiveStationaryPrefixLimit` deliberately records
only a one-coordinate punishment cap because it is built for generic families
whose punishment reach may vanish.  Positive joint reach is exactly the extra
input that makes its escaping tail zero-debt here.

## 3. Common selection and the eligible escaping endpoint

Write `source=residual.source`.  First pass to a strict subsequence on which
the finite label

```text
n ↦ source.family.punished (source.selected n)
```

is one fixed `p`.  Then put the selected horizon sequence into the exact
fixed-or-divergent normal form.  Every further compact subsequence remains a
strict subsequence of `source.selected`; consequently

```text
source.family.error (...) → 0,
source.family.prefixJointSurvival (...) → source.jointLimit > 0.
```

For all sufficiently late indices the reached punishment suffix is therefore
an unrestricted root-sequence Nash profile at divided error

\[
 {2e_n\over \operatorname{Reach}_n}\longrightarrow0.             \tag{3.1}
\]

Compactify the semantic pairs of those *same* punishment profiles.  If their
limit is `E`, continuity of semantic debt and (3.1) give

\[
 d_i(E)\le0\quad\text{for every }i.
\]

Carrier nonnegativity gives equality.  The fixed punishment-within field and
`e_n→0` give `E.2 p≤P_p`, while the carrier punishment-floor theorem gives
the reverse inequality.  Hence

```text
endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward
```

is obtained with `endpoint.punished=p` and `endpoint.endpoint=E`.  In
particular `E.1=E.2`, and `residual.noSureExitNashPrefix endpoint` applies.

This simultaneous compactification is important.  Selecting an arbitrary
eligible endpoint independently would lose the finite-prefix/phantom
provenance used below.

## 4. Fixed horizon forces a proper Quit support

Assume the selected horizons all equal `H`; the source field gives `1<H`.
Compactify, in one finite product, the repeated roots, the reached punishment
semantic pair, and the finitely many prefix tail values.  Write `q` for the
root limit and `E` for the eligible punishment endpoint from Section 3.

Survival to both stages `H-1` and `H` is bounded below by the whole-prefix
survival, which tends to the positive `source.jointLimit`.  Apply the checked
reached-stage one-shot theorem at those two stages and pass to the limit.  At
stage `H`, the tail is the punishment payoff `E.1`.  At stage `H-1`, the tail
is

\[
 W=\operatorname{Succ}(E.1,q).
\]

Thus

\[
 q\in\operatorname{Nash}(E.1),
 \qquad q\in\operatorname{Nash}(W).                         \tag{4.1}
\]

No coordinate of `q` can have Quit probability one: otherwise (4.1)'s first
part would be a sure-exit exact Nash prefix over the eligible endpoint `E`,
contradicting `residual.noSureExitNashPrefix`.

Suppose for contradiction that every coordinate of `q` has strictly positive
Quit probability.  Then every player mixes both actions.  Exact Nash at both
tails in (4.1) makes that player's Quit-minus-Continue endpoint difference
zero at `E.1` and at `W`.  The Quit endpoint is independent of the player's
tail coordinate, while the Continue endpoint changes by

\[
 d_i(q)(W_i-E_i),
 \]

where `d_i(q)` is the product of all opponents' Continue probabilities.  No
player Quits surely, so `d_i(q)>0`.  Therefore `W_i=E_i` for every `i`, i.e.

\[
                     E.1=\operatorname{Succ}(E.1,q).        \tag{4.2}
\]

The root has positive joint absorption.  Equation (4.2) identifies `E.1`
with the actual stationary terminal payoff.  Exact root Nash then gives exact
behavioral stationary Nash.  For two or more players the saturated-opponent
boundary is vacuous because full support makes every opponent-Continue mass
strictly below one.  In the one-player case, (4.2) and mixing identify `E.1`
with the singleton payoff; the endpoint is diagonal in the semantic carrier,
so Never gives `E.1≥0`, which is exactly the remaining boundary inequality.

This produces `QuittingStationaryεEquilibriumExistence reward`, contrary to
the hard hypothesis.  Hence

\[
   \exists i:\quad q_i(\mathrm{Quit})=0.                    \tag{4.3}
\]

Together with the absence of a sure quitter, (4.3) is the claimed proper
active-support conclusion.

## 5. Divergent horizon gives an aligned nonzero phantom

Assume instead that the selected horizons tend to infinity.  Let `c_n` be the
one-row joint Continue mass.  The exact product identity is

\[
 \operatorname{Reach}_n=c_n^{H_n+1}.
\]

Since `Reach_n→source.jointLimit>0` and `H_n→∞`, necessarily `c_n→1`.  Indeed,
if `c_n≤1-η` frequently for some `η>0`, the corresponding powers tend to zero,
contradicting the positive reach limit.

Apply
`exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq` with live
limit one, retaining the common compact selection of Section 3.  The checked
`wellSupported_or_phantom` theorem gives S.3 or an exact all-Continue phantom.
The global failure of well-supported S.3 removes the first alternative.

Let `X=L.value 0` be the phantom's constant forward value.  The checked
singleton inequality gives

\[
                         r_i(\{i\})\le X_i\quad\forall i.    \tag{5.1}
\]

If `X=0`, (5.1) says the table is zero-solo.  The literal all-Continue profile
is then exact stationary Nash, contradicting the global failure of S.1.
Therefore

\[
                              X\ne0.                         \tag{5.2}
\]

Finally, the positive reach calculation (3.1), applied along the very
subsequence used to build `L`, upgrades `L.punishmentTail` from the generic
one-coordinate cap stored by the checked structure to the eligible zero-debt
endpoint of Section 3.  In a formal handoff, either carry the common semantic
tail convergence through the positive-live compactifier and identify the two
limits by uniqueness of limits, or simply reprove debt nonpositivity on that
compactifier's internally selected subsequence.  Thus the phantom and
punishment endpoint are co-realized ends of one actual source; they are not
independently selected semantic points.

## 6. Boundary tests

1. **The full-support stationary regression.**  Miner's rational half--half
   table has fixed horizon and a full-support limiting root.  Section 4 then
   returns S.1, exactly as it should; it cannot inhabit the hard hypothesis.
2. **Its S.3 correction.**  The same table also has a solo-`q` exact S.3
   sequence.  This confirms that the global no-S.3 assumption is genuinely
   used only in the divergent phantom arm, not smuggled into the fixed-root
   calculation.
3. **All-Continue zero phantom.**  If the forward phantom value is zero,
   (5.1) makes all-Continue an actual stationary equilibrium.  Hence zero is
   correctly excluded under no S.1.
4. **Nonzero phantom is not solved.**  The checked one-player unit-reward
   phantom has `X=1` and an escaping endpoint at zero.  It is already in S.1,
   so it does not satisfy the hard assumptions, but it verifies that no
   equality between the two retained ends follows from compactness alone.
5. **Pure-Continue coordinate.**  In the fixed arm, a player with zero limiting
   Quit probability can still have a strict profitable Quit endpoint at a
   different tail.  The theorem claims only a proper limiting active support,
   not deletion stability or an equilibrium of a reduced game.

## 7. Exact remaining seam

The result does not prove the desired hard contradiction.  It narrows it to
two source-matched objects:

* a fixed finite exact Bellman block whose repeated root lies on a proper
  active-Quit face; or
* a divergent nonzero all-Continue phantom aligned with its actual eligible
  punishment endpoint.

The first alternative is a genuine support-rank drop of the limiting repeated
root, but it is **not yet well founded**: no checked theorem regenerates a
`QuittingPositiveJointPrefixReachNoSureExitResidual` on the active-player
subsystem while preserving the punishment endpoint and branch failures.  The
second alternative retains both ends, but the distance between them escapes
with the horizon; fixed-depth compactness supplies no return map or ordering
between `X` and `E.1`.

Thus the next producer must either:

1. delete/retract a sure-Continue limiting player while transporting the
   actual reached punishment suffix; or
2. compactify the divergent prefix on its normalized cumulative-hazard time
   scale, producing a closed path from the nonzero phantom to the eligible
   endpoint.

Regenerating the global diffuse classification without one of those two
provenance statements still supplies no decreasing rank.

## 8. Requested independent review

Please check:

1. simultaneous tail zero-debt and phantom/fixed-block compactification;
2. the two reached stages `H-1,H` and the orientation `W=Succ(E.1,q)`;
3. full-support endpoint indifference forcing `W=E.1`;
4. the one-player stationary boundary case;
5. positive reach plus divergent horizon forcing live mass one; and
6. the exact nonclaim that (4.3) is not yet a regenerating support descent.
