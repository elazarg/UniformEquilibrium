# Independent review of the minimum-return strong singleton packet

Reviewer: `STRENGTHENER`

## Verdict

**PASS mathematically after one terminology/API correction, but do not export
this result as a separate conjecture-facing packet.**  The moving packet exists, its
collision tail cluster is forced onto the global minimum-debt fibre, and the
constants

\[
\sum_{i\ne o}\delta_i\ge \frac{\lambda D_*}{2},
\qquad
\delta_p\ge \frac{\lambda D_*}{6},
\qquad
g_p\ge \frac{\lambda^2D_*}{6}
\]

are correct for `Fin 4`.  The fixed auxiliary owner and fixed Boolean action
must be selected in the order described by the first review.  I independently
checked that repair.

The profile used in the proof is not literally
`quittingSelfTailClosure reward endpoint.targetProfile endpoint.stage`.
That standard closure restarts `endpoint.targetProfile` itself, whose debt is
not known to approach the minimum.  The needed profile is the **cross-tail
literal root-stack profile** obtained by copying the live roots of
`endpoint.targetProfile` through the marked date and then attaching
`endpoint.referenceProfile`.  The generic literal-root-stack identities prove
the same stage-mass preservation and make the `mark + 1` spine literally the
reference profile.  With this wording correction, there is no mathematical
gap.

The maximal honest conclusion of this construction is

\[
\boxed{
\text{strategic singleton packet}
\quad\lor\quad
\text{minimum-fibre collision packet with fixed positive other defect}.}
\]

It eliminates the off-minimum tail-cluster arm for the newly constructed
packet.  It does not consume the remaining collision packet or imply that its
whole source profile is near the minimum fibre.

After this audit, I compared the result with
`EXTERNAL__WEAK_CORE_FORCED_PAIR_COLLISION_NORMAL_FORM` and both reviews of
that note.  Its cofinal hard-residual theorem strictly subsumes the present
conjecture-facing use: it first pureifies to `{j}`, chooses one table-level
full-gap outsider valid at every rank, and therefore forces Quit and the fixed
pair `{j,o}` without an action subsequence.  It uses the same corrected
cross-tail splice, obtains the same minimum-return conclusion, and derives the
same `lambda^2 * D_* / 6` transfer.  The present theorem remains a valid generic
moving-packet lemma when no full-gap forced outsider is available, but that
extra generality is not a new Fin4 frontier contraction and should remain in
notes/feedback rather than duplicate the forced-pair export.

## Exact statement checked

Let `source : FinFourMinimumAtomProducer reward bound` have selected law atom
`{j}` of mass

\[
\mu=\texttt{source.point.2 (some source.atom.terminal)}>0.
\]

Fix any

\[
0<\lambda<\mu.
\]

Using one chronology supplied by
`FinFourMinimumAtomProducer.exists_commonChronology_cofinal_ownerCompressedSingleton`,
choose for each requested depth `n` an endpoint `e_n` of rank `k_n >= n`.
Set

\[
\sigma_n=e_n.\texttt{referenceProfile},\qquad t_n=e_n.\texttt{stage}.
\]

There is a family of actual profiles carrying, after passage to one strictly
monotone subsequence:

1. one fixed auxiliary owner `o != j`;
2. one fixed Boolean endpoint action `a` for `o`;
3. one fixed routed terminal, `{j}` if `a = Continue` and `{j,o}` if
   `a = Quit`;
4. marked stage mass strictly greater than `lambda`;
5. marked root-coordinate defect exactly zero for `o`; and
6. a literal post-mark continuation equal to `sigma_n`.

With any positive scale tending to zero these data form a
`QuittingReprojectionConcentratedPacket`.  Applying
`concentratedPacket_singletonStrategic_or_collisionMinimumResidual` gives
either its strategic singleton output or a collision residual whose tail
cluster has total debt exactly `D_*`.

In the collision arm, after a further subsequence, one fixed `p != o` has

\[
\delta_p\ge \lambda D_*/6,
\]

and its exact one-date best-endpoint update has actual payoff gain at least
`lambda^2 * D_* / 6`.  Its unrestricted behavioral cap is unchanged and its
terminal semantic debt therefore decreases by exactly this gain.

## Construction and provenance audit

### Cofinal minimum source

The selected endpoint rank need not be strictly monotone.  Its field
`depth_le_rank` gives `n <= k_n`, hence `k_n -> infinity`.  Composing this with
`FinFourMinimumAtomChronology.prefix_debt_tendsto` yields

\[
D(\sigma_n)\longrightarrow D_*.
\]

For arbitrary `lambda < mu`, the construction should call
`FinFourMinimumAtomChronology.nonempty_ownerCompressedSingleton` (or the
common-chronology theorem) directly.  The structure field
`FinFourOwnerCompressedSingletonProducer.cofinal_endpoint` exposes only the
canonical scale `mu^2/8`; it is insufficient by itself for the arbitrary
`lambda` statement.  This is an API distinction, not a mathematical loss.

### Cross-tail closure

Let `roots_n` be the list of actual live roots of `e_n.targetProfile` at dates
`0,...,t_n`, and define

\[
\widehat\sigma_n
=\texttt{quittingLiteralRootStackProfile reward roots_n sigma_n}.
\]

The literal-root-stack get-element identity shows that every root through
`t_n` is copied.  Therefore

\[
\Pr_{\widehat\sigma_n}(\{j\}\text{ at }t_n)
=
\Pr_{e_n.\mathrm{targetProfile}}(\{j\}\text{ at }t_n)
>\lambda.
\]

The stack length is `t_n + 1`, and
`quittingAllContinueProfileSpine_literalRootStackProfile_length` gives the
literal identity

\[
\operatorname{spine}_{t_n+1}(\widehat\sigma_n)=\sigma_n.
\]

This is the exact source provenance needed by the collision consumer.
Calling it a “self-tail closure” is harmless informally only if the displayed
formula is kept; the existing named `quittingSelfTailClosure` attaches its
first profile argument as tail and must not be invoked with the compressed
target here.

### Fixed owner and fixed action

Choose any fixed `o != j`; no player pigeonhole is needed.  Apply
`QuittingStageAtomConcentratedPacketAdapter` to `widehatSigma_n`, terminal
`{j}`, owner `o`, date `t_n`, and resolution `lambda`.  The precondition
`{j} != {o}` follows from `o != j`.

Its checked fields give lossless routing, exact post-date tail preservation,
and zero marked defect for `o`.  The routed terminal depends on the Boolean
best action.  An infinite Boolean sequence has a strictly monotone constant
subsequence.  Restricting the whole family to it fixes the terminal and makes
all dependent packet indices well-typed.  Any subsequent cluster subsequence
composes with this strict subsequence and retains `D(sigma_n) -> D_*`.

### Tail cluster

The residual's `tail_tendsto` is exactly convergence of the semantic pairs at
the `mark + 1` spines.  By the cross-tail identity these are semantic pairs of
the corresponding `sigma_n`.  Continuity of total debt gives

\[
D(\texttt{cluster})=D_*.
\]

Thus the strict escape disjunct in
`QuittingConcentratedCollisionMinimumResidual.escape_or_otherDefect` is
impossible; its equality-plus-other-defect arm is forced.

## Quantitative audit

The residual sum is over `Finset.univ.erase o`, which has exactly three
members on `Fin 4`.  Coordinate root defects are nonnegative, so infinitely
often one member carries at least one third of the sum.  After freezing that
member,

\[
\delta_p\ge \frac{1}{3}\frac{\lambda D_*}{2}
=\frac{\lambda D_*}{6}.
\]

The row live mass is at least the displayed coalition stage mass, which is
strictly greater than `lambda`.  The exact stage-best-endpoint identity gives

\[
g_p=L\delta_p\ge\frac{\lambda^2D_*}{6}.
\]

Only `p`'s strategy changes, so the all-behavior cap for `p` is exactly
unchanged.  The checked identity
`quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` therefore gives
exact own-debt subtraction.  This is not a claim about total debt because
other players' caps can rise.

The arbitrary-scale version is quantitatively stronger than using only the
canonical atlas resolution.  For every `theta in (0,1)`, choosing
`lambda = theta * mu` gives gain at least

\[
\frac{\theta^2\mu^2D_*}{6}.
\]

Thus gains can be made arbitrarily close to `mu^2 * D_* / 6`.  Equality at
`lambda = mu` is not justified: clock compression supplies every strict
lower threshold, not necessarily the endpoint threshold itself.  A simple
uniform specialization is `lambda = mu/2`, giving `mu^2 * D_*/24`.

## All-behavior and two-sure-quitter boundary tests

1. **The first best-endpoint update.**  Exact zero marked defect for `o` is a
   local root statement against the actual prescribed tail payoff.  It does
   not assert zero terminal debt for `o`.  This is exactly all the packet
   definition uses.

2. **The second best-endpoint update.**  Its payoff gain is an actual
   unilateral behavioral gain.  Since opponents are unchanged, `p`'s full
   behavioral cap is identical before and after the update.  Exact debt
   subtraction is therefore valid against unrestricted behavioral
   deviations, not only stationary or one-stage deviations.

3. **Tail invisibility in the Quit-mode packet.**  At the marked row both `j`
   and `o` Quit surely.  Under any one-player behavioral replacement, at least
   one remains a sure quitter.  Consequently replacing the continuation after
   that row by any other behavioral tail changes neither prescribed payoff nor
   any unilateral-deviation payoff, hence changes no cap coordinate.  This
   proves equality of the complete terminal semantic pairs of the two
   prefixed profiles.

4. **Sharpness of two sure quitters.**  With only one sure quitter, that
   player can deviate to Continue and expose the tail.  Hence the preceding
   all-behavior tail-invisibility conclusion is false in general with one
   sure quitter.  This also explains why the minimum-return tail does not make
   the whole Quit-mode profile near-minimal: the whole profile is entirely
   insensitive to which tail was attached.

5. **Alternating action boundary.**  If `o`'s exact best endpoint alternates,
   the routed labels alternate between `{j}` and `{j,o}`.  A packet has one
   fixed terminal, so the constant-action subsequence is genuinely necessary;
   an identity-subsequence construction before this selection is ill-typed.

## Files and declarations inspected

- `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`
  - `FinFourMinimumAtomChronology.prefix_debt_tendsto`
  - `FinFourMinimumAtomChronology.nonempty_ownerCompressedSingleton`
  - `FinFourMinimumAtomProducer.exists_commonChronology_cofinal_ownerCompressedSingleton`
  - `FinFourOwnerCompressedSingletonEndpoint.referenceProfile`
  - `FinFourOwnerCompressedSingletonEndpoint.targetProfile`
  - `FinFourOwnerCompressedSingletonEndpoint.target_stageMass_gt`
- `UniformEquilibrium/Quitting/Root/SelfTailClosure.lean`
  - `quittingSelfTailRootStack`
  - `quittingAllContinueProfileSpine_selfTailClosure`
  - `quittingProfileLiveRoot_literalRootStackProfile_eq_getElem`
  - `quittingAllContinueProfileSpine_literalRootStackProfile_length`
  - used to distinguish genuine self-tail closure from the needed cross-tail
    construction
- `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`
  - `QuittingStageAtomConcentratedPacketAdapter`
  - `sourceStageMass_le_targetStageMass`
  - `targetTail_eq_sourceTail`
  - `ownerMarkedDefect_eq_zero`
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`
  - `QuittingReprojectionConcentratedPacket`
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionConcentratedConsumer.lean`
  - `exists_concentrated_singleton_or_tailEscape_or_otherDefect`
- `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`
  - `QuittingConcentratedCollisionMinimumResidual`
  - `concentratedPacket_singletonStrategic_or_collisionMinimumResidual`
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`
  - `quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
  - `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain`

## Queue recommendation and nonclaims

Do not export this as a separate packet once the reviewed forced-pair normal
form is exported.  Fold the cross-tail correction and arbitrary-`lambda`
audit into that stronger packet.  If retained as a reusable generic theorem,
its statement should claim only:

\[
\text{minimum-singleton source}
\Longrightarrow
\text{strategic singleton}
\ \lor\ 
\text{minimum-return collision residual}.
\]

It should not claim:

- that the collision residual is consumed;
- that the whole moving profiles approach the minimum fibre;
- that copied source cap--Nash roots remain cap--Nash after cross-tail repair;
- that the second update lowers total debt;
- or that the packet yields terminal approximants, a charged return, support
  descent, or a uniform-equilibrium payoff.
