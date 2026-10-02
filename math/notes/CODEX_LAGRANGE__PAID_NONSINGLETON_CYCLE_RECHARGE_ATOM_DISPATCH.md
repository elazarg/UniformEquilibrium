# Paid nonsingleton cycles force a fixed spectator recharge and atom dispatch

Author: `CODEX_LAGRANGE`

## Status

This note proves an ordinary-mathematics contraction of the source-attached
period `4/6/8` obstruction in
`SERIAL_ENDPOINT_AUDITOR__PAID_SINGLETON_DYNAMICS_PAIR_BASE_NOGO.md`.

The contraction is source faithful.  At every outer rank, all cycle vertices
are literal pure-coalition siblings at the same marked date, with the same
complete pre-date behavior, the same complete post-date behavior, and the
same reached mass.  The final vertex is therefore the identical behavioral
profile, not merely the same coalition label.

If every selected edge has whole-profile gain at least `g_0`, exact own-debt
subtraction and literal return imply that some edge raises a distinct
spectator's unrestricted terminal-semantic debt by at least `g_0 / 3`.  For
the positive-minimum Fin4 dispatch one may take

\[
 g_0=\lambda D_*/4,
 \qquad
 c:=g_0/3=\lambda D_*/12.
\]

The checked theorem
`hasVanishingDebtAtomAlternative_of_endpointDebtRise` then gives, on that
actual source/endpoint edge and at errors tending to zero, a fixed atom
charge

\[
 q={7c\over8}={7\lambda D_*\over96}.
\]

Thus a paid nonsingleton cycle is not a bare terminal-reward circulation: it
produces a fixed-label, source-profile-exact vanishing-debt atom alternative.
This is a real local contraction, but not yet the maintained chronological
shadowing producer.  The atom decoder does not make its source and endpoint
successive play histories, and its decoded atom need not be the original
routed coalition.

There is also an exact compact target split.  If the recharged endpoint
cluster lies on the global minimum fibre, its actual terminal-law limit keeps
the routed coalition with mass at least `lambda`; same-point causalization
therefore regenerates a complete `FinFourMinimumAtomProducer` at that target,
with the same hard residual and the routed coalition as its causal atom.  If
the cluster is not minimum, it is a literal strict off-minimum endpoint.  The
fresh minimum chronology in the first arm is not a continuation of the paid
horizontal edge, so neither arm by itself closes uniform existence.

This note is not Lean checked and is not an export candidate without review.

## 1. Self-contained source-attached cycle data

Let `I = Fin 4`, let `r` be a quitting reward table, and assume a positive
global minimum terminal-semantic debt

\[
 D_*>0.
\]

Fix `lambda > 0`.  For every outer index `n`, retain:

* one actual behavioral profile `beta_n`;
* one marked date `t_n` whose live mass is `L_n >= lambda`;
* a common post-date profile (in the maintained forced-pair family this is
  literally the selected near-minimum `referenceProfile`); and
* a simple nonsingleton Boolean cycle
  \[
  C_0\xrightarrow{p_0}C_1\xrightarrow{p_1}\cdots
  \xrightarrow{p_{K-1}}C_K=C_0,
  \qquad K\in\{4,6,8\},
  \tag{1}
  \]
  where `C_{k+1}=C_k triangle {p_k}` and every displayed toggle is a
  strict best endpoint for `p_k`.

Define `sigma_{n,k}` by changing only the live root of `beta_n` at `t_n` to
the pure coalition `C_k`.  The relevant equality is behavioral-profile
equality:

\[
 \boxed{\sigma_{n,K}=\sigma_{n,0}.}
 \tag{2}
\]

Indeed, every sibling uses the same `beta_n`, the same date, and the pure
root determined by its coalition; `C_K=C_0`.  For each edge, put

\[
 \theta_{n,k}:=(\sigma_{n,k+1})_{p_k}.
\]

All other player strategies are unchanged, so

\[
 \boxed{
 \sigma_{n,k+1}
 =\operatorname{update}(\sigma_{n,k},p_k,\theta_{n,k}).}
 \tag{3}
\]

This is the exact input form required by the checked endpoint-debt-rise
decoder below.

The common-prehistory statement is also quantitative.  Reaching `t_n` is
decided before the overwritten root, hence every sibling has live mass
`L_n`.  Since `C_k` is nonempty and pure, absorption at the marked row is
certain conditional on reaching it.  Therefore

\[
 \Pr_{\sigma_{n,k}}(C_k\text{ at }t_n)=L_n.
 \tag{4}
\]

If `nu_{n,k}` denotes the complete terminal law, there is a common pre-date
subprobability law `nu_n^{pre}` such that

\[
 \boxed{
 \nu_{n,k}=\nu_n^{\mathrm{pre}}+L_n\delta_{C_k}.}
 \tag{5}
\]

In particular, the common post-date tail is retained literally by the
profiles, although it is screened on the event which reaches the
nonsingleton pure row.  Equations (2)--(5) are stronger than a repeated
finite coalition label.

### Match to the maintained forced-pair family

For
`FinFourOwnerCompressedMinimumReturnForcedPairPacket`, the initial pair
profile is

```text
(packet.base.forcedAdapter (packet.subsequence n)).targetProfile
```

over the literal common source

```text
packet.base.crossTailProfile (packet.subsequence n)
```

and marked date

```text
(packet.base.endpoint (packet.subsequence n)).stage.
```

The source attachment is checked by:

* `forcedTerminal_val` and `forcedTerminal_card`;
* `forcedPair_stageMass_eq_liveMass` and
  `lambda_lt_forcedPairStageMass`;
* `forcedPair_postDateSpine_eq_reference`;
* `payerTarget_postDateSpine_eq_reference`; and
* `payerRoutedStageMass_eq_liveMass`.

The first paid endpoint also has the stronger checked bounds `D_*/3` and
`lambda D_*/3`.  The cycle argument below uses only the uniform Fin4 bound
available after reselecting a best endpoint at every nonsingleton sibling.

## 2. Positive minimum gives the edge floor

For a nonsingleton coalition `C`, define the pure toggle wall

\[
 h_i(C):=[r_i(C\mathbin\triangle\{i\})-r_i(C)]_+,
 \qquad H_C=\sum_i h_i(C).
 \tag{6}
\]

The stationary pure-`C` profile is an actual terminal-semantic carrier
point, and `quittingTerminalSemanticDebt_pureSetRoot_eq` identifies its
whole debt coordinate with `h_i(C)`.  Global minimality gives

\[
 H_C\ge D_*.
 \tag{7}
\]

Selecting a maximum toggle at a Fin4 nonsingleton row therefore gives

\[
 h_{p_k}(C_k)\ge H_{C_k}/4\ge D_*/4.
 \tag{8}
\]

Because another quitter remains whenever a member leaves a nonsingleton
coalition, the continuation is screened.  The actual whole-profile payoff
gain is exactly

\[
 g_{n,k}
 :=U_{p_k}(\sigma_{n,k+1})-U_{p_k}(\sigma_{n,k})
 =L_n h_{p_k}(C_k).
 \tag{9}
\]

Combining `L_n >= lambda` with (8),

\[
 \boxed{g_{n,k}\ge g_0:=\lambda D_*/4>0.}
 \tag{10}
\]

The exact source theorem behind (9) is
`sourceToTargetGain_eq_liveMass_mul_defect`; its general one-date form is
the payoff identity used in
`quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain`.

The period classification is not used to improve (10).  It is used only to
know that `K` is finite, nonzero, and uniformly one of `4,6,8` after the
paid-singleton arm has failed.

Even if the classified orbit uses a fixed strict selector which is not the
maximum-wall selector, the recharge theorem below still applies.  The fixed
finite cycle then has

\[
 \bar h:=\min_{k<K}
   \bigl(r_{p_k}(C_{k+1})-r_{p_k}(C_k)\bigr)>0,
\]

so one may use the table-dependent floor `g_0=lambda * bar h`.  The explicit
`lambda D_*/4` value uses maximum-defect screening at every nonsingleton
vertex.

## 3. Cycle recharge lemma

Write

\[
 d_{n,k,i}:=
 d_i(\operatorname{Sem}(\sigma_{n,k})),
 \qquad
 \Delta_{n,k,i}:=d_{n,k+1,i}-d_{n,k,i}.
\]

Updating only `p_k` leaves that player's unrestricted cap unchanged.
The checked exact own-debt identity gives

\[
 \boxed{\Delta_{n,k,p_k}=-g_{n,k}.}
 \tag{11}
\]

Because (2) is equality of complete behavioral profiles, not only equality
of roots or coalitions,

\[
 \sum_{k<K}\Delta_{n,k,i}=0
 \qquad(i\in\operatorname{Fin}4).
 \tag{12}
\]

Sum (12) over players and separate each edge's mover from its three
spectators.  Using (11),

\[
\begin{aligned}
 \sum_{k<K}\sum_{j\ne p_k}\Delta_{n,k,j}
 &= -\sum_{k<K}\Delta_{n,k,p_k}\\
 &= \sum_{k<K}g_{n,k}\\
 &\ge K g_0.
\end{aligned}
\tag{13}
\]

There are exactly `3K` spectator-edge pairs.  Hence at least one pair
`(k_n,j_n)`, with `j_n != p_{k_n}`, obeys

\[
 \boxed{
 d_{n,k_n+1,j_n}-d_{n,k_n,j_n}
 \ge {g_0\over3}
 ={\lambda D_*\over12}.}
 \tag{14}
\]

This averaging allows signed spectator changes; no termwise monotonicity is
assumed.  Negative cap leakage on some edges only forces a larger positive
recharge elsewhere.

The set of possible `(k_n,j_n)` is finite.  Passing to a strict subsequence
freezes one cycle offset `k`, mover `p=p_k`, and observer `j != p` such that
(14) holds at every retained outer index.  Put

\[
 c:=\lambda D_*/12.
 \tag{15}
\]

This is the positive-minimum information which the terminal-reward
eight-cycle regression does not carry: its `D_*` is zero, so (15) gives no
charge there.

### General finite-player form

The same proof on `m` players gives a spectator rise at least
`g_0/(m-1)`.  No period bound is needed once literal profile return and a
uniform positive edge floor are supplied.

## 4. Checked atom dispatch from the recharge edge

At a retained outer index, set

\[
 \sigma=\sigma_{n,k},
 \qquad
 \tau=\sigma_{n,k+1}
   =\operatorname{update}(\sigma,p,\theta_n).
\]

Equation (14) is exactly

\[
 c\le d_j(\operatorname{Sem}(\tau))
       -d_j(\operatorname{Sem}(\sigma)).
 \tag{16}
\]

The theorem
`hasVanishingDebtAtomAlternative_of_endpointDebtRise` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
VanishingDebtAtomAlternative.lean` assumes:

* an actual `profile`;
* a mover, observer, and complete mover `target` strategy;
* positive `charge` and positive `error` with
  `error <= charge / 8`; and
* the observer debt-rise inequality at the literal
  `Function.update profile mover target` endpoint.

Its conclusion is

```text
HasQuittingStoppingLawVanishingDebtAtomAlternative
  reward profile mover observer target (7 * charge / 8) error.
```

Apply it with input charge `c`.  Define

\[
 q:={7c\over8}={7\lambda D_*\over96},
 \qquad
 e_n:={q/8\over n+1}.
 \tag{17}
\]

Then `e_n>0`, `e_n -> 0`, and

\[
 e_n\le q/8=7c/64\le c/8.
\]

Thus every retained outer index has

\[
 \boxed{
 \operatorname{HasVanishingAtomAlternative}
   (\sigma_{n,k},p,j,\theta_n,q,e_n).}
 \tag{18}
\]

Unfolded, (18) is the checked disjunction:

1. a prescribed terminal payoff-difference atom of scaled size at least
   `q/2`; or
2. one common pure-time response of `j`, a rectangle terminal atom of
   scaled size at least `q/4`, and observer debt at the responded endpoint
   at most `e_n`.

The source profile, mover target strategy, observer, and fixed charge are
retained exactly.  In the rectangle arm the response stopping time may vary
with `n`; the finite terminal label and the disjunction tag may be frozen by
another subsequence.

### Exact limitation of this contraction

Equation (18) is not yet a `QuittingVanishingDebtAtomAccess` as defined in
`UniformExistenceBoundary.lean`.  That structure is indexed by a supplied
`QuittingPositiveMinimumDebtTangentFamily`, uses its vanishing replacement
scale, and is only the static input to a still-missing local chronological
reprojection theorem.  The cycle profiles need not be near the minimum in
whole debt and have not been identified with one such tangent frontier.

Nor does (18) produce a
`QuittingChronologicalDebtShadowingCertificate`.  The terminal atom decoder
compares actual source/endpoint profiles and common observer responses; it
does not assert that the horizontal endpoint is reached after the source in
one play.  Its decoded terminal atom also need not equal `C_k` or
`C_{k+1}`.  Therefore the maintained chronological-shadowing producer still
needs a source-matched port, seam/radius control, and compatible iteration.

The honest contraction is

\[
 \boxed{
 \text{paid nonsingleton cycle}
 \Longrightarrow
 \text{fixed positive spectator recharge}
 \Longrightarrow
 \text{fixed-charge vanishing-debt atom alternative}.}
 \tag{19}
\]

It is a local atom-interface output, not a uniform-payoff consumer.

## 5. Compact target-law split and minimum-source regeneration

Retain the frozen recharge edge and compactify, along one further strict
subsequence, both endpoint semantic/law pairs:

\[
 (\operatorname{Sem}(\sigma_{n,k}),\nu_{n,k})\to(X,\mu),
 \qquad
 (\operatorname{Sem}(\sigma_{n,k+1}),\nu_{n,k+1})\to(Y,\nu).
 \tag{20}
\]

They remain in the compact joint terminal-semantic law carrier.  Debt
continuity and (14) give

\[
 d_j(Y)-d_j(X)\ge c,
 \qquad d_j(Y)\ge c>0.
 \tag{21}
\]

By (4) and
`quittingStageCoalitionMass_le_terminalOutcomeMass`,

\[
 \nu_{n,k+1}(C_{k+1})\ge L_n\ge\lambda.
\]

Finite-coordinate convergence therefore yields

\[
 \boxed{\nu(C_{k+1})\ge\lambda>0.}
 \tag{22}
\]

Global minimality gives `D(Y) >= D_*`.  There are two exact cases.

### Minimum target

If

\[
 D(Y)=D_*,
 \tag{23}
\]

then `(Y,nu)` is a supplied minimum joint-law point, retains the routed
cycle coalition `C_{k+1}` with positive mass, and has the known positive
debt coordinate (21).  Apply

```text
exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
```

to `(Y,nu)` and the specific terminal `C_{k+1}`.  Its hypotheses are exactly
joint-carrier membership, (22), positive terminal-debt infimum, and
`D(Y)=inf`.  The result is a
`QuittingMinimumLawCausalSuffixAtom r (Y,nu)` whose terminal is the routed
coalition itself.

Together with the unchanged
`FinFourQuantitativeFullSupportHardResidual`, carrier memberships, global
minimum proof, positive infimum, and debt-equals-inf equality, these data
fill every field of `FinFourMinimumAtomProducer`.  Hence

\[
 \boxed{
 D(Y)=D_*
 \Longrightarrow
 \text{full minimum-atom source regeneration at the actual target law},}
 \tag{24}
\]

with causal atom mass at least `lambda` and named positive debtor `j` of
debt at least `c`.

The generic theorem
`nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff`
also applies, but direct causalization is stronger here because it preserves
the routed coalition selected by the cycle.

### Off-minimum target

If (23) fails, then

\[
 D(Y)>D_*.
 \tag{25}
\]

This is a literal off-minimum endpoint cluster retaining the incoming common
pre/post-row provenance, routed law atom (22), recharge (21), and prelimit
atom alternatives (18).  No theorem inspected here returns it to the
minimum fibre or turns its strict excess into an admissible chronological
charge.

### Why regeneration is not recurrence

The chronology constructed in (24) is selected afresh from `(Y,nu)`.  It is
not asserted to extend any `sigma_{n,k+1}`, the old marked date, or the
horizontal update from `sigma_{n,k}`.  Regeneration therefore solves the
source-object problem but not the orientation problem:

\[
 \text{incoming paid edge}
 \not\Rightarrow
 \text{first edge of the regenerated exact chronology}.
\]

Repeated minimum-target regeneration can still cycle horizontally unless a
strict rank or executable seam theorem is added.

## 6. Resulting finite split

For the corrected paid-singleton dispatch, the current source-exact split is

\[
\boxed{
\begin{array}{ll}
\text{paid singleton endpoint},
  &\text{the maintained singleton arm};\\[1mm]
\text{period }4,6,8\text{ nonsingleton cycle},
  &\text{fixed spectator recharge and atom dispatch};
\end{array}}
\tag{26}
\]

and after compactifying the recharged endpoint, the cycle arm further splits
as

\[
\boxed{
 \text{minimum target with full same-law source regeneration}
 \quad\lor\quad
 \text{strict off-minimum target}.}
\tag{27}
\]

The first line of (27) is no longer blocked by missing minimum-law
provenance.  Its blocker is finite-rank or chronological recurrence after
regeneration.  The second line is blocked earlier: whole-target
near-minimality/return is absent despite the minimum post-date tail.

Thus a genuine positive-`D_*` counterexample surviving this reduction would
have to support the fixed-charge atom packet (18) while repeatedly selecting
either off-minimum endpoint clusters or minimum clusters whose freshly
causalized chronologies never inherit the incoming charge.

## 7. Declarations and files inspected

Checked declarations:

* `quittingTerminalSemanticDebt_pureSetRoot_eq` --
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`;
* `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` --
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticLiveWeightedCollisionTransfer.lean`;
* `sourceToTargetGain_eq_liveMass_mul_defect` and
  `targetOwnerDebt_eq_sourceOwnerDebt_sub_gain` --
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`;
* `hasVanishingDebtAtomAlternative_of_endpointDebtRise` and the definition
  `HasQuittingStoppingLawVanishingDebtAtomAlternative` --
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
  VanishingDebtAtomAlternative.lean`;
* `quittingStageCoalitionMass_le_terminalOutcomeMass` --
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticPureTimeRectangleDisintegration.lean`;
* `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` and
  `QuittingMinimumLawCausalSuffixAtom` --
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticLawCarrierCausalization.lean`;
* `nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff`
  -- `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticMinimumLawFiniteAtom.lean`;
* `finFourHardResidual_minimumLaw_causalSuffixAtom` --
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
* `FinFourMinimumAtomProducer` --
  `Research/Quitting/FinFourProducerAtlas/Source.lean`; and
* the forced-pair mass, gain, debt, tail, and fixed-payer declarations in
  `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`.

Conference boundaries inspected:

* `SERIAL_ENDPOINT_AUDITOR__PAID_SINGLETON_DYNAMICS_PAIR_BASE_NOGO.md`;
* `SERIAL_ENDPOINT_AUDITOR__MINIMUM_CAP_TUBE_FORCED_PAIR_BARRIER.md`;
* `THREE_ROLE_CONSUMER__TARGET_LAW_REGENERATION_AND_HORIZONTAL_RECURRENCE_BOUNDARY.md`;
* `FORCED_PAIR_REVIEW__ENDPOINT_CLOSED_PASSPORT_HAS_NO_RANK.md`; and
* `PAIR_WALL_REVIEW__POSITIVE_MINIMUM_CANONICAL_RAY_CYCLE.md`.

## 8. Requested independent checks

1. Check that the corrected period `4/6/8` orbit can be selected by a fixed
   maximum-defect rule at every nonsingleton vertex, so that (8)--(10) apply
   verbatim rather than with the finite table-specific minimum edge margin.
2. Check the literal profile identity (2) and the exact `Function.update`
   presentation (3) against the proposed all-nonempty endpoint edge type.
3. Check the signed spectator average (13), especially that all cap changes
   are already included in the whole semantic debts.
4. Check the constants `c=lambda D_*/12` and
   `q=7 lambda D_*/96` in the call to
   `hasVanishingDebtAtomAlternative_of_endpointDebtRise`.
5. Check the direct same-terminal causalization in (24), separately from the
   fresh-chronology nonreturn warning.

The next mathematical question is whether the fixed-charge packet (18),
together with either the fresh minimum source (24) or the strict endpoint
excess (25), supplies the missing source-matched local port and sublinear seam
needed by chronological debt shadowing.
