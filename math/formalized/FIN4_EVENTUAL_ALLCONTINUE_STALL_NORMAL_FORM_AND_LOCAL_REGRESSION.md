# Eventual all-Continue rays fix finitely, and local hard data do not exclude the stall

Author: `CODEX_NOETHER`

Independent review:
[`CODEX_NOETHER__EVENTUAL_CONSTANT_FORCED_PAIR_STALL__BY_CODEX_RIEMANN.md`](../feedback/CODEX_NOETHER__EVENTUAL_CONSTANT_FORCED_PAIR_STALL__BY_CODEX_RIEMANN.md)

## Exact statement

Let a canonical maximum-absorption semantic prefix ray be generated from an
actual finite-clock forced-pair source.  At step (k), choose a product root
(q_k) of maximum absorption among all exact Nash roots against the current
unrestricted behavioral cap, and prefix it to the current semantic/profile
state (Z_k).

Suppose the strict arm of the ray occurs, so its limiting debt is

\[
  L>D_*>0,
\]

where (D_*) is the global minimum terminal semantic debt.  If for some
(N), the selected root is all Continue,

\[
  q_N=\mathbf C,
\]

then all of the following hold.

1. Every exact root against the cap of (Z_N) is all Continue.
2. The ray is literally constant from (N) onward:

   \[
     Z_k=Z_N\qquad(k\ge N).
   \]

3. (Z_N) is represented by one actual finite-clock profile.  Its shifted
   pure pair terminates play by a finite date under the prescribed profile
   and under every unilateral behavioral deviation.
4. Every unrestricted behavioral cap at (Z_N) is therefore the maximum of
   finitely many pure-time deviation payoffs and is attained.

Let (p) be the canonical paid mover, let (Y) be its literal best-endpoint
update at the marked pure-pair row, and let (g>0) be its exact whole-profile
gain.  Then

\[
 d_p(Y)=0,
 \qquad
 D(Y)=D(Z_N)-g+K_p,
 \tag{1}
\]

where the entire remaining obstruction is the spectator leakage

\[
 K_p:=\sum_{i\ne p}\bigl(d_i(Y)-d_i(Z_N)\bigr).
 \tag{2}
\]

Global minimality supplies only

\[
 K_p\ge g-(L-D_*).
 \tag{3}
\]

It supplies no upper bound on (K_p).

There is moreover an explicit rational four-player quitting table which
simultaneously has:

- the paired normalized singleton matrix;
- full normal core and `ResidualHardClass`;
- punishment normality for every player;
- a full-support uniform singleton packet of mass (1/4);
- a literal forced pair ({0,1}) with semantic data

  \[
    U=(1,4,1,2),\qquad B=(3,4,2,2);
  \]

- owner (1) of zero defect and outside payer (2) of gain (1); and
- all Continue as the unique exact root at that cap.

Here is the complete table definition.  Index players by (0,1,2,3), put

\[
 M=\begin{pmatrix}
 0&3&-1&-1\\
 3&0&-1&-1\\
 -1&-1&0&3\\
 -1&-1&3&0
 \end{pmatrix},
\tag{4}
\]

and set (r_i(\{a\})=M_{ia}).  For (T\subseteq I\setminus\{i\}),
define passive values (f_i(T)) by (f_i(\{a\})=M_{ia}), with every
other value zero except

\[
 f_2(\{0,1\})=1,\qquad f_3(\{0,1\})=2.
\tag{5}
\]

Define membership gains

\[
\begin{aligned}
 g_0(T)&=\mathbf1_{3\in T}-2\mathbf1_{1\in T},\\
 g_1(T)&=\mathbf1_{0\in T}-2\mathbf1_{3\in T},\\
 g_2(T)&=\mathbf1_{0\in T}-2\mathbf1_{3\in T},\\
 g_3(T)&=\mathbf1_{1\in T}-2\mathbf1_{0\in T},
\end{aligned}
\tag{6}
\]

and, for every coalition containing (i), set

\[
 r_i(T\cup\{i\})=f_i(T)+g_i(T).
\tag{7}
\]

Equations (4)--(7), together with the passive rule
(r_i(S)=f_i(S)) when (i\notin S), define every coordinate of every
nonempty coalition.

For this table the canonical ray is immediately constant.  Nevertheless,
all Never is an exact equilibrium and (D_*=0).  Thus the local matrix,
punishment, singleton-packet, forced-pair, and unique-cap-root data do not by
themselves consume eventual stall.  Any valid consumer must use the positive
global-minimum/terminal-witness provenance through a genuinely nonlocal
control of (K_p) or an equivalent chronological object.

## Conjecture-facing change

The strict normalized inert branch previously allowed an ambiguous
"eventually all-Continue" limiting behavior.  The theorem removes that
ambiguity: this arm is exact finite fixation at one literal finite-clock
profile, not a compactness bubble or a tail-escape phenomenon.

The rational regression also decisively rules out a local proof using only
the non-witness hard fields and unique-root rigidity.  The live eventual-stall
obligation is the signed spectator leakage (2), with the positive global
minimum as indispensable input.

## Proof

### Finite fixation

The selected root (q_N=\mathbf C) has zero absorption.  Since it maximizes
absorption among exact roots and absorption is nonnegative, every exact root
against the same cap also has zero absorption.  A product root has zero
absorption exactly when every player Continues surely.  Hence all Continue is
the unique exact root.

Prefixing all Continue changes neither prescribed payoff nor any opponent
strategy, unrestricted cap, debt coordinate, or terminal law.  The
autonomous selector therefore sees the same cap again and selects the same
root.  Induction gives (Z_k=Z_N) for all (k\ge N).

The source is a literal finite profile with a pure pair at its marked date,
and only finitely many roots have been prefixed before fixation.  Under any
one-player deviation, at least one member of the pure pair still Quits at the
marked date.  Hence no unilateral deviation reaches a later date.  Before
the mark there are finitely many pure quitting dates, and Never is the only
remaining pure-time endpoint.  The standard pure-time representation of a
behavioral best response is therefore a maximum over this finite set.  This
proves actual cap attainment without restricting the deviator to stationary
or finite-memory strategies.

### Leakage identity

At a pure pair, a unilateral endpoint change cannot expose the tail because
another member still Quits surely.  Exact prefix scaling therefore makes the
copied marked gain (g) the mover's entire whole-profile debt.  Changing only
the mover's prescribed strategy leaves its unrestricted cap unchanged, so
its debt falls by exactly (g) and becomes zero.  Summing the coordinate
changes gives (1)--(2).  Since (Y) is an actual profile,
(D(Y)\ge D_*); substituting (D(Z_N)=L) gives (3).  The inequality has the
wrong direction for descent and contains no upper estimate on the spectators.

### Rational regression

Direct evaluation of (4)--(7) at (C=\{0,1\}) gives

\[
 U(C)=(1,4,1,2),\quad B(C)=(3,4,2,2),\quad d(C)=(2,0,1,0),
\]

and

\[
 r_2(\{0,1,2\})-r_2(\{0,1\})=1.
\]

Against (b=(3,4,2,2)), writing the root hazards as
((x_0,x_1,x_2,x_3)), the four Quit-minus-Continue differences are

\[
\begin{aligned}
 G_0&=x_3-2x_1-3(1-x_1)(1-x_2)(1-x_3),\\
 G_1&=x_0-2x_3-4(1-x_0)(1-x_2)(1-x_3),\\
 G_2&=x_0-2x_3-2(1-x_0)(1-x_1)(1-x_3),\\
 G_3&=x_1-2x_0-2(1-x_0)(1-x_1)(1-x_2).
\end{aligned}
\tag{8}
\]

At an exact root, (x_i>0) implies (G_i\ge0), whereas (x_i=0)
implies (G_i\le0).  If (x_0>0), the first inequality gives
(x_3\ge2x_1).  The case (x_3=0) forces (x_1=0,x_2=1), after which
(G_1=x_0>0), impossible.  Hence (x_3>0); then (G_3\ge0) gives
(x_1\ge2x_0>0), while (G_1\ge0) gives (x_0\ge2x_3).  Chaining
these inequalities yields (x_3\ge8x_3), impossible.  Thus (x_0=0).

If (x_1>0), (G_1\ge0) forces (x_3=0,x_2=1), and then
(G_3=x_1>0), contradicting (x_3=0).  Hence (x_1=0).  If
(x_3>0), (G_3\ge0) forces (x_2=1), and then (G_0=x_3>0),
contradicting (x_0=0).  Hence (x_3=0).  Finally (x_2>0) would give
(G_2=-2<0).  Every hazard is therefore zero, proving unique all Continue.

Direct calculation of the normalized singleton matrix gives (4), from which
the checked paired-matrix theorems give the full normal core and residual-hard
matrix facts.  Punishment normality follows because against all Never, Quit
and Never both pay zero.  The average of each row of (M) under the uniform
owner law is (1/4\ge0), giving the claimed full-support packet.

Finally, every own singleton reward is nonpositive at all Never, so no player
can profit by quitting against opponents who Never quit.  Thus all Never is
an exact terminal Nash profile and (D_*=0).  This is an exact boundary
regression, not a candidate counterexample.

## Boundary audit

- The theorem quantifies over unrestricted unilateral behavioral deviations;
  finite cap attainment follows from sure termination by another pair member,
  not from a stationary-deviation approximation.
- The regression does **not** instantiate
  `FinFourQuantitativeFullSupportHardResidual`: it deliberately lacks the
  terminal exploitability witness and its witness-dependent `massFloor`.
- Equation (3) is only a lower bound on spectator leakage.  Reversing it would
  assume the missing theorem.
- The result does not consume a genuinely infinite shrinking ray.

## Source correspondence

The canonical selector, exact cap-root scaling, and strict-ray dichotomy are
in:

- `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
- `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`; and
- `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`.

Pure-pair all-behavior screening and literal endpoint debt subtraction are in
the terminal semantic reached-row and same-stage endpoint modules named by
the upstream forced-pair packet.  The paired singleton matrix facts already
exist in the Fin4 block-pair example modules.  The new content is the exact
finite-fixation/cap-attainment normal form, its leakage localization, and the
single rational table co-realizing all witness-independent local fields with
immediate stall.

## Adapter and consumer

The checked canonical forced-pair maximal-prefix ray supplies the input
without reselection.  The output replaces the eventual-stall arm by one
finite actual state plus the exact scalar/vector obligation (K_p).  A future
consumer must use positive global-minimum provenance to prove an upper
control on (K_p), convert it to chronological charge, or regenerate a
well-founded minimum-fibre source.

## Lean handoff

The elementary formal targets are:

```text
maximalCapRay_eq_eventually_const_of_selected_allContinue
eventualConstantRay_unique_exactRoot_allContinue
eventualConstantForcedPair_caps_attained_finitePureTime
eventualConstantForcedPair_endpoint_debt_eq_sub_add_spectatorLeakage
```

The regression should be a witness-independent structure or conjunction.  It
must not manufacture a terminal witness or `massFloor` field.  Its unique-root
proof is finite endpoint algebra and should remain separate from the generic
fixation theorem.

## Scope and nonclaims

The positive-minimum stall normal form does not prove terminal approximants,
a uniform-equilibrium payoff, a positive-gap counterexample, or an upper bound
on (K_p).  The regression has (D_*=0) and exists to exclude local-only
arguments; its all-Never profile separately gives a uniform-equilibrium payoff
for that explicit zero-minimum table only.

## Formalization record

The packet is proved in Lean at its full corrected scope in two checked
Research modules.

`Research/Quitting/FinFourProducerAtlas/EventualAllContinueStallNormalForm.lean`
contains the generic finite-barrier and actual strict-ray normal form.

- `quittingRootSequenceHazardTerminalValue_eq_of_eq_le_of_opponentBarrier`,
  `sSup_range_quittingRootSequencePureTimeTerminalValue_eq_barrierBest`, and
  `exists_quittingContinuationBestResponseValue_eq_pureTime_of_barrier` prove
  that a finite opponent sure-stop barrier makes the unrestricted behavioral
  cap a finite attained pure-time maximum.
- `FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayProfile_opponentBarrier`
  and `exists_rayProfile_capAttainer` apply that theorem to every actual row
  of the retained pure-pair maximal ray.
- `FinFourMaximalRayEventualAllContinue.fixedProfile_semantic_eq`,
  `rayPair_eq_fixedProfile`, `fixedProfile_unique_exactRoot`, and
  `exists_fixedProfile_capAttainer` retain one actual finite-clock profile,
  the fixed semantic orbit, the unique exact all-Continue root, and attained
  full behavioral caps.  The equality here is semantic-orbit equality; the
  theorem does not identify the date-shifted `BehaviorProfile` sequence
  pointwise.
- `FinFourMaximalRayEventualAllContinue.fixedProfile_debt_eq_rayLimit` proves
  that this profile has debt `L`.
- `fixedProfile_endpoint_debt_eq_sub_add_spectatorLeakage` proves (1)--(2),
  while `rayPaidGain_sub_fixedExcess_le_spectatorLeakage` and
  `rayPaidGain_sub_rayLimitExcess_le_spectatorLeakage` prove (3).
  `not_spectatorLeakage_lt_rayPaidGain_sub_fixedExcess` records the exact
  strict-descent no-go.
- `endpoint_debt_eq_minimum_of_spectatorLeakage_le` returns the endpoint to
  the minimum fibre only under the displayed supplied upper threshold.  No
  theorem produces that threshold.

`Research/Quitting/FinFourEventualAllContinueLocalRegression.lean` implements
the packet's exact rational table rather than substituting another
zero-minimum example.

- `normalizedSoloMatrix_eq`, `normalCore_eq_univ`, `residualHardClass`,
  `normal`, and `singletonPacket_support_eq_univ` prove the paired normalized
  singleton matrix, full normal core, witness-independent residual-hard
  class, punishment normality, and full-support uniform singleton packet of
  mass `1/4`.  The table does not instantiate a positive terminal-gap witness
  or its witness-dependent mass floor.
- `pair_semantic_eq`, `pair_debt_eq`, `owner_one_debt_eq_zero`,
  `payer_two_debt_eq_one`, `payerEndpoint_gain_eq_one`, and
  `payerEndpoint_debt_eq_zero` prove the advertised pair payoff
  `(1,4,1,2)`, unrestricted behavioral cap `(3,4,2,2)`, debt
  `(2,0,1,0)`, zero-debt owner `1`, and unit-gain payer `2`.
- `endpointDifference_zero`, `endpointDifference_one`,
  `endpointDifference_two`, and `endpointDifference_three` are the literal
  four endpoint polynomials in (8).  `exactRoot_eq_allContinue` proves their
  unique exact-root consequence.
- `maximalRoot_pairSemantic_eq_allContinue` and
  `maximalPrefixOrbit_pairSemantic_eq` prove immediate fixation of the
  canonical semantic ray.
- `neverTerminalNash`, `neverPair_globalMinimum`,
  `terminalDebtSumInf_eq_zero`, `neverUniformEquilibriumPayoff`, and
  `not_hasPositiveMinimumTerminalSemanticDebt` prove the all-Never exact Nash
  profile, global debt minimum zero, its literal uniform-equilibrium payoff,
  and the impossibility of attaching this table to a positive-minimum source.

The mathematical and Lean seals are `M` and `L`.  The strict-ray normal form
retains `A` relative to the already selected actual eventual-all-Continue
branch, but it does not prove that branch occurs for a positive-minimum source
and has no downstream `C`.  The explicit regression has `A` and `C` for its
own zero-minimum table through its literal profiles and all-Never uniform
payoff; those seals do not transfer to the positive-minimum strict branch.

No upper bound on spectator leakage, leakage orientation or cancellation,
chronological return, debt descent, source regeneration, terminal
approximation, positive-gap counterexample, recursive completion, or general
uniform-equilibrium conclusion is proved.
