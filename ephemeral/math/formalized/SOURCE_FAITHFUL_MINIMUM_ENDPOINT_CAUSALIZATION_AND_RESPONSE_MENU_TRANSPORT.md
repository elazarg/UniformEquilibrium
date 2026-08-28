# Source-faithful minimum-endpoint causalization and response-menu transport

Authors: `CODEX_AMPERE`
Independent reviews:

- [initial interface audit](../feedback/CODEX_AMPERE__SOURCE_FAITHFUL_CAUSALIZATION_AND_RESPONSE_SEAM__BY_CODEX_NOETHER.md)
- [independent rereview after repair](../feedback/CODEX_AMPERE__SOURCE_FAITHFUL_CAUSALIZATION_AND_RESPONSE_SEAM__BY_CODEX_LAPLACE.md)

## Exact statement

Let `I` be a finite nonempty player type and let `r` be a finite quitting
reward table.  All strategies below are complete behavioral strategies, and
all caps quantify over arbitrary unilateral behavioral deviations, including
`Never` and unbounded or randomized stopping times.

Let

\[
 z=(x,\nu)
\]

be a joint terminal semantic/law carrier point with

\[
 D(x)=D_*>0,
\]

where `D_*` is the infimum of total terminal debt over actual behavioral
profiles.  Suppose actual profiles `sigma_n` are supplied such that

\[
 (\operatorname{Sem}(\sigma_n),\operatorname{Law}(\sigma_n))\to z.
\tag{1}
\]

Fix a nonempty terminal coalition `T`, dates `t_n`, and `lambda>0` satisfying

\[
 \Pr_{\sigma_n}(T\text{ absorbs at }t_n)\ge\lambda
 \qquad(n\in\mathbb N).
\tag{2}
\]

Then one may choose, for every `n`, an exact cap--Nash product-root word
`W_n` of length `n+1` above the **literal supplied suffix** `sigma_n`.  If

\[
 \widehat\sigma_n=W_n*\sigma_n,
 \qquad
 c_n=\Pr(W_n\text{ jointly survives}),
\]

then

\[
 D(\widehat\sigma_n)\to D_* ,
 \qquad c_n\to1,
\tag{3}
\]

and the marked atom is transported exactly:

\[
 \Pr_{\widehat\sigma_n}
   (T\text{ absorbs at }n+1+t_n)
 =c_n\Pr_{\sigma_n}(T\text{ absorbs at }t_n).
\tag{4}
\]

In particular the right side is eventually at least `lambda/2`.  Finite
cutoffs can be selected so that these exact supplied profiles, marks, root
words, and cutoffs form a minimum-law causal suffix chronology for `z` and
`T`.  No new realizing sequence is selected.

There is a response-menu enhancement.  Fix a player `o`.  For each `n`, let
`R_n^-` and `R_n^+` be any two complete behavioral response plans for `o`
against `sigma_n`.  Shift each plan by forcing `o` to Continue throughout
`W_n` and then following that plan literally.  If `c_{-o,n}` is the
probability that every opponent of `o` survives `W_n`, then

\[
\begin{aligned}
 &U_o(\widehat\sigma_n[o\leftarrow\operatorname{shift}R_n^+])
 -U_o(\widehat\sigma_n[o\leftarrow\operatorname{shift}R_n^-])\\
 &\qquad=c_{-o,n}
 \bigl(
 U_o(\sigma_n[o\leftarrow R_n^+])
 -U_o(\sigma_n[o\leftarrow R_n^-])
 \bigr),
\end{aligned}
\tag{5}
\]

with

\[
 c_n\le c_{-o,n}\le1,
 \qquad c_{-o,n}\to1.
\tag{6}
\]

Equation (5) holds rankwise for arbitrary behavioral plans.  Hence any finite
menu of two-counterfactual response contrasts attached to the incoming
sequence survives causalization asymptotically without loss.

### Fin4 endpoint adapter

Let `source` be a Fin4 minimum-atom producer and let `endpoint` be a
`ConcentratedCollisionThreeRoleEndpointLaw` whose target joint point is on
the global minimum-debt fiber.  Assume explicitly that the incoming marked
coalition is nonsingleton.  The checked per-rank mass theorem then gives the
uniform marked-mass hypothesis (2) on the endpoint's literal target profiles.

The construction above yields a new source-faithful regeneration object
containing:

1. the usual next `FinFourMinimumAtomProducer` at the endpoint target point;
2. an explicit public `FinFourMinimumAtomChronology` of that same producer;
3. pointwise equalities identifying the chronology's suffix profiles with
   the incoming endpoint target profiles; and
4. pointwise equalities identifying its marks with the incoming marked dates.

The point and named terminal are the endpoint target point and routed terminal
respectively.  These equalities are constructor data of the new chronology;
they are not inferred from the hidden existential chronology of the older
regeneration interface.

Without nonsingletonity one still retains the exact target profiles, but must
select new finite-window marks from the positive limiting terminal-law
coordinate.  Equality with the incoming marks is not asserted in that weaker
form.

## Conjecture-facing change

The minimum-fiber three-role regeneration previously reconstructed the target
point and terminal law but did not publicly attach its new chronology to the
actual endpoint profiles and dates.  This allowed every later response chart
to be lost through an unrelated realizing-sequence selection.

The theorem removes that loss.  The regenerated minimum source may use the
literal incoming endpoint sequence, while retaining its marked atom and any
finite family of complete response contrasts.  Thus arbitrary carrier
re-realization is no longer a possible explanation for response-witness
switching in the Fin4 minimum-return arm.

The result does not orient a paid cycle and does not consume spectator cap
leakage.  Observer rotation and the fixed-observer paid-endpoint consumer
remain open.

## Proof

### Debt squeeze and survival

Exact cap-stack accounting gives

\[
 D(W_n*\sigma_n)=c_nD(\sigma_n).
\tag{7}
\]

Every left side is the debt of an actual profile, so global minimality gives

\[
 D_*\le D(W_n*\sigma_n).
\tag{8}
\]

Since `0<=c_n<=1`, equations (7)--(8) yield

\[
 D_*\le D(W_n*\sigma_n)\le D(\sigma_n).
\tag{9}
\]

By (1), `D(sigma_n)->D_*`, so (9) proves the first part of (3).  Dividing
(7) by `D(sigma_n)`, whose limit is the positive number `D_*`, proves
`c_n->1`.

### Atom and cutoff

Literal root-stack transport gives (4).  Combining (2), (4), and `c_n->1`
gives the eventual `lambda/2` floor.  Coordinate convergence in (1) and
stage-mass domination also give

\[
 \nu(T)\ge\lambda>0.
\tag{10}
\]

For every sufficiently large `n`, the complete `T`-law mass is the increasing
sum of its finite-stage masses, so choose a finite cutoff whose sum exceeds
`nu(T)/2`.  Replacing the cutoff by its maximum with `t_n+1` preserves that
inequality and includes the supplied mark.  Together with words of length
`n+1`, this is exactly the causal chronology tuple; finitely many early ranks
may be filled arbitrarily because causality is eventual.

### Behavioral response transport

Both shifted counterfactuals prescribe exactly the same action—Continue—for
the observer throughout the prefix.  If an opponent absorbs in the prefix,
the two resulting payoffs agree.  Their payoff difference is reached only
when every opponent survives, with probability `c_{-o,n}`, at which point the
literal suffix comparison is unchanged.  This proves (5).

Joint survival implies opponent survival, hence

\[
 c_n\le c_{-o,n}\le1.
\]

Equation (6) follows by squeezing.  The proof uses no bounded response time.
`Never` shifts to `Never`; a finite relative quit date `q_n`, even when
`q_n->infinity`, shifts to the finite absolute date `|W_n|+q_n`; and an
arbitrary behavioral response shifts by following the same live hazards after
the prefix.

### Fin4 construction

For the endpoint object, set `sigma_n` equal to its literal target profile at
the retained strict rank and set `t_n` equal to the incoming mark.  Target
joint convergence supplies (1), target minimum equality supplies `D=D_*`,
and `perRank_mass_chain endpoint hcollision n` supplies (2).  Apply the
preceding construction, use its causal atom to build the same next producer
as the existing minimum-target regeneration, and simultaneously expose the
chronology made from the same tuple.  The profile and mark equalities are then
pointwise constructor equalities.

## Probability, information, and deviation audit

- Terminal outcomes are the first nonempty quitting coalition; infinite
  continuation pays the table's declared Never payoff.
- Product roots use independent simultaneous actions.  No correlated public
  randomization is added.
- Before absorption there is one live public history at each date.  Shifting
  an arbitrary behavioral strategy means sure Continue along the finite live
  prefix and the original live hazards afterward.
- Semantic caps range over the full unilateral behavioral strategy class.
- Equation (5) compares two counterfactual responses which agree during the
  prefix.  It does not identify either one with the new prescribed profile.
- The survival factor in (5) is opponent survival, not joint survival.
- Relative dates may diverge with `n`; every identity is rankwise exact.

## Boundary tests

1. **Observer Quit mass in the cap word.**  It does not affect (5), because
   both counterfactuals override the observer to Continue.  It would affect a
   raw gain against the prescribed prefixed profile, which is deliberately not
   claimed.
2. **Singleton incoming mark.**  The strong original-mark adapter is not
   asserted.  New finite-window marks remain available from (10).
3. **Zero-survival prefix.**  It is incompatible with (7)--(9) and `D_*>0`;
   in fact survival tends to one.
4. **Semantic/law equality without literal source attachment.**  In the
   two-player clock/tester table with `r_c({c})=-1`,
   `r_a({c,a})=1`, and the remaining displayed rewards zero, profiles in
   which `c` quits deterministically at an arbitrary date `N` and `a` plays
   Never have the same prescribed payoff, cap, debt, and terminal law, while
   `a`'s maximizing pure response occurs exactly at `N`.  Hence an unrelated
   realizer cannot preserve a response chart merely from semantic/law
   equality.  This regression has global minimum zero and is used only to
   test the interface.

## Source correspondence

The proof uses the following checked declarations and files:

- `exists_quittingCapNashRootStack`,
  `quittingTerminalDebtSum_capNashRootStack_eq`, and
  `quittingCapNashStackContinueProduct_le_one` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
- `quittingStageCoalitionMass_literalRootStack_add_length` and the existing
  causalization theorem in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `exists_finiteWindow_sum_stageCoalitionMass_gt` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionWindow.lean`;
- `ConcentratedCollisionThreeRoleEndpointLaw.target_joint_tendsto` and
  `perRank_mass_chain` in
  `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`;
- the existing minimum-target regeneration in
  `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`; and
- `quittingRelativePureTimeTerminalValue_sub_prefixTransport` and
  `quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul` for the
  already checked pure-time transport special case.

The new mathematical content is the supplied-realizer causalization package,
the source-faithful Fin4 endpoint wrapper, and the arbitrary-behavioral
two-counterfactual transport adapter.  Pure-time transport itself is not new.

## Adapter and remaining consumer

The actual-data adapter starts from the equality arm of a nonsingleton
`ConcentratedCollisionThreeRoleEndpointLaw`; no new table, minimum point, law,
profile sequence, or mark is selected.  Its output is the same next minimum
producer plus a public literal chronology and transported response menu.

Downstream, the output can be fed directly into the next minimum-atom/forced-
pair producer without losing the incoming endpoint realization.  What is not
yet supplied is a common observer chart around a complete paid cycle or a
consumer for the resulting fixed-observer paid switch.  This export strictly
closes the source-reselection gap; it does not claim those later arrows.

## Lean handoff

Suggested declarations:

```text
exists_deep_nearMinimum_capNashChronologies_from_supplied_causalRealizers

FinFourSourceFaithfulMinimumTargetRegeneration

ConcentratedCollisionThreeRoleEndpointLaw.
  nonempty_sourceFaithful_finFourMinimumTargetRegeneration

shiftedResponseDifference_capNashPrefix_eq_opponentSurvival_mul
```

The first theorem should accept the supplied convergent profiles and marks.
The Fin4 wrapper should store the next producer and a separate explicit
chronology, with propositional profile/mark equalities.  It must not try to
recover those equalities from the old producer's existential chronology.

## Scope and nonclaims

- No common observer is selected around a paid cycle.
- No cross-player response seam is called a unilateral deviation.
- No paid endpoint is consumed into a terminal approximation, admissible
  return, or renewable support decrease.
- No raw prescribed-profile gain is claimed to scale by one survival factor.
- No Lean, adapter, or consumer seal is claimed by this mathematical packet.
- No four-player or general counterexample is constructed.

## Formalization record

The packet's source-faithful causalization and both Fin4 endpoint forms are
proved in Lean in two checked Research modules.

`Research/Quitting/SourceFaithfulMinimumLawCausalization.lean` contains the
generic construction and response transport.

- `quittingShiftedBehavioralResponse` forces one responder to Continue along
  the finite root word and then follows the supplied complete behavioral
  response literally.
- `quittingTerminalPayoff_shiftedBehavioralResponse_sub_eq` proves the exact
  two-counterfactual identity (5) for arbitrary complete behavioral responses.
  `quittingLiteralRootStackJointSurvival_le_opponentSurvival` and
  `tendsto_quittingLiteralRootStackOpponentSurvival_one` prove (6).
- `QuittingSourceFaithfulMinimumCausalization` is indexed by the supplied
  profile and mark families.  It retains their joint semantic/law convergence
  and uniform marked mass, and stores only newly selected finite cutoffs and
  exact cap--Nash root words.  Its fields `prefix_debt_tendsto`,
  `continueProduct_tendsto_one`, `shifted_mark_mass_eq`,
  `eventually_shifted_mark_mass_floor`, and `causal` are the literal Lean
  forms of (3)--(4), the eventual `lambda / 2` bound, and the chronology.
- `nonempty_sourceFaithfulMinimumCausalization` constructs that object from
  the displayed minimum carrier point, supplied realizing profiles and marks,
  and uniform positive marked-stage floor.  It does not reselect either input
  family.
- `QuittingSourceFaithfulMinimumCausalization.lambda_le_terminalMass`,
  `terminalMass_pos`, `opponentSurvival_tendsto_one`, and
  `responseMenu_transport` expose the retained law atom and finite-menu
  consequences.
- `QuittingSourceFaithfulMinimumCausalChronology` and
  `nonempty_sourceFaithfulMinimumCausalChronology` are the weaker fallback:
  they retain the supplied profile family but select positive dates inside
  finite terminal-mass windows.  They claim no incoming-mark equality and no
  uniform per-stage floor.

`Research/Quitting/FinFourProducerAtlas/SourceFaithfulThreeRoleRegeneration.lean`
contains the actual Fin4 adapters.

- `FinFourSourceFaithfulMinimumTargetRegeneration` stores the explicit
  nonsingleton incoming-coalition certificate and the strong generic
  causalization at the endpoint target point and routed terminal.
  `ConcentratedCollisionThreeRoleEndpointLaw.nonempty_sourceFaithful_finFourMinimumTargetRegeneration`
  constructs it from a same-minimum three-role endpoint and the checked
  nonsingleton routed-stage mass chain.
- `FinFourSourceFaithfulMinimumTargetRegeneration.next`, `chronology`,
  `next_residual_eq`, `next_point_eq`, `next_terminal_eq`,
  `chronology_profile_eq`, and `chronology_mark_eq` retain the incoming hard
  residual, exact endpoint point and routed terminal, literal endpoint target
  profiles, and literal incoming marked dates.  The strong route retains the
  packet resolution as its uniform marked-stage floor and obtains the
  eventual half-resolution shifted floor from the generic causalization.
- `responseMenu_transport`, `responseMenu_lowerBound_transport`,
  `responseMenuMultiplier_tendsto_one`, and `responseMenuMultiplier_bounds`
  expose the arbitrary behavioral response identity, supplied menu lower
  bounds, and their exact multiplier on the same public chronology.
  `toMinimumTargetRegeneration` forgets to the older regeneration interface.
- `FinFourSourceFaithfulReselectedMarkRegeneration` and
  `ConcentratedCollisionThreeRoleEndpointLaw.nonempty_sourceFaithful_reselectedMarkRegeneration`
  implement the packet's singleton-compatible fallback.  They retain the
  endpoint target profiles, original hard residual, endpoint point, and routed
  terminal, but reselect positive finite-window dates.
  `eventually_selectedMark_mem_positiveWindow` makes that weaker date claim
  literal, while `chronology_profile_eq` records exact profile provenance.

Evidence seals:

- **M:** PASS.  The debt squeeze, survival limit, exact atom transport,
  arbitrary-behavior response transport, nonsingleton routed-stage route, and
  reselected-mark fallback match the reviewed proof and its boundary audit.
- **L:** PASS.  The named generic declarations and both Fin4 adapters are
  checked Lean declarations.
- **A:** PASS.  The strong Fin4 theorem starts from the actual same-minimum
  three-role endpoint and preserves its target profiles and incoming marks;
  the fallback preserves the actual target profiles and reselects only dates.
- **C:** Not present.  No common observer, paid-cycle orientation,
  spectator-leakage consumer, terminal approximation, renewable return, or
  uniform-equilibrium conclusion is constructed.

The modules are reachable through
`Research/Quitting/FinFourExhaustiveProducerAtlas.lean` and the `Research`
reader umbrella.  The two-player clock/tester example remains a mathematical
interface boundary test rather than a separately encoded regression theorem;
it is not used by any positive Lean declaration.  The packet proves no raw
prescribed-profile gain scaling, response-witness identification across
players, paid endpoint consumption, positive-gap counterexample, or general
finite-quitting completion.
