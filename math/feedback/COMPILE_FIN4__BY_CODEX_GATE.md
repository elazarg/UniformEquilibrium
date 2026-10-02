# Export-gate review of `COMPILE_FIN4`

Reviewer: `CODEX_GATE`

## Verdict

**FAIL as one export packet.** The note contains correct ordinary mathematics,
but its three examples do not have one common conjecture-facing scope, and the
surrounding program-schema claims are not proved at export strength.

There is one plausible narrow export after revision:

> A positive lower bound on exact cap--Nash prefix debt, together with one
> retained positive finite coalition atom, forces a quantitative failure of
> total-variation tightness along every cofinal outward-prefix sequence.

The proof in Proposition 2 is correct after replacing the undefined phrase
“no source-faithful actual behavioral limit exists” by an exact statement
about the marginal stopping laws. It answers the acceptable-partial-answer
clause of
`questions/FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL.md` for one precisely
specified operation and adapter class. It does **not** by itself consume the
actual uniform-escape component.

Proposition 1 is also correct and genuinely strengthens the full-root example
relative to the constrained-face example already exported in
`exports/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`. It should be
folded into that packet or its Lean handoff rather than creating a second
generic adapter-grammar export. Its table has global debt infimum zero.

Proposition 3 is a correct example for the bare raw-decoration topology, but
it is not an instance of the positive-minimum normalized actualizer: its table
has global debt infimum zero and its decorated point has zero whole debt. It
therefore does not prove that the present Fin4 minimum-return hypotheses fail
to imply tightness. Keep it as an internal boundary example unless a distinct
named obligation is supplied.

No Lean source was changed or compiled in this review. The assessment is of
ordinary mathematics and exact source correspondence only.

## Mandatory export checklist

| Gate item | Status | Finding |
| --- | --- | --- |
| 1. Exact self-contained statement | **FAIL** | `actual tail`, `semantic debt`, `exact cap--Nash root`, `compact executable trace`, `source-faithful`, `deleted-player law`, and the topology on behavioral profiles are not defined. The seven instruction types do not have a formal trace semantics. |
| 2. Complete definitions and proof | **FAIL as a packet** | Propositions 1--3 and the tight-port lemma have complete elementary proofs in their narrow meanings. The claimed “sufficient finite program schema,” the global trace exclusion, the summable relaxed-root **decoder**, and the ranked transition are not proved. Section 5 proves only an approximate-root selection lemma and explicitly leaves payoff, cap, debt, law, and ancestry estimates outstanding. |
| 3. Probability, information, agency, stopping, and deviations | **PARTIAL** | The stopping-law coupling correctly covers private independent behavioral clocks and complete unilateral replacement, including Never and arbitrarily late stopping. The packet must state that these are the project’s one-live-history product behavioral semantics. “Behavioral limit” must not mean pointwise hazard convergence, under which the prefix sequence may converge to all Continue. |
| 4. Actual-data adapter or named boundary change | **FAIL as written; repairable for Proposition 2** | The asserted direct application to the current uniform-escape packet is unsupported: its positive marked atom is before the literal post-row tail to which the one-root dispatch is applied. Proposition 2 can instead be presented as the exact negative answer for a retained-atom recursive cap--Nash-prefix adapter class accepted by `FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL`. |
| 5. Positive and negative boundary tests | **PARTIAL** | The rational calculations in Propositions 1 and 3 are valid. The retained-atom theorem still needs explicit sharp boundary tests: finite prefixing is legal; `m=0` removes the obstruction; without a positive debt lower bound the retained mass may vanish; and the conclusion is failure of law-tight compactification, not failure of pointwise hazard compactness. |
| 6. Source and freshness audit | **FAIL** | The note gives a commit hash but no declaration/file audit, no comparison with the existing exports, and no literature statement. Much of Sections 1, 2, 7, and 8 overlaps existing exported or checked material. Exact overlap is recorded below. |
| 7. Independent review with no unresolved objection | **FAIL pending revision** | This review leaves mandatory scope and packet-structure objections. Once the retained-atom theorem is split and corrected, I found no mathematical objection to that theorem. The current monolith cannot cite this review as a pass. |
| 8. Lean handoff | **FAIL** | The note offers an architectural vocabulary but not a theorem-level handoff with proposed declarations, dependencies, and finite tests. A narrow handoff for Proposition 2 is proposed below. |

## Independent mathematical checks

### Proposition 1: full maximal-root nonclosedness — PASS narrowly

For the displayed table and source profile `tau_t`, direct calculation gives

\[
U(\tau_t)=(t,-t,0,-1/2),\qquad B(\tau_t)=(t,0,0,0),
\]

so the total debt is `t + 1/2`. These are unrestricted caps:

- player 0 obtains at most `t`, attained by waiting or Never;
- each of players 1, 2, and 3 obtains zero by Never, and every event in which
  that player Quits has nonpositive payoff.

At continuation cap `(t,0,0,0)`, players 1, 2, and 3 strictly Continue. Player
0 compares Quit value zero with Continue value `t`. Hence all Continue is the
unique exact root for `t>0`; for `t=0`, every player-0 mixture is exact and
sure Quit uniquely maximizes absorption. Thus the graph of **unconstrained**
absorption-maximal exact roots is not closed.

This is stronger than the constrained-face calculation in the existing
adapter-grammar export. It remains a generic topological example only: the
all-Never profile has debt zero, so the table does not test a positive global
minimum or the actual Fin4 residual.

The note should not infer the complete “cannot be a visible edge of a compact
executable trace” conclusion without either restating the closed-output
theorem and its adapter class or explicitly invoking the already exported
`CW`/`SD`/bounded-`Rank` theorem. Nonclosedness alone excludes continuous
compact-output realizations; it does not define every possible meaning of
“compact executable trace.”

### Proposition 2: retained-atom prefix escape — PASS after topology repair

Let

\[
D_n=D(\sigma_n),\qquad c_n=\Pr_{x_n}(\text{all Continue}),
\qquad C_n=\prod_{k<n}c_k.
\]

Exact cap--Nash debt scaling gives `D_n=C_n D_0`. From `D_n >= D_*>0`,

\[
C_n\ge q:=D_*/D_0>0.
\]

If the initial profile has coalition `S` at finite date `s` with mass `m`,
literal prefixing puts that same coalition at date `n+s` with mass `C_n m`,
hence at least `qm`. Every member `i` of `S` therefore has at least `qm`
finite stopping mass beyond every fixed horizon along a suitable cofinal
row. No common finite-tail envelope exists.

Since `C_n` decreases to a positive limit, `c_n=C_{n+1}/C_n` tends to one.
For fixed `t<n`, player `i`'s stopping probability at date `t` is bounded by
the absorption mass `1-c_{n-1-t}`, and therefore tends to zero. If `p_{i,k}`
is player `i`'s individual Continue probability in `x_k`, then

\[
P_{i,n}=\prod_{k<n}p_{i,k}\ge C_n\ge q
\]

has a limit `p_i`, and the Never coordinate is exactly

\[
P_{i,n}\Pr_\tau(T_i=\infty)
\longrightarrow p_i\Pr_\tau(T_i=\infty).
\]

The coalition atom implies `Pr_tau(T_i=infinity) <= 1-m`, so the limiting
finite coordinates together with the limiting Never coordinate have total
mass at most `1-qm`. The same argument applies to every cofinal subsequence.

The exact conclusion should be:

> For every `i in S`, the live-spine stopping-law sequence has no
> total-variation-convergent cofinal subsequence in the space of probability
> laws on `Nat` plus Never. Its coordinatewise finite/Never limit is a
> subprobability law with defect at least `(D_*/D_0)m`.

This does not say that no behavioral profile is a pointwise limit of the
hazards. Pointwise hazard convergence may produce the all-Continue profile;
that profile simply fails to preserve the displayed stopping-law and terminal
chronology. This topology correction is mandatory.

The proof does not use maximality of the roots. The strongest theorem should
therefore quantify over **every** exact cap--Nash left-prefix chain satisfying
the positive debt lower bound. The canonical maximal-prefix ray is a
corollary, not part of the hypotheses.

### Tight-port realization lemma — PASS but duplicate

Coordinate convergence at each finite date and at Never, together with a
common finite-tail envelope, proves conservation of total mass and
total-variation convergence. The hazard quotient realizes the limiting law.
Product coupling and contraction under the labelled first-stopping map give
uniform convergence of the complete one-coordinate replacement kernel, hence
of unrestricted behavioral caps. The proof is sound under either standard TV
normalization; the packet should fix one convention so its constants are
literal.

This is not new conjecture-facing content. The actual-law realization and
uniform replacement estimates are already part of
`exports/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`, while
`StoppingLaw.stoppingLaw_toScalarHazard` and
`quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` provide the checked
law-to-behavior inverse. The current frontier also has the more semantic
opponent-tight realization theorem. The lemma may be cited in the narrow
packet, but should not be advertised as a new Fin4 adapter.

### Section 5: relaxed maximal-root selection — PASS only as a root lemma

The compactness argument is correct: if `b_n -> b`, an absorption maximizer
over roots with defect at most `2 ||b_n-b||_infinity` has exact
absorption-maximal cluster points at `b`. A null sequence admits a subsequence
below any prescribed positive summable error schedule.

What is **not** proved is the claimed summable macro decoder. The note itself
leaves the one-step payoff, cap, debt, stopping-law, and ancestry estimates
open. Until those estimates and a downstream finite consumer are supplied,
this is a possible comparison-transport ingredient, not a legal replacement
or an exportable adapter.

### Proposition 3: constant raw decorations — PASS narrowly, FAIL as a Fin4 actualizer objection

With player 0 Quitting surely at date `n`, the whole semantic/law point is
constant, the postmark spine is all Never, the marked mass is one, the
player-1 gain over the player-2 comparison clock is one, and player 0's local
defect is zero. Player 0's marginal clock is `delta_n`, so no total-variation
tight subsequence exists.

This exactly demonstrates that `QuittingMarkedPairDecoration` omits absolute
clock data. But the displayed table has a zero-debt all-Never profile, and the
constant endpoint decoration itself has zero whole debt. It does not satisfy
the positive reference-debt hypotheses of
`QuittingMarkedPairMinimumReturnActualizer`. Therefore the conclusion

> the existing actualizer therefore needs a `TightPort` field

is too strong. The valid conclusion is conditional:

> The bare raw-decoration topology, even with positive marked mass and actual
> gain, does not imply stopping-law tightness. Any use of its limit as an
> actual source needs an additional theorem; the current actualizer correctly
> retains actual approximating rows and does not claim that the carrier point
> is attained.

That fact is already explicit in the checked source and current frontier.

## The failed direct application to uniform escape

The principal conjecture-facing overclaim is in “Application to uniform
escape.” The current source-preserving uniform-escape adapter defines
`FinFourUniformEscapePacket.continuationProfile` as the all-Continue spine
**after** the marked row and applies
`FinFourUniformEscapePacket.exists_maximalCapNash_halfFloorDispatch` to that
post-row tail. Its source guarantees the tail's semantic pair and complete
outcome-law provenance, but this declaration does not supply a positive
finite stage atom inside that continuation profile.

The source-preserving marked atom occurs at the row immediately before this
tail. It cannot be used as Proposition 2's initial suffix atom without a new
adapter showing that a positive finite atom exists in the literal
`continuationProfile` itself. This is the same provenance distinction already
enforced by the tail-escape source audit: escaped terminal-law mass and a
pre-tail collision atom are not current root absorption and are not
automatically atoms of the post-row continuation.

Accordingly, replace “applies directly under the positive-global-minimum
hypothesis” and “the construction has exactly the hypotheses used above” by:

> The theorem excludes a recursive exact-prefix compactification whenever the
> literal source to which it is applied already carries the displayed finite
> atom. The present one-root uniform-escape dispatch does not itself provide
> that tail-atom hypothesis, so no terminal component is consumed here.

## Source, duplication, and telescope audit

The relevant declarations inspected were:

- `quittingUniformEquilibriumPayoffConjecture`
  (`UniformEquilibrium/Quitting/Conjecture/Basic.lean`), the open target;
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`), the positive
  and negative semantic endpoints;
- `quittingBehaviorStoppingLaw`
  (`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`) and
  `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy`
  (`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`),
  the complete live-spine law and its behavioral realization;
- `quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`)
  and
  `quittingStageCoalitionMass_rootThenContinuation_succ`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`),
  the two exact telescopes used in Proposition 2;
- `quittingMaximalCapPrefixProfile_debt_succ`,
  `summable_maximalCapPrefix_absorption`, and
  `maximalCapPrefix_atomMass_lowerBound`
  (`Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`), the existing
  maximal-ray debt and retained-atom core;
- `semanticMinimum_mul_capNashStackAbsorptionSum_le_debtDrop`
  (`Research/Quitting/CapChangingLawRetainedSquareNoGo.lean`), the stronger
  arbitrary finite exact-stack telescope already checked;
- `QuittingMinimumLawCausalSuffixPureNeverMarginalLimit.not_jointTight` and
  `.not_opponentTight`
  (`Research/Quitting/MinimumLawCausalSuffixPureNeverLimit.lean`), the existing
  checked failure of tightness for the source-matched all-Continue inert
  branch;
- `FinFourUniformEscapePacket.continuationProfile`,
  `.semanticPair_continuationProfile_eq_tail`, and
  `.exists_maximalCapNash_halfFloorDispatch`
  (`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`),
  the actual one-root uniform-escape interface;
- `QuittingMarkedPairDecoratedFamily.baseDecoration`, `.rawDecoration`,
  `.rawDecoration_markedMass_eq`, `.rawDecoration_actualGain_eq`, and
  `.descendant_postMarkSpine_eq`
  (`Research/Quitting/NormalizedPassportPrefixOrbit.lean`), the exact carrier
  tested by Proposition 3;
- `QuittingMarkedPairMinimumReturnActualizer` and its `profiles`,
  `sourceProfiles`, `resolution_le_stageMass`,
  `gainFloor_le_actualPayoffGain`, and `wholeDebt_tendsto`
  (`Research/Quitting/NormalizedPassportMinimumReturn.lean`), which retain
  actual rows but do not attain the compact point; and
- `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit`
  (`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`),
  the current checked tightness-based semantic realization boundary.

The freshness split is therefore:

1. Proposition 1 strengthens the existing constrained-face root example to
   the full exact-root correspondence, but does not enter positive global
   minimum.
2. Proposition 2's exact quantitative subprobability defect for an arbitrary
   positive-debt exact prefix chain is the most plausible new statement. Its
   debt and atom identities are already checked; the new part is the explicit
   marginal stopping-law escape conclusion.
3. The tight-port theorem, vanishing-reach warning, abstract grammar, and rank
   rules substantially overlap existing exports.
4. Proposition 3 is a tailored raw-decoration instance of the already known
   clock-escape/nonattainment boundary, and does not meet the positive-minimum
   actualizer hypotheses.

A narrow search of tracked `Literature/` found no paper theorem being invoked
for any of these claims. The packet should simply state that no
literature-derived result is used; it should not imply a literature novelty
claim beyond the repository comparison above.

## Required split and disposition

Do **not** export the current note as one result.

### Primary packet: conditionally exportable after correction

Proposed title:

# Positive-minimum exact cap--Nash prefix rays with a retained atom are not stopping-law tight

Proposed outline:

1. **Exact statement.** Fix a finite nonempty player set, bounded quitting
   table, actual tail `tau`, finite coalition/date atom `(S,s,m)`, and an
   outward sequence of literal prefixes. Require every root to be exact Nash
   against the full unrestricted continuation cap and every prefixed profile
   to have debt at least one fixed `D_*>0`. State the exact finite-coordinate,
   Never-coordinate, tail-envelope, and no-TV-subsequence conclusions.
2. **Conjecture-facing change.** Name the acceptable partial-answer clause of
   `FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL`. Exclude only compact trace
   edges that require the prefix-ray stopping laws to actualize by
   total-variation tightness. State that the actual uniform-escape component
   is not consumed without a tail-atom adapter.
3. **Definitions and assumptions.** Define behavioral product clocks,
   unilateral caps, total debt, literal root prefixing, stage-coalition mass,
   total variation, and a tight finite-tail envelope.
4. **Proof.** Separate the debt-survival identity, retained-atom shift, failure
   of tightness, fixed finite-coordinate limit, Never-coordinate limit, and
   quantitative missing-mass conclusion.
5. **Boundary tests.** Show finite prefixes are executable; `m=0` removes the
   law obstruction; a zero debt lower bound permits the retained mass to
   vanish; and pointwise hazard convergence does not provide operational-law
   convergence.
6. **Adapter and consumer.** State the excluded adapter class exactly and list
   only genuine alternatives: stop at a finite prefix, discharge the escaped
   mass through a proved decoder, or reconstruct an independently tight
   source before applying a pointwise root.
7. **Source correspondence.** Use the declarations listed above and explain
   the overlap with the existing pure-Never/non-tightness results.
8. **Lean handoff.** Suggested theorem shape:
   `not_tight_marginalStoppingLaws_of_capNashPrefixChain_retainedAtom`, with a
   quantitative corollary
   `coordinateLimitMass_le_one_sub_debtRatio_mul_atomMass`. Reuse the checked
   debt and stage-mass telescopes rather than rebuilding them.
9. **Scope and nonclaims.** No uniform payoff, no positive-gap table, no
   obstruction to finite prefixing, no obstruction to pointwise post-limit
   selection, and no claim that the present uniform-escape tail carries the
   required atom.

### Proposition 1: fold into an existing packet

Add the unconstrained four-player table as a strengthening of
`EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO`, or append it to that
packet's formalization handoff. A separate export would duplicate the already
resolved generic architecture obligation. Preserve the explicit nonclaim
`D_*=0`.

### Proposition 3 and the remaining schema

Keep Proposition 3, the incomplete relaxed-root decoder, and the
regeneration/suffix design audit in `notes/`. They are useful diagnostics but
do not independently pass the conjecture-facing export criterion. The final
packet must also remove the transient CI sentence and commit-status prose;
source correspondence should be timeless and declaration-based.

## Final gate decision

The current file is **not ready for `exports/`**. After the split and the
mandatory topology/provenance corrections, the retained-atom prefix-ray
theorem is mathematically sound and can return for a focused final gate. No
mathematical repair is required inside its core calculation; the remaining
work is exact statement, source-facing scope, packet structure, boundary
tests, and Lean handoff.

## Focused final gate: `POSITIVE_MINIMUM_EXACT_PREFIX_CLOCK_ESCAPE`

Target rechecked:
`/tmp/POSITIVE_MINIMUM_EXACT_PREFIX_CLOCK_ESCAPE.md`.

### Final verdict

**PASS for one export packet.** I found no unresolved mathematical objection.
The revised packet isolates only the generic exact-prefix clock theorem, its
varying-tail reverse-prefix strengthening, and the actual Fin4 strict
maximal-ray specialization. The original root-selector example, decoration
example, abstract schema, relaxed-root construction, and uniform-escape claim
are absent. The remaining three results form one proof chain and should not be
split into separate packets.

This is an ordinary-mathematics gate. It does not assign a Lean seal.

### Eight-item export checklist

| Gate item | Status | Focused finding |
| --- | --- | --- |
| 1. Exact self-contained statement | **PASS** | The packet fixes a finite nonempty player set, bounded rewards, actual product-behavior profiles, unrestricted unilateral caps, literal prefixing, all constants, the stopping space `Nat` plus Never, and one TV normalization. In the Fin4 corollary it now identifies the positive global minimum `D_*`, the ray-source debt `D_0`, and the strict limit `L`, with `D_0 >= L > D_* > 0`. |
| 2. Complete definitions and proof | **PASS** | Theorem A proves the debt telescope, retained-atom transport, fixed-coordinate decay, Never-coordinate limit, exact missing mass, and exact TV limit `1 - min(a_i,b_i)`. Theorem B proves finite-head decay and unit late-finite escape for varying tails. No mathematical lemma is deferred. |
| 3. Probability/information/agency audit | **PASS** | The packet uses the one-live-public-history quitting semantics, independent behavioral randomization, complete stopping laws, and arbitrary unilateral behavioral replacement, including Never and arbitrarily late randomized stopping. It distinguishes finite-tail mass, the Never coordinate, TV convergence, and weak convergence on the one-point compactification. |
| 4. Named adapter or live-boundary change | **PASS** | The precise excluded operation is the ancestry-preserving strategic-TV actualization of the displayed infinite canonical maximal-prefix ray. This is an accepted negative partial answer to `questions/FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL.md`. The packet states the surviving options: finite stopping, an explicit error-controlled clock decoder, or an independently tight reconstructed source. |
| 5. Positive and negative boundary tests | **PASS** | The packet records legality of every finite prefix, the roles of the positive debt and atom hypotheses, the Nash-free scope of Theorem B, the pointwise all-Never hazard boundary, the weaker one-point weak topology, and the possibility of unrelated tight reconstruction. These tests match the exact conclusion and do not turn it into a nonrealizability claim. |
| 6. Source and freshness audit | **PASS** | The named debt, literal-stack, survival, and marked-stage declarations occur in the cited files. The direct actual-profile debt theorem is now cited. The packet correctly says `rayBaseProfile_neverMass_eq_zero` is a joint terminal-outcome fact and assigns the marginal zero-Never projection to the new handoff. It also distinguishes the existing replicated-all-Continue/pure-Never results `QuittingMinimumLawCausalSuffixPureNeverMarginalLimit.not_jointTight` and `.not_opponentTight`. No paper result is used. |
| 7. Independent review | **PASS** | The earlier reviews' live objections have been incorporated: the packet was split, topology made exact, the fixed-tail/varying-tail mismatch removed, the stronger TV formula included, the marginal/joint Never distinction repaired, and the uniform-escape atom misattachment disclaimed. This focused review leaves no objection. |
| 8. Lean handoff | **PASS** | The proposed declarations separate generic fixed-tail, generic reverse-prefix, and Fin4 marginal-law conclusions. The handoff reuses checked debt and stage transport and explicitly asks the formalizer to derive pair-member zero Never from the sure pure-pair base rather than storing the desired conclusion as a field. |

### Independent proof and source check

For Theorem A, exact cap--Nash prefixing gives

```text
D(sigma_n) = C_n D_0,     C_n = product_{k<n} c_k.
```

The debt floor makes `C_n` decrease to `C_infinity >= D_*/D_0 > 0`, so
`c_n = C_(n+1)/C_n -> 1`. The retained tail event moves to date `n+s` with
mass `C_n m`. At every fixed date, a player's stopping mass is bounded by
the corresponding receding root absorption and tends to zero. Individual
Continue products converge, giving the stated Never limit `a_i`, while the
retained event yields

```text
1 - a_i >= C_infinity m >= (D_*/D_0)m.
```

On the countable stopping space, finite overlap with any fixed law tends to
zero and overlap at Never tends to `min(a_i,b_i)`. Hence the asserted exact
TV limit is `1 - min(a_i,b_i)`. This also rules out every cofinal TV-convergent
subsequence.

For Theorem B, the root at fixed absolute date `t` in the rank-`n` reverse
word is `x_(n-1-t)`. A player's Quit marginal there is at most
`alpha_(n-1-t)`. A fixed finite sum therefore tends to zero. Zero base Never
mass survives every finite prefix, so all remaining mass is late and finite.
This proves unit escape and TV distance tending to one without using Nash.

For the actual Fin4 adapter, the checked profile is
`packet.rayFamily.rayProfiles n`: its outer word is the reverse canonical
maximal-root stack, and its base is the fixed sure pair followed by a
rank-dependent counterfactual tail. The actual-profile debt identity and the
positive strict limit imply root absorption tends to zero. Each pair member
has marginal Never mass zero directly from the initial pure-pair root.
`rayProfiles_stageMass_eq_survival` gives marked-date pair mass tending to
`L/D_0`. Earlier roots could also produce the same terminal pair, so the
packet now correctly states only that the time-forgetting pair coordinate has
liminf at least `L/D_0`, and that every selected law cluster retains at least
this mass.

### Final packet title and outline

Retain the proposed title:

> **Positive-minimum exact-prefix rays force stopping-clock escape**

Recommended single-packet order:

1. generic fixed-tail theorem with the exact TV formula;
2. varying-tail reverse-prefix theorem;
3. strict Fin4 maximal-prefix corollary;
4. named-question narrowing and permitted repairs;
5. probability/topology definitions;
6. the two proofs and source-facing adapter proof;
7. declaration-level source/freshness audit;
8. boundary tests, Lean handoff, and explicit nonclaims.

The packet is ready to enter `exports/` under this title, subject to the
ordinary author/coordinator file move. No mathematical amendment is required
by this gate.
