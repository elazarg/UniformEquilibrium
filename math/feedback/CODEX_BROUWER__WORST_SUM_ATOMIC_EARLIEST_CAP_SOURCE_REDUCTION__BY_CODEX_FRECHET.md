# Independent whole-artifact review of the atomic-earliest worst-SUM reduction

Reviewer identity: CODEX_FRECHET.

## Final verdict and frozen artifact

**PASS. No unresolved mathematical objection remains to the complete merged
artifact and its stated counterexample-source reduction.** This is an
ordinary-mathematical verdict, not a Lean check or an L/A/C seal. No uniform-
equilibrium existence theorem or unrestricted positive-gap example is proved.

Reviewed artifact:
[`CODEX_BROUWER__WORST_SUM_ATOMIC_EARLIEST_CAP_SOURCE_REDUCTION.md`](../notes/CODEX_BROUWER__WORST_SUM_ATOMIC_EARLIEST_CAP_SOURCE_REDUCTION.md),
920 lines, SHA256
`1e5c8544ed71e153ee90ae87ac72b8413153e29faa43460599f1ac510e0b6e83`.

I read the whole artifact, checked the integration of its thirteen sections,
and compared its changed mathematical material with the independently
reviewed 711-line source. The earlier wording ambiguity is resolved: cap
dates are not all equal; pairwise distinctness is explicitly not claimed.
The exact singleton-margin input (8), its tracked declaration/file, and its
full hypotheses and conclusion are restored in the final frozen version.
They are present in the reviewed bytes, not supplied by an implicit reference.

My separate EA1–EA6 falsification was performed without reading NOETHER's EA
review or verdict. This whole-artifact pass follows an independent assessment
of its actual source, full-cap endpoint, finite spectra, and reward selection;
it is not inferred merely from component agreement.

## Exact quantifier order and resulting normal form

The original input is the existence of any signed four-player quitting game
without a uniform-equilibrium payoff. The model has independent complete
natural-date stopping laws plus Never, terminal rewards on the first finite
tied coalition, zero reward on all-Never, and unrestricted complete unilateral
behavioral replacements. Every finite pure date and Never is a cap test.
No public correlation, bounded controller, or conditional payoff criterion
is introduced.

The proof produces one fresh sixty-coordinate unit-bounded reward table r̂
with positive actual global total-debt infimum d. This table is chosen before
any fresh minimizing sequence, owner, support, or cap family. For every finite
minimizing sequence at that table and every subsequence satisfying Section
3's convergences, every produced marked global minimum has either a multiple
maximizing-point cap, or all of the following properties:

- all four complete caps are unique and their dates are not all equal;
- at least two owners have zero own point mass at their respective caps;
- the earliest cap is finite, isolated, and has positive mixture point mass;
- at least one owner maximizing at that earliest point has zero own mass
  there.

An owner whose cap is later may supply the earliest mixture atom. Nothing
requires all earliest maximizing owners to carry own mass, or excludes the
earliest zero-own-mass point from topological support.

There is also a universal statement before the reward modification: at every
produced positive global SUM minimum of every bounded signed Fin4 table, the
earliest point in the union of all active response sets is finite. If it has
zero mixture mass, some owner has a sure strictly earlier prescribed law, and
each of the other three recipients has τ, c, and Never as full maximizers.
When τ=c the two finite names denote one point and there are two distinct
points including Never. The exception is retained exactly.

## Tracked source and objective audit

I followed the root/math instructions, SOURCES, GOAL, export gate, and both
project research methods. The relevant source lookup was bounded to the
stopping-law, terminal-carrier, singleton-margin, and membership-stretch
neighborhoods identified by `docs/TOOLKIT.md`.

The exact declarations checked in place under their displayed imports were:

- `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff`,
  `quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`,
  `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`,
  and
  `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
  in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`;
- `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws` and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime` in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`;
- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- `quittingTerminalSemanticCarrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and
  `quittingTerminalSemanticDebtSum` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticDebt.lean`;
- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `positive_minimum_fourPlayer_allOwner_quadraticMargins` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`;
- `quittingTerminalExploitability_eq_max_debt` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitability.lean`,
  `quittingTerminalExploitabilityInf` in
  `UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`,
  `exists_maximum_quittingTerminalExploitabilityInf_unitReward` and
  `exists_membershipStretch_singletonFiber_source_of_positiveInf` in
  `UniformEquilibrium/Diagnostics/Quitting/MembershipStretchWorstTableSource.lean`,
  and
  `exists_membershipStretch_source_opposedReversals_of_no_uniformPayoff_finFour`
  in `UniformEquilibrium/Diagnostics/Quitting/MembershipStretchOpposedSource.lean`.

The cited source files were confirmed tracked. The key behavioral bridge,
carrier, singleton-margin, and quadratic-margin sources were clean locally
when inspected. No Lean or axiom-audit command was run.

The nearby all-response switching fences were inspected in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSimultaneousMixtureWitnessSwitchRegression.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessPassportRegression.lean`.
The candidate proves simultaneous all-test stability rather than assuming
separate resets combine safely or that a selected branch remains active.
`Literature/README.md` and the quitting definitions in section 4 of
`Literature/Simon2007.lean` were read as a semantic comparison. No unproved
paper statement or `sorry`-backed Literature theorem is used.

The SUM/MAX distinction is exact. Nonnegative debts give

    inf_p max_i d_i(r,p) ≤ Δ(r) ≤ 4 inf_p max_i d_i(r,p),

but do not transfer minimizers, cap geometries, or worst tables. The existing
MAX membership-stretch sources do not provide the present SUM spectrum
identities and interval separation. The new proof consistently retains SUM
from its original no-UE input through fresh-source consumption.

## Producer, signed transport, and full moving caps

I independently reconstructed the Section 3 producer. Tail truncation is
uniform over responders, so finite laws have the unrestricted infimum. The
common quantile chart is deterministic; the four raw coordinates are sampled
independently. Bounded weak-* sequential compactness, the endpoint limit, and
the complete finite-response-set limit can be obtained on one subsequence.

A complementary interval of the limiting endpoint set comes from one old
positive atom and contains only its response midpoint. Endpoint points not
in the response limit are countable: two distinct endpoints in one response-
free complementary interval would force an intervening old atom midpoint.
The collapse consequently discards only a null set and yields genuine
marginal laws on the compact test calendar.

Marginal weak-* convergence gives product convergence on rectangles and then
all L¹ tests by density and the uniform product bound. Prescribed tie/order
kernels converge almost everywhere after excluding retained endpoints, c,
and raw equality diagonals. A moving response approaching a retained midpoint
must eventually be that original atom's actual date; any other limiting test
has zero mixture mass and comparison kernels converge off a null boundary.
Never is handled separately. These facts give payoff convergence and both
directions of the full-cap limit, not just convergence of selected tests.

The compact laws need not be a single natural-date behavioral profile. Their
actual payoff/full-cap pair is in the original behavioral semantic closure.
Continuous total debt and the all-actual-law floor make it a global minimum
of that carrier, exactly as required by (8).

Section 4 transports existing-atom resets and chronological conditionals
through the same old finite laws. Positive own atom mass or a positive
conditional normalizer permits a common small signed box. Old whole-interval
cuts converge strongly, normalizers remain positive, and modified old-chart
densities stay bounded. The prescribed and arbitrary moving-response kernels
are unchanged, so full-cap convergence survives simultaneous reweighting.
Removing old mass does not remove the old enumeration of all actual deadlines.
Zero c mass and the c/c⁺ duplicate comparison are preserved.

## All-active earliest conditioning: the actual endpoint check

Section 7 does not assume uniqueness. If the earliest point of the union of
all active sets were Never, every active set would equal {Never}. A zero own
Never mass gives another recipient equal maximizing c/Never values. If all
own Never masses are positive, Section 6's all-supported exclusion applies.
Thus earliestness is finite without a uniqueness premise.

At a zero-mixture earliest point τ, if a final strict-late mass vanishes,
its owner exits strictly before τ almost surely. Every other recipient's
entire upper response family has one payoff, and its nonempty active set has
a point in that family. The asserted full maximizing points follow. This is
a sure early law, not a pure-date replacement.

If all final late masses are positive, fix any lower cut u_n<τ and condition
all four owners late. Every nonoriginal opponent-product term contains an
exit before u_n, so the same positive affine transformation applies to every
response above u_n, including every active branch and Never. A compact lower
set below a_n<τ contains no active point for any owner, hence has positive
gaps preserved by uniform total-variation control. An empty lower set is
harmless. This produces one signed box with all complete caps represented by
their selected active branches. The box may shrink with n; the exact
multiaffine polynomial identity is obtained separately for each fixed n.

Positive final normalizers and zero mass at τ give total-variation convergence
of these conditionals and a direct bounded-density final-cut realization in
the original carrier. This is not an uncontrolled limit of conditioners with
vanishing normalizers.

At the final laws ν, expansion using E_j=q_j|_(clock<τ) applies to the closed
upper family t≥τ, including τ itself. Positive affine rescaling of the old
response ordering gives an upper bound by the displayed old maximizer τ_i
for every upper response. At τ the response pays s_i, so its displayed value
is at least s_i. Every lower finite response also pays s_i. Hence

    B_i(ν)=V_i(τ_i,ν_-i) for all i,
    B_m(ν)=s_m for one owner active at τ.

Only after this all-response bound does the selected polynomial identity
become actual D(ν)=δ. Carrier membership and the global floor make ν another
true minimum, where (8) gives δ≤B_m(ν)−s_m=0. Distinct later caps are allowed
to exceed singleton values; equality for one earliest owner suffices. This
is the new complete consumer, rather than a conditional endpoint interface.

## Finite spectra, fixed reward direction, and integration

Sections 6, 8, and 9 retain the independently checked identities: exceptional
latest debt a_m, common supported-set join sum C_A, earliest tie's individual
join J_(m,H), and the isolated earliest sole-unsupported F/G floor spectrum.
The sure boundary supplies all required old positive atoms. Late conditional
mass or actual pure play supplies the F/G reduction; the convex combination
in (13) alone is not used as an individual spectrum value. Other polynomial
endpoints remain selected-response identities without an actual-minimum
assertion.

Reward robustness gives the actual all-profile 8e bound for Δ. Whole-cube
worst SUM selection and the singleton margin imply Ω≤4/5<1. Independent
exact enumeration of all sixteen omitted/grand sign patterns confirmed 82
labels, maximum coefficient ℓ¹ norm six, and every positive-contact endpoint
target at least one. Contact C_A sums require no positivity of their old
individual terms.

The same fixed direction separates every possible new minimum value in
[Ω−16α,Ω]. A contact moves above Ω; an upper noncontact stays above Ω;
a lower noncontact stays below Ω−16α because 28α<σ. This covers every fresh
minimizing law and every changing owner, support, or tester. The table is not
changed again after seeing those choices. The eight-entry subtheorem and its
optional fiber maximization are kept distinct from the expanded direction.

The integration is stronger than the earlier theorem for an explicit reason.
Section 7 makes an all-unique earliest cap a finite positive mixture atom,
hence isolated. A sole unsupported owner must be later, tied earliest, or
strictly earliest. The first two cases meet the avoided a/J spectra; the
strictly earliest case now necessarily meets the avoided F/G spectrum.
There is no remaining appeal to the invalid uniform-gap principle at a
nonisolated point. This excludes every sole-unsupported all-unique source.
Together with common-cap exclusion and the earliest supported-group
alternative, it yields precisely the stated fresh-table normal form.

## Exact attempts to falsify the actual hypotheses

The artifact's participant-indicator tests check out exactly. Pure date-zero
play has unique supported caps and zero debt. Independent half-date-zero,
half-Never laws have U_i=1/2, B_i=1, D=2; resetting with λ=1/4 gives date-zero
mass 5/8 and debt 3/2. Thus a positive debt at one profile is insufficient.
The all-zero table likewise permits a zero-mixture earliest c=0 with all
final late masses positive when the true gap is zero.

I independently enumerated the no-strict-late example at N=4 and derived its
formula for every N. Recipient 0's finite response is the fraction of
{N,…,2N−1} strictly before its date; each other recipient's is the fraction
of {0,…,N−1} strictly before its date. Never pays one to every recipient.
Thus U=(0,1,1,1), B=(1,1,1,1). Its chart limit has τ=1/4 and e_0=0,
while e_0^n=1−4u_n is positive at every preceding cut and tends to zero.
The other three caps maximize on [τ,c] and Never. All-Never is exact Nash,
so the displayed D=1 is correctly not called the global gap.

An additional independent attack uses owner 0 as Never observer, owner 1
with density 1/2 and Never mass 1/2, owner 2 with density t and Never mass
1/2 on raw clocks [0,1], and owner 3 Never. Give observer 0 passive
singleton rewards +1 on {1}, −1 on {2}, and zero otherwise. Give every
other recipient payoff one when absent from a nonempty quitting coalition,
and zero when present. All own singletons are zero. Then

    V_0(t)=t/2−t²/2+t³/12,
    A_0={2−√2},
    A_1=A_2=A_3={last finite point,Never},
    D=(2√2−1)/6>0.

The earliest active point is nonisolated with zero mixture mass and all
final late masses positive. Yet AllNever is Nash and the global infimum is
zero. This attacks a stronger claim with distinct later active sets and
confirms exactly where the global minimum hypothesis is required.

In that example a legal reset of owner 1 toward its positive Never atom gives

    V_0^λ(t)=(1−λ)(t/2+t³/12)−t²/2,
    (V_0^λ)′(2−√2)=−λ(1/2+(2−√2)²/4).

Thus an arbitrarily small signed existing-atom reset can move a nonisolated
unique cap. The merged proof avoids that false stability principle by using
early submeasures and the actual final full-cap comparison. Finally, an
isolated zero-mass c is possible, and a negative singleton against pure
Never opponents distinguishes a selected finite payoff from the true Never
cap. These attacks reinforce rather than invalidate the stated safeguards.

## Significant increment, inherited strengthening, and final boundary

No strategic witness required by this reduction remains assumed. The original
no-UE bridge supplies the positive gap; finite approximation supplies
minimizing sequences; compactness and moving kernels supply each marked
minimum; existing-atom or positive-mass chronological conditioning supplies
every local law change; and the full-cap endpoint proof consumes the earliest
zero-mixture branch. When conditioning fails, a definite sure-early output is
proved. Whole-table selection then produces one fresh source for all later
requests. This is not an exceptional conditional certificate statement.

The result demonstrably narrows the surviving counterexample-source
obligation: it eliminates the previously remaining sole-unsupported
nonisolated-earliest arm and forces every all-unique source to have at least
two unsupported owners at a finite isolated positive-mixture earliest atom.
The tracked MAX selections and compact SUM pair/margin results do not state
this geometry. It establishes no new raw reward-table UE existence class,
and it leaves both advertised residual branches open.

Separately, the implemented all-owner quadratic-margin theorem applies with
M=1 and gives B_i−s_i≥d+d²/8 and U_i−s_i≥d²/8. At the worst SUM table it
improves the inherited numerical bound to Ω≤√33−5. These are existing
consequences, not this artifact's geometric contribution; the weaker bound
used in the artifact already suffices for finite contact separation.

The complete proof, exact probability/agency scope, tracked inputs, boundary
tests, actual producer, and narrow Lean handoff are present in the frozen
artifact. There is no deferred mathematical lemma or conference-file
dependency in that artifact. The next mathematical question is a whole-law
repair of a surviving multiple-cap source or of an all-unique source with
several unsupported owners at the earliest mixture atom. Export assembly
still requires the conference's independent-review count and other mechanical
gate checks; this review leaves no mathematical objection to its stated
scope.
