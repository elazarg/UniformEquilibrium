# Independent review of the worst-SUM cap-spectrum source reduction

Reviewer identity: CODEX_FRECHET.

## Current verdict and review boundary

**PASS for the three numbered mathematical conclusions**, as an ordinary
mathematical counterexample-source reduction. I found no unresolved
mathematical objection after reconstructing the producer, signed transport,
cap-stability arguments, source identities, and fresh-table comparison. This
review is not a Lean check and confers no L, A, or C seal.

The reviewed source is
[`CODEX_MORSE__WORST_SUM_CAP_SPECTRUM_SOURCE_REDUCTION.md`](../notes/CODEX_MORSE__WORST_SUM_CAP_SPECTRUM_SOURCE_REDUCTION.md),
711 lines, SHA256
`4c6cc98812936445f78f20151f23e5b20a2d4def783bc2e8bfbe5894a0a4e8d1`.
The complete frozen source, rather than a selected earlier argument, was
reviewed. It was not edited.

One wording qualification is necessary: the prose phrase “distinct unique cap
dates” must mean **not all four cap dates equal**. Pairwise distinctness is not
one of the three numbered conclusions and is not proved. The numbered theorem
is sound with its stated quantifiers. An assembled statement should say “unique
cap dates which are not all equal,” retaining possible partial ties.

The newer tracked all-owner quadratic margin applies to these sources and can
be inherited. Its role and a resulting stronger numerical bound are recorded
separately below; they do not undermine the claimed new geometric reduction.

## Exact claim being checked

There are four owners. Every nonempty quitting coalition has one real reward
for each owner, and joint Never has reward zero. On the unique live history,
strategies are independent complete stopping laws on natural dates plus Never.
A deviation replaces one owner's entire law; all finite deadlines and Never
are available. Payoffs, caps, and debts here are unconditional expectations of
terminal rewards, not finite-horizon payoffs, conditional regrets, or pathwise
bounds. Define

    d_i(r,p) = sup_t V_i(t,p_-i) - U_i(p),
    D_r(p) = Σ_i d_i(r,p),
    Δ(r) = inf_p D_r(p).

The exact quantifier order is

    existence of any signed Fin4 no-UE table
      ⇒ existence of one table r̂ in the sixty-coordinate unit cube,
         with d = Δ(r̂) > 0,
         such that for every finite-law sequence minimizing D at r̂,
         and every subsequence satisfying the marked producer's convergences,
         every resulting marked minimum satisfies conclusions (1)–(3).

Those conclusions are:

1. Four unique complete caps cannot share one maximizing point.
2. If all caps are unique, the earliest maximizing group contains an owner
   with zero own point mass at its maximizing point.
3. If exactly one owner has zero own point mass at its unique cap, that cap is
   strictly earlier than all other caps and is nonisolated in the finite-test
   calendar.

Own point mass, topological support, and mixture point mass are different
notions. The last conclusion forces a finite zero-mixture-mass point because
the producer isolates every positive finite mixture atom and isolates Never.
It does not assert that the point is outside topological support.

The table is chosen before every new minimizing sequence. This is not a
statement about the geometry of every original counterexample, nor does it
transfer an original minimizer to a modified table. The separate eight-entry
construction preserves all singleton entries before the optional own-singleton
fiber maximization; the expanded construction does not preserve them.

## Bounded source and overlap audit

I read the root and math instructions, SOURCES, GOAL, export gate, and both
project research-method documents. I used the membership-stretch section of
`docs/TOOLKIT.md` to locate the relevant existing selection route and searched
the stopping-law and terminal-semantic subtrees for nearby definitions and
no-go results. No global Lean survey or build was performed.

The following tracked declarations were inspected under their displayed
imports:

- `quittingStoppingLawExpectedPayoff`,
  `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff`,
  `quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`,
  `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`,
  and
  `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
  in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
  Their cap is over complete replacement laws, not a bounded response menu.
- `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws` and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime` in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`.
  These justify the reduction of an unrestricted deviation to a supremum over
  finite pure deadlines and Never.
- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.
  The gap quantifies over every complete behavioral profile. Its UE target is
  fixed before accuracy; its imported terminal-to-uniform selection is the
  appropriate bridge for the live-date reward convention.
- `quittingTerminalSemanticPair` and `quittingTerminalSemanticCarrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and
  `quittingTerminalSemanticDebtSum` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticDebt.lean`.
  The carrier is the closure of actual payoff/cap pairs and the objective is
  the sum of the four cap-minus-prescribed coordinates.
- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
  Its hypotheses are carrier membership, a global SUM minimum, and positive
  sum debt. There is no sign, conditioned-Nash, or punishment hypothesis.
- `positive_minimum_fourPlayer_allOwner_quadraticMargins` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
  Its stronger consequences apply here, as discussed below.
- `quittingTerminalExploitability_eq_max_debt` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitability.lean`, and
  `quittingTerminalExploitabilityInf` in
  `UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`.
  The latter minimizes MAX debt, not total debt.
- `exists_maximum_quittingTerminalExploitabilityInf_unitReward` and
  `exists_membershipStretch_singletonFiber_source_of_positiveInf` in
  `UniformEquilibrium/Diagnostics/Quitting/MembershipStretchWorstTableSource.lean`,
  and
  `exists_membershipStretch_source_opposedReversals_of_no_uniformPayoff_finFour`
  in `UniformEquilibrium/Diagnostics/Quitting/MembershipStretchOpposedSource.lean`.
  These produce a different, MAX-aligned source. They do not state the present
  marked-calendar cap-order or unsupported-owner conclusions.

The two nearby fences inspected were
`not_simultaneousMixtureSwitchEnvelope_subadditive_at_moving_source` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSimultaneousMixtureWitnessSwitchRegression.lean`
and `envelope_is_modular_on_vertices` together with the common-witness
discussion in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessPassportRegression.lean`.
The candidate does not assume separately safe resets combine safely, nor that
modular envelope values supply a common witness. It proves simultaneous
stability against all tests on one signed box before using multiaffinity.

I also read `Literature/README.md` and the quitting-game definitions in section
4 of `Literature/Simon2007.lean`, including `QuittingGame`, `QuitProfile`, and
`IsQuitEpsilonEquilibrium`. These are consistent with terminal reward zero on
nontermination and complete sequence deviations. No paper theorem or
`sorry`-backed Literature declaration is an input to this proof. The new
compactification and geometric arguments must stand on the proof given here.

The cited files were confirmed tracked. The principal behavioral bridge,
carrier, singleton-margin, and quadratic-margin files had no local changes at
inspection. This is a static declaration/source audit, not a claim that I ran
Lean or an axiom audit.

## Independent reconstruction of the producer

The finite-support reduction is uniform in the responder. Moving an owner's
finite tail mass to Never changes a prescribed terminal reward only on the
union of the changed draws; with rewards bounded by M its error is at most
2M times that union's probability. A fixed response sees only the changed
opponents. The same bound therefore passes through the supremum over all
finite deadlines and Never. Tail finite masses tend to zero, so the finite-law
and unrestricted-law infima agree.

The common quantile coordinate is a deterministic chart for the four
marginal laws. The product measure still uses four independently sampled raw
coordinates. There is no common random draw, public signal, or correlation.
Each density is bounded by four. Bounded weak-* compactness is sequential here
because L¹ is separable; the common subsequence can additionally retain the
finite endpoint and finite-response sets in the Hausdorff topology and retain
c_k.

I checked the two geometric assertions needed for collapse. A component of
the limiting endpoint complement lies eventually in one old atom interval;
its endpoints converge to the component endpoints, and its sole response
point is the atom midpoint. Distinct limiting endpoints in an interval
disjoint from the response limit would force an old response midpoint between
them. Consequently each complementary component of T contains at most one E
point. The discarded E points are countable, hence null. This justifies the
almost-everywhere monotone collapse and its pushed marginal probability laws.

Products of the marginal densities converge weak-* on the product raw space:
first test against products of L¹ functions, then use finite sums of rectangle
tests and their L¹ density. Uniform density bounds control the approximation.
This argument does not multiply two weak limits on the same variable.

For the prescribed kernels, outside retained interval endpoints, c, and the
raw equality diagonals, two coordinates either lie in the same retained atom
or are separated by a limiting endpoint. The old tie/order indicators then
stabilize. Never membership stabilizes separately. This proves kernel L¹
convergence and the fixed-kernel/moving-kernel integral split in the source.

For a moving finite response approaching a retained midpoint, the response
must eventually be the old atom's actual date: there is no other test inside
that atom interval. At every other limiting finite test the mixture atom is
zero, so opponent comparison indicators converge away from a null raw
boundary. The same bounded-kernel argument applies. Never remains a separate
test. Compactness then gives both directions of complete-cap convergence:
moving maximizing tests give the upper bound, approximating any limiting
maximizer gives the lower bound.

Thus the produced laws may be diffuse on a compact ordered calendar, but their
payoff/full-cap pair is the limit of literal actual behavioral pairs. They
are not being identified with a single behavioral profile on natural dates.
Continuous total debt and the actual all-law floor make this a true minimum
of the original semantic carrier. This distinction is sufficient for every
use of the tracked singleton-margin theorem.

The degenerate cases do not break the construction. For c=0 the finite test
is still present and differs from Never against all-Never opponents. For c=1
the last finite test and Never have identical payoff whenever all opponents
stop finitely. An isolated zero-mass finite tester is also possible; it is
not silently converted into an atom.

## Signed transport, cap stability, and the polynomial step

For a reset to an existing own atom, signed legality follows from its positive
own mass; for a conditional reset it follows from its positive normalizer.
Redundant unit-mass directions cause no problem. These are reweightings of old
laws, not insertions of negative probability at unsupported response points.

The retained left and right interval endpoints realize strict-before and
strict-after conditionals. At zero-mass cuts the raw initial-segment boundary
is in E, so approximating old endpoint cuts exist. Their indicators converge
strongly. Normalizers converge to positive values, and all modified densities
remain uniformly bounded on a common small signed box. The old test sets and
comparison kernels still enumerate all original deadlines after reweighting.
Hence the producer's moving-response proof transports the full cap, even
when endpoint reweighting removes some old atoms. It is not a fixed-tester
approximation.

There are exactly two valid stability mechanisms used:

- An isolated unique point has a strict gap on its compact complement. The
  product coupling bound is uniform over all responses and controls
  simultaneous opponent changes.
- For a nonisolated late cap, expansion into a positive multiple of each old
  marginal plus an early signed submeasure makes every term containing that
  submeasure independent of every response above the common cut. Thus all
  upper responses have the same affine transformation with positive slope.
  The compact lower set has the needed separate gap.

In particular the second mechanism applies to Never and to all upper finite
tests, not just to the chosen maximizing responses. It also applies to signed
parameters. No positive complement gap is assumed for a nonisolated point.

Once all caps are fixed on an open signed box, the selected sum F is
multiaffine and equals actual D there. A useful direct proof of constancy is
to average F over the vertices of a sufficiently small centered sign cube.
Its average is F(0), while every vertex is at least F(0). Every vertex is
therefore equal to F(0); the finite sign transform makes every nonconstant
squarefree coefficient zero. This proves the polynomial identity globally
without claiming anything about distant endpoint caps.

## Source identities checked

I reconstructed the following identities rather than assuming them from their
labels:

| Geometry | Valid conclusion at positive global SUM minimum |
| --- | --- |
| Four supported unique caps | Resetting all owners to their cap atoms gives selected endpoint zero, contradiction. |
| Supported earliest group separated from later caps | Positive late masses give a zero selected endpoint; otherwise the sure boundary forces three supported caps at one date and one unsupported later cap, with δ = a_m. |
| Four common unique zero-mixture-mass caps | Conditioning everyone strictly after the cap produces an actual full-cap minimum with every cap equal to its singleton value, contradiction. |
| Common cap with a proper nonempty supported set A | The late conditional endpoint gives δ = C_A. |
| Sole unsupported owner tied with the earliest supported group H | The endpoint gives the individual join δ = J_(m,H), not the sum over every outsider. |
| Sole unsupported owner strictly earliest and isolated | An early conditional endpoint first forces no own mass before t₀. Late mass then gives a passive floor; absent late mass, actual pure play forces either the empty floor or the own-grand gap. |

The sure boundary in the second row is important. A later owner's sure exit
no later than t₀ makes every other response after t₀ tie Never. It forces all
three supported caps to t₀, excludes a second later owner, and forces positive
own mass of the exceptional owner at t₀. All four resets toward this old atom
are consequently legal. The exceptional owner's selected response withdraws
from grand absorption, giving r_m(I∖{m}) − r_m(I).

The third row is the only endpoint that is promoted to an actual minimum.
The promotion is justified. For the final conditionals ν_j=(q_j−E_j)/e_j,
every product term containing an early submeasure exits strictly before every
t≥τ. Its payoff is independent of t, including at τ itself. Positive
rescaling of the original response ordering gives V_i(t,ν_-i)≤s_i on that
entire upper region. Below τ the response is a sole quit with value s_i.
Thus the true full cap is s_i, not merely the displayed value. The selected
sum δ is then the actual sum, and singleton margin gives δ≤0.

In the isolated earliest case I checked the participant-gap pitfall. Equation
(13) alone is only a convex combination of two gaps. If there is late mass,
conditioning it separately gives δ=s_m−r_m(H), a passive floor. If there is no
late mass, the original exceptional law is pure t₀; uniqueness then makes
every supported cap t₀, so the participant coalition is the grand coalition.
This is precisely why the spectrum requires G_m but does not require every
possible participant pair/triple gap.

## Fresh-table comparison and moving minimizing laws

At reward sup-distance e every prescribed payoff and every response payoff at
the same actual profile changes by at most e. Suprema and then infima give
the uniform bounds 8e for D and Δ. This proves continuity independently of
attainment, active-owner choices, or cap-support geometry.

The entire cube therefore has an attained worst SUM value Ω. The ordinary
singleton margin and AllNever competitor give Ω≤4/5<1 whenever Ω>0. The
expanded target was independently checked over all sixteen choices of the
four signs of a_i. There are 82 labelled functionals, and their maximum
coefficient ℓ¹ norm is six. Their possible target values are

    a: {−1,1}; C: {−1,1,4,6}; J: {−1,1,2};
    F: {1,2}; G: {1,2}.

The negative a, C, or J target is incompatible with that label being a
positive contact Ω. At every compatible contact the target is at least one.
For a contact C_A the check uses the whole sum; it does not require all its
old summands to be positive. The intermediate zero in the omitted/grand pair
is essential to the simultaneous withdrawal/join target.

With α=min(1,Ω,σ)/64, the new actual infimum satisfies

    Ω−16α ≤ d ≤ Ω,       d ≥ 3Ω/4 > 0.

Each label moves by at most 12α. Contact labels move strictly above Ω; old
upper noncontacts remain above Ω; old lower noncontacts remain below
Ω−16α because 28α<σ. This compares each new label with the entire possible
new-minimum interval. It covers changes of minimizing owner, support, cap
date, active tester, and attained minimum. No old minimizing profile enters
this step or the subsequent fresh producer.

The signed-eight subtheorem also checks out: absolute withdrawal contacts
move toward two, and old lower absolute values remain below Ω−16α because
18α<η. Optional own-singleton fiber maximization stays in the same Δ interval
and leaves those withdrawal coordinates fixed. It must not be advertised as
preserving own singletons or Γ after that optional step.

## Exact attempted falsifiers and boundary tests

### Positive debt is not a global source

Let every owner's law be (δ_0+δ_Never)/2. Give every passive recipient reward
one, every sole quitter reward one, and every participant in a coalition of
size at least two reward minus one. The marked calendar is
T={1/4,1/2}, c=1/2, with Never separate. Every owner has

    U_i = 1/16,
    V_i(0) = −3/4,
    V_i(any later finite date) = 1,
    V_i(Never) = 7/8.

All four marked caps are unique at the same isolated zero-mixture-mass point
c, and D=15/4>0. Yet the profile with one pure quitter at zero and three pure
Never owners is exact Nash with all prescribed payoffs and caps equal to one;
Δ=0. These values were checked by an exact enumeration of the sixteen
prescribed draws and eight opponent draws. This is a falsifier of the tempting
profilewise version, and confirms that the candidate's global minimum
hypothesis is indispensable. It also checks the separate finite/Never test.

### A nonisolated unique cap moves under an arbitrarily small legal reset

For an observer with singleton reward zero, take two independent opponents
on [0,1] plus Never. The first has density 1/2 and Never mass 1/2; the second
has density t and Never mass 1/2. A third opponent is pure Never. Give the
observer passive singleton rewards +1 for the first opponent and −1 for the
second. Other unused observer entries can be zero. Then

    V(t) = t/2 − t²/2 + t³/12,
    V′(t) = 1/2 − t + t²/4.

The unique finite maximum is τ=2−√2. It is nonisolated, and the complement
has no uniform payoff gap. Reset the first opponent toward its existing
Never atom with parameter λ. The response becomes

    V_λ(t) = (1−λ)(t/2+t³/12) − t²/2,
    V′_λ(τ) = −λ(1/2+τ²/4).

Any sufficiently small nonzero λ changes the maximizing point. The direction
is a legal signed existing-atom reset. Finite grid approximations of these
laws give marked diffuse calendars, up to the monotone quantile rescaling.
This attack does not refute the candidate: its nonisolated stability uses
early submeasures below the cap. The displayed Never reset is a later
replacement, exactly the unconsumed case in Section 9.

### Selected endpoint responses need not be endpoint caps

Against three pure Never opponents and own singleton reward minus one, a
displayed finite response has value minus one, while the true cap is zero
through Never. Consequently a polynomial's distant selected-response value
cannot be promoted to actual debt. The candidate uses its endpoint identities
only algebraically except in Section 7, where the all-test bound was proved
separately above.

### Isolation does not imply mass

The first example has an isolated finite c with zero mixture mass. Conversely
every positive finite atom produced by the quantile construction is isolated
by half its retained interval length. The proof uses the valid direction only.
The case c=1 also makes finite c and Never equal in response value without
identifying the two points; this correctly excludes uniqueness when needed.

## Increment and strategic-input assessment

The incoming condition is no-UE of an arbitrary signed Fin4 reward table. Its
positive-gap witness comes from the tracked semantic equivalence. Finite
minimizing profiles exist by the finite-support approximation; their marked
global minima are produced by compactness and kernel convergence. Every
strategic reweighting used for the geometric identities is an explicitly
realized old-law atom or ordered conditional. The table comparison produces
one positive-gap fresh table before all later geometry requests. No Nash
continuation, credible punishment, maximizing-law witness, or conditioned
minimizing tail remains assumed for the claimed conclusions.

This is therefore an actual source reduction, not an exceptional conditional
certificate theorem. It rules out common unique caps, rules out an entirely
supported earliest group, and rules out every sole-unsupported configuration
except a strictly earliest nonisolated cap, simultaneously at every produced
minimum of one fresh counterexample table. These are definite residual
geometric exclusions beyond the existing compact pair minimum and numerical
margin. They change the surviving counterexample-source obligation; they do
not establish a new raw-table UE existence class.

For clarity, nonnegative debts give

    inf_p max_i d_i(r,p) ≤ Δ(r) ≤ 4 inf_p max_i d_i(r,p).

Their positivity is equivalent, but their minimizing profiles and worst tables
need not coincide. Thus the tracked membership-stretch MAX sources do not
already provide the fresh SUM identities or finite contact avoidance used
here. Nor may the present conclusions be transported back to those MAX
sources without another argument.

### Separately inherited stronger margin

At every produced unit-bounded positive global SUM minimum, the hypotheses of
`positive_minimum_fourPlayer_allOwner_quadraticMargins`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`)
are satisfied with M=1. Hence for every owner, with d_i=B_i−U_i,

    B_i−s_i ≥ d+d²/8,
    U_i−s_i ≥ d−d_i+d²/8 ≥ d²/8 > 0.

These are stronger than the candidate's used singleton margin. At the worst
SUM table they combine with B_i≤1 and AllNever to give

    Ω ≤ 4(1−Ω−Ω²/8),
    Ω²/2+5Ω−4 ≤ 0,
    Ω ≤ √33−5 < 4/5.

The stronger bound is inherited from implemented mathematics, not a new
contribution of this candidate. The existing weaker threshold already makes
every contact target strictly larger than Ω, so no proof step or constant
repair depends on the improvement. The quadratic theorem does not specify
unique maximizing dates, atom support, or the fresh all-minimum cap-order
classification. It can be carried alongside the reduction without confusing
numerical margin with the new geometric increment.

## Conclusion and next requested check

No mathematical objection remains to the frozen three numbered conclusions.
The proof covers the actual whole-behavior infimum, the full moving-response
cap, and every freshly produced marked minimizing law. It does not prove a
uniform-equilibrium payoff, consume multiple caps or several unsupported
owners, or make polynomial endpoints Nash.

The concrete next assembly check is to make “not all four equal” explicit,
retain this ordinary-mathematical status, and obtain the required second
independent review before any export. A mathematical next question is whether
the remaining strictly-earliest nonisolated sole-unsupported case admits a
whole-law repair; the later-reset calculation above shows why isolated-cap
stability cannot simply be reused for it.
