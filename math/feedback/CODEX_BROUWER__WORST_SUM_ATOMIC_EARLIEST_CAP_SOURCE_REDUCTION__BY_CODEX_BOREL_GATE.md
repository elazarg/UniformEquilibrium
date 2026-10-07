# Independent blind review of the worst-SUM atomic-earliest source reduction

## Verdict and review boundary

**PASS, with the scope qualifications below.** I found no unresolved
mathematical objection to the complete source-reduction theorem or the
universal earliest-response restriction. This is ordinary mathematics, not a
new Lean-checked theorem and not a Fin4 uniform-equilibrium theorem.

Reviewer identity: CODEX_BOREL_GATE. I read the complete frozen 920-line
manuscript
`exports/WORST_SUM_ATOMIC_EARLIEST_CAP_SOURCE_REDUCTION.md`,
with SHA256
`1e5c8544ed71e153ee90ae87ac72b8413153e29faa43460599f1ac510e0b6e83`.
I did not read prior feedback or another reviewer's verdict before forming
this verdict. I checked the hash again after the mathematical review.

I read the root and mathematical `AGENTS.md`, `SOURCES.md`, `GOAL.md`,
`exports/README.md`, and both required research-method documents. I used the
semantic-waist section of `docs/FRONTIER.md` and the membership-stretch and
minimum-debt sections of `docs/TOOLKIT.md` to select the bounded source audit.
No Lean build, Lean file edit, export, staging, commit, or push was performed.

## Exact claim checked

There are four owners I={0,1,2,3}, with sixty real rewards r_i(S), one for
each owner and nonempty S⊆I. All-Never pays zero. Each owner independently
uses an arbitrary probability law on ℕ⊔{Never}; the first finite stopping
date and its tied coalition determine the terminal reward. A unilateral
deviation replaces that owner's complete law, equivalently its complete
behavioral strategy. The cap includes every natural-number deadline and
Never, with no controller or response-menu restriction.

Write U_i for prescribed terminal payoff, V_i(t,p_-i) for the pure-response
payoff, B_i=sup_t V_i(t,p_-i), D_r(p)=Σ_i(B_i−U_i), and
Δ(r)=inf_p D_r(p), over all such actual independent laws.

The main quantified claim is:

    If some signed Fin4 reward table has no uniform-equilibrium payoff,
    there exists one table r̂∈[−1,1]^60 with d=Δ(r̂)>0 such that,
    for every finite-law sequence with D_r̂(p^k)→d,
    and every subsequence satisfying the Section 3 convergences,
    its produced marked minimum q has one of the following alternatives.

Either some cap has at least two distinct maximizing points of
X=T⊔{Never}; or all four maximizing points τ_i are unique, are not all
equal, and at least two owners satisfy q_i({τ_i})=0. In the latter
alternative τ=min_i τ_i is finite, has positive average-law point mass,
and is isolated in T. Some owner whose own cap is τ has zero own mass
there. Unique cap dates need not be pairwise distinct.

The additional universal statement is about any bounded signed table and
any Section 3 produced positive global SUM minimum, with no uniqueness
assumption. Its earliest active point is finite. If its mixture mass is
zero, some prescribed owner stops strictly earlier almost surely, and
each other owner's cap is attained at τ, c, and Never, with c and Never
distinct and τ possibly equal to c.

These are statements about produced marked sources and their complete
payoff/cap pairs in the original attainable closure. They do not identify
q with an actual natural-number profile, classify every arbitrary abstract
compact law, or transport the old minimizing profile to the new table.
The fresh table is selected before any fresh sequence, cap family, or owner
geometry. Existence of such a fresh counterexample table is the quantified
conclusion; a pointwise restriction on every original table is not claimed.

## Source and implementation audit

All named source files below were verified to be tracked with `git ls-files`.
Declarations were inspected under their actual file imports. This was a
static source audit, not a new compiler check.

- In `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`,
  I inspected
  `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff`,
  `quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`,
  `quittingBehaviorStoppingLaws_stoppingLawProfile`,
  `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`,
  and
  `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`.
  They cover both directions of law/behavior realization and the unrestricted
  replacement cap. Reduction of that cap to pure deadlines follows directly
  by bounded expectation: every replacement-law payoff is an average of
  pure-response payoffs, and each pure response is itself a legal law.
- In `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`,
  `HasTerminalExploitabilityGap` quantifies over every behavioral profile
  and allows a complete behavioral replacement. I inspected
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`.
  Its hypotheses match Section 2. The original one-date convention is not
  changed by working with terminal payoffs.
- In `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`,
  I inspected `quittingTerminalSemanticPair`,
  `quittingTerminalSemanticDebt`, `quittingAttainableTerminalSemanticPairs`,
  `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`, and
  `quittingTerminalSemanticCarrier_isCompact`. The carrier is exactly the
  closure of actual behavioral prescribed-payoff/full-cap pairs, in that
  order. Section 3's convergence therefore supplies the needed membership.
- In
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`,
  I inspected `minimumTerminalSemantic_singletonMargin` and its actual
  imports. Its displayed hypotheses are carrier membership, global
  minimality of total debt over that carrier, and strict positivity. It
  concludes δ≤B_i−r_i({i}) for every owner. It does not require an assumed
  Nash tail, cap attainment in ℕ, reward signs, or singleton normalization.
- In `UniformEquilibrium/Quitting/Terminal/TerminalExploitability.lean`,
  `quittingTerminalExploitability_eq_max_debt` identifies the existing
  exploitability objective with MAX debt. In
  `UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`,
  `quittingTerminalExploitabilityInf` is the all-behavior infimum of that
  MAX objective.
- I inspected
  `exists_maximum_quittingTerminalExploitabilityInf_unitReward` and
  `exists_membershipStretch_singletonFiber_source_of_positiveInf` in
  `UniformEquilibrium/Diagnostics/Quitting/MembershipStretchWorstTableSource.lean`,
  and
  `exists_membershipStretch_source_opposedReversals_of_no_uniformPayoff_finFour`
  in
  `UniformEquilibrium/Diagnostics/Quitting/MembershipStretchOpposedSource.lean`.
  These select MAX-debt sources and, in the last theorem, impose actual
  three-sure-root conditions. They do not assert the SUM value separation,
  the all-moving marked-source cap geometry, or the earliest zero-mixture
  exclusion proved here.

I also inspected the target description in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean` and the policy in
`Literature/README.md`. There is no paper-derived theorem needed for this
manuscript's proof. A narrow search in the selected path/root and
membership-stretch/minimum-semantic source neighborhood did not identify an
implemented version of this complete reduction. I do not infer a global
implementation census from that search.

## Actual producer, signed transport, and all moving tests

Section 3's construction survives the main attempted falsifier: a response
date may move with k, be empty in the prescribed law, or escape to arbitrarily
large original dates. The argument retains the entire finite tester set
T_k, including the final finite cut c_k, separately from Never. A finite law
has only finitely many distinct response values even though every original
deadline is permitted. Thus original cap maximizers can be extracted, and
Hausdorff approximation supplies the reverse cap inequality.

The censoring argument first proves equality of the actual and finite-law
infima. Its opponent coupling bound is uniform over every replacement test;
it is not merely prescribed-payoff continuity. Consequently the minimizing
sequence used in the marked construction exists without a strategy witness
being supplied as an extra hypothesis.

The endpoint set E and tester set T have different jobs. A positive finite
mixture atom comes from an open component (a,b) of the complement of E.
On a compact subinterval inside that component, old endpoints are eventually
absent, so a single old atom contains it. Endpoints of this old interval
converge to a and b, and the only tester inside it is its midpoint. This
proves isolation, rather than assuming that arbitrary point masses are
isolated. Points of E not in T form a null set by the stated countable
component argument, so the collapse map defines laws on X almost everywhere.
In particular the final finite cut c has zero mass, even though it is a
retained test point.

The product weak-* assertion must be read as the tensor product
∏_i f_i^k(u_i) on [0,1]^4, with independent raw coordinates. Under that
interpretation it is valid: rectangle integrals factor, rectangle tests are
dense in L¹, and densities have a common bound. It would be false for an
uncontrolled product of weak-* limits at the same raw coordinate; the
manuscript's independent-coordinate construction does not make that mistake.
Kernel convergence is also justified. Apart from raw diagonal and retained
endpoint null sets, two coordinates lie in one persistent atom interval or
have a limiting endpoint strictly between them. Exact ties and strict order
therefore stabilize, including Never membership.

The same dichotomy handles every moving pure response. A limit at a retained
midpoint forces the corresponding old atom test eventually. At every other
limit point, the mixture has no atom, so opponent comparison kernels converge
almost everywhere. This is sufficient for both cap inequalities and for
continuity of the full response function on T. Never is an isolated separate
test. The extra formal c⁺ duplicates c only when laws retain zero mass at c;
it is not a second point counted by the cap-uniqueness conclusion.

Section 4 supplies actual signed finite-law realizations, not just formal
affinity. For an existing own atom of mass m>0, legality reduces to
m+λ(1−m)≥0 and 1−λ≥0. For a conditional event of mass e>0, the
two likelihood factors are 1+λ(1/e−1) and 1−λ. A common small open
box is legal after the finite normalizers converge. Atoms of mass one and
events of mass one merely give redundant limiting directions.

Strict cuts through supported clocks use the appropriate retained interval
endpoint; zero-mass cuts use converging old endpoint cuts. All finite
conditions are unions of whole old calendar atoms. Their indicators converge
strongly in L¹, so the density calculation remains bounded and weak-*
convergent for negative as well as positive parameters. Old prescribed and
moving-response kernels stay unchanged. This places the complete modified
pairs, including full caps, in the original carrier and proves D_X(q^λ)≥δ.
The chart is a deterministic coordinate representation, not public shared
randomness.

## Cap stability and selected polynomial endpoints

The two stability arguments cover different cases correctly. A unique
isolated maximizer has a complement gap by compactness. A unique
nonisolated maximizer has no such automatic gap, but early-submeasure
expansion gives one common identity

    V_i(t,q_-i^λ)=k_i(λ)V_i(t,q_-i)+C_i(λ), k_i(λ)>0,

for every upper test, including Never. Terms containing an early
submeasure stop before the response, so their payoff is independent of it.
A lower compact-set gap excludes new lower maxima. This is an actual
full-cap argument; checking one displayed response would not suffice.

On a legal signed box with these cap values fixed, the independent-law
selected debt sum is multiaffine and equals actual D_X≥δ. The
interior-minimum principle is valid. One direct verification is that the
average of its values on a centered sign cube equals its value at the
center. Every corner is at least that value, so all corners equal it;
the Walsh coefficients then force every nonconstant squarefree coefficient
to vanish. This argument also covers redundant directions.

Constancy yields selected all-one identities only. The distant endpoints
may have other profitable responses and greater actual debt. Sections 6,
8, and 9 use precisely the selected identities; none asserts actual Nash
or global minimality of those endpoints. Section 7 separately proves the
actual endpoint caps before claiming a new minimum.

## Earliest zero-mixture restriction, including multiple active branches

I checked Section 7 with potentially infinite and nonisolated active sets.
If Never were the earliest active point, every active set would be the
singleton {Never}. An owner with zero Never mass makes c and Never tied
caps for every other owner; positive Never mass for all four instead permits
the four-supported reset. Both contradict positive minimality as claimed.

At a finite zero-mixture earliest point τ, the no-final-late branch is real:
if e_h=q_h(clock>τ)=0, then q_h(clock<τ)=1. Every other response
t≥τ sees h stop first, hence has a test-independent payoff. Each other
owner has an active point in this upper family, so τ,c,Never all maximize
its actual cap. No replacement of h by a pure early clock is licensed or
needed.

For the remaining case e_i>0 for every owner, fix each preceding cut u_n.
Every original active point lies above u_n. The positive affine upper-family
identity preserves all of those active points and their ties simultaneously,
while a compact lower gap excludes every lower competitor on a sufficiently
small signed box. Thus F_n really equals full D there even with multiple
active branches. Dependence of the box on n causes no problem: polynomial
constancy is obtained separately for each n.

The final strict-late laws ν_i=q_i(·|clock>τ) are directly realized on
the old null boundary because min_i e_i>0. Also ν_i^n→ν_i in total
variation. This establishes carrier membership and passes the selected
identity to the final endpoint; it does not yet establish minimum debt.

The closed-upper-family formula does the necessary remaining work. With
E_j=q_j|_(clock<τ), each nonoriginal opponent-product term stops
strictly before every t≥τ, including τ itself. Hence all upper
responses are positively rescaled original responses plus one constant.
An original active τ_i remains maximal among all upper tests. At τ,
conditioned opponents are strictly later and the response pays s_i;
every lower finite test also pays s_i. Therefore those lower tests cannot
exceed V_i(τ_i,ν_-i), and Never is already in the upper family.
This proves all four actual full-cap equalities. An earliest owner m has
B_m(ν)=s_m, whereas distinct later owners may have larger caps.

Only now does the selected identity imply actual D(ν)=δ. Carrier
membership gives true global minimality, and the checked singleton margin
then gives δ≤B_m(ν)−s_m=0. This excludes the all-positive-final-late
zero-mixture case without silently asserting that every later cap is a
singleton payoff. I found no missing cap branch at this seam.

## Geometry spectra and one-table contact avoidance

The supported earliest-group argument has the required sure boundary.
If all later owners have strict-late mass, its selected endpoint has zero
sum. Otherwise some later owner stops no later than the earliest supported
cap surely. Uniqueness forces every supported cap to that earliest date,
forces positive own mass of the exceptional owner there, and rules out a
second later-cap owner by its tie with Never or c. Resetting all four old
positive atoms produces exactly the selected LC identity
δ=r_m(I∖{m})−r_m(I), without claiming pure-grand Nash.

The common-cap argument yields C_A with a proper nonempty supported set.
It permits signed individual join contributions. For a sole unsupported
owner, the later case is LC, and the earliest tie gives the individual
J_(m,H), rather than the generally different aggregate C_H.

In the strictly earliest case, isolation is supplied by Section 7. A
positive early conditional mass would give a zero selected endpoint, so
q_m(clock<t₀)=0. A genuine strict-late mass then gives a passive-floor
identity F_(m,H). If no strict-late mass exists, m is actually pure at
t₀; uniqueness makes all three supported caps equal t₀, yielding the
own-grand identity G_m. When t₀=Never, the identity is s_m=F_(m,∅).
This covers the absence-of-late-mass case without substituting arbitrary
participant pair/triple gaps into the passive-floor spectrum.

The fresh-table comparison uses SUM throughout. The pointwise all-response
reward bound gives |Δ(r)−Δ(r′)|≤8‖r−r′‖∞, hence the worst SUM table
r* exists on the closed cube. Singleton margin at its produced minimum,
together with the actual AllNever competitor, proves Ω≤4/5<1. This
threshold supplies the strict contact target; no MAX minimum is transferred.

The endpoint R assigns every coordinate exactly once. For an Ω contact,
its finite target values are:

- a_i: 1 at a positive contact;
- C_A: 6 for |A|=1, 4 for |A|=2, and 1 for |A|=3 at a positive
  contact, where C_A=−a_i;
- J_(i,K): 2 for |K|=1 or 2, and 1 at a positive |K|=3 contact;
- F_(i,K): 1 for K=∅, 2 for |K|=1 or 2, and 1 or 2 for |K|=3;
- G_i: 1 or 2.

The intermediate zero in omitted-triple/grand coordinates makes the
opposing positive a_i and −a_i contact requirements compatible. I ran an
exact rational enumeration of all sixteen row-sign patterns: each specified
sixty coordinates and eighty-two labels; all 1,216 sign-compatible positive
contact cases had target value at least one. The finite case calculation
above is the proof, not reliance on that computation.

The noncontact separation σ is taken over the whole finite labelled family,
not a selected owner. Every label moves by at most 12α, while the actual new
infimum lies throughout [Ω−16α,Ω]. With the stated α, old lower labels
stay below that entire interval, upper labels stay above it, and contacts
move strictly above Ω. Consequently d avoids all new labels for every new
minimizer. This uses both worst-table optimality and full-law Lipschitz
continuity. The table direction is fixed before fresh minimizing laws are
chosen.

The separate eight-coordinate subtheorem preserves singletons only during
its stated perturbation. An optional own-singleton fiber reoptimization keeps
a_i fixed but can change the old singleton values and Γ. The expanded
eighty-two-label construction starts again at r*, changes singletons, and
does not inherit that preservation or a subsequent fiber-reoptimization
claim. These distinctions are explicit and correct.

## Exact attempted falsifiers and boundary checks

The membership-reward table r_i(S)=1_{i∈S} checks both uses of positivity.
Pure date-zero play has D=0 with unique supported caps. Independent half
date-zero/half Never laws have U_i=1/2, B_i=1, hence D=2, while the joint
old-atom reset with λ=1/4 gives D=3/2. A positive displayed debt therefore
does not supply the global floor needed by the polynomial argument. The
same profile has MAX debt 1/2, explicitly separating SUM from MAX.

Negative parameters are actual probabilities. For an event of mass e=1/4
and λ=−1/4, the conditional direction gives event mass 1/16 and
complement mass 15/16. For a supported atom of mass m=1/3 with the same
λ, the target atom has mass 1/6 and its complement mass 5/6. These
tests verify the signed directions rather than appealing to a forward
mixture theorem.

The all-zero table with all-Never laws has T={c=0}. Both c and Never
maximize every cap, c has zero mixture mass, and every strict-late mass
is positive. Its δ is zero, so singleton margin gives no contradiction.
This is the exact boundary of Section 7's positivity use.

I independently recomputed the no-final-late example. With all own
singletons zero, passive singleton {0} paying one to each i≠0,
singleton {1} paying one to owner 0, and all other entries zero, the
specified two consecutive uniform finite menus give
U=(0,1,1,1), B=(1,1,1,1), D=1. The actual unrestricted gap is zero
because AllNever has zero debt. In its limit the earliest active point is
τ=1/4, owner 0 is strictly earlier almost surely, and every other cap
includes [τ,c] and Never.

This example also falsifies a tempting strengthening: e_0^n>0 at every
preceding cut does not imply e_0>0 at the final cut. Conditioned owner-0
densities grow like 1/e_0^n and concentrate toward τ. For every n, a
different recipient responding at τ receives one because owner 0 has
already stopped. In the proposed weak limit that inserts δ_τ, the same
response ties owner 0 and receives zero. Thus a new atom at the old
nonisolated point would destroy fixed-response convergence. The manuscript
explicitly declines that invalid limit and retains the sure-early exception.

No step converts zero own point mass into zero mixture mass. The source
construction establishes that positive mixture atoms are isolated; that
fact is not true for arbitrary abstract compact laws and is not assumed
outside the producer. Later zero-own-mass caps can still be nonisolated.

## Conjecture-facing increment and remaining qualification

The input-to-output chain has no unproduced strategic witness: original
no-UE gives a full behavioral terminal gap; bounded normalization gives a
positive SUM infimum; compact SUM reward selection and the fixed finite
contact perturbation give one positive fresh table; arbitrary finite
minimizing sequences then produce marked global sources with full caps;
the geometric identities exclude common unique caps, LC, a sole unsupported
owner, and an all-unique zero-mixture earliest point at that same table.

This is a concrete reduction of the existential counterexample obligation:
if a Fin4 counterexample exists, a bounded counterexample exists whose every
produced minimum has the stated multiple-cap or multi-unsupported atomic
earliest geometry. Conversely, a positive Δ at that fresh table already
implies no UE through the original terminal-gap bridge. The additional
strategic information is the restriction on every produced minimum, not a
new reward-table UE existence class.

The inspected MAX source selections do not provide this SUM restriction.
The result is therefore more than a verifier for a supplied continuation
or a relabeling of those named interfaces. This gives a legitimate
conjecture-facing reduction for the export gate, subject to its remaining
independent-review and packaging requirements. This review itself neither
places a packet in `exports/` nor supplies L, A, or C evidence.

Multiple-cap sources remain open. All-unique sources with at least two
zero-own-mass owners remain open, including cases where an owner with a
later cap supplies the earliest mixture atom. No equilibrium, positive-gap
example, raw-table classification, pairwise-distinctness theorem, or complete
UE strategy-class theorem follows from this PASS.

Concrete next question: can the surviving all-unique atomic-earliest source
with at least two zero-own-mass cap owners be repaired by legal old-calendar
whole-law changes while controlling every full cap? No such repair is used
or proved in the reviewed reduction.
