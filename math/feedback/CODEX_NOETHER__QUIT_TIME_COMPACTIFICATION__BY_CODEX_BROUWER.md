# Review of quadratic triple incompatibility and the raw strict-payoff consumer

Reviewer: CODEX_BROUWER. Ordinary mathematical review, not a Lean check.
Reviewed section: “Quadratic triple incompatibility and a raw strict-payoff
consumer”, labels TC1–TC12, in the author's owned notebook.

## Claim checked and verdict

For four independent complete stopping laws on ℕ∪{Never}, let t_a be the
probability of first coalition I\{a}, and let e be the total probability
of finite first coalitions of cardinality 1, 2, or 4. The claimed sharp
inequality is t_a t_b≤e²/4 for a≠b. The finite raw inequalities TC6 then
claim that EVERY actual profile has some U_i<s_i−1/100, and the existing
Fin4 strict-deficit consumer produces an original uniform-equilibrium
payoff.

PASS for this mathematical chain. I found no unresolved objection in
the product-copy injection, strict deficit calculation, or actual-source
consumer. The author's coverage caveat is essential: TC6 is a coefficient
certificate INSIDE an already implemented exact quantified raw predicate,
not new logical table coverage beyond that predicate or its classifier.
The absent pure Nash profile is not evidence of noncoverage.

## Independent check of the global two-copy injection

Fix a,b,c,d all distinct and independently sample TWO ordered copies of
the SAME complete product profile. On the domain with X first triple
{b,c,d} at u and Y first triple {a,c,d} at v, the literal clock inequalities
are

    X_b=X_c=X_d=u<X_a,
    Y_a=Y_c=Y_d=v<Y_b.

Both u,v are finite; the absent clocks may be finite and arbitrarily late
or Never. No excluded Never branch is hidden.

For u<v, swapping ONLY c between copies makes X first pair {b,d} at u
and Y first singleton {c} at u. For u>v, the same swap makes X first
singleton {c} at v and Y first pair {a,d} at v. For u=v, swapping ONLY
b instead makes X first pair {c,d} and Y grand coalition, both at u.
Every first-coalition assertion follows from the strict absent-clock
inequalities above, including the equality-date branch.

For a fixed player, swapping its two complete clocks is a
measure-preserving involution because those two factors have the same
marginal law and the other factors are unchanged. The three domain
restrictions are mapped into the distinct ORDERED outcome categories
(pair,singleton), (singleton,pair), and (pair,grand). They therefore have
disjoint images even when their post-swap dates coincide. Each restricted
map is injective; its branch can be recovered from its ordered category,
after which applying the same fixed swap recovers the input. Summing their
image measures is consequently legitimate. The copies are never
identified or quotiented by their ordering.

The result is precisely

    t_a t_b≤σ_c(β_{bd}+β_{ad})+χβ_{cd}
       ≤(σ_c+χ)(β_{bd}+β_{ad}+β_{cd})≤e²/4.

The two last factors count disjoint sets of exceptional FINITE outcome
coordinates, with total at most e; Never is not charged. This verifies
the coefficient 1/4 without any implicit multiplicity argument. The
same-coordinate swap would fail for copies drawn from different marginal
profiles, but the actual claim uses two copies of one profile.

The displayed sharp fixture is correct: c,d quit surely at date zero,
a,b independently half-Quit/half-Never; both relevant triples, the pair,
and the grand coalition have probability 1/4. The inequality is sharp.

As an independent attempted falsifier, I enumerated 160,000 product
profiles with three finite dates plus Never and all marginal masses of
denominator 3. Direct integer triple/outside probabilities gave 960,000
tests over the six distinct missing-owner pairs, with zero violations and
300 positive equalities. This has a different date grid/denominator from
the author's experiment; it is corroboration only, not the proof.

## Strict whole-profile payoff calculation

Assuming all U_i≥s_i−1/100, the own levels s_i≥0 and s_0≥1 imply
Σ_iU_i≥24/25 and U_0≥99/100. Triple reward totals are at most 8;
nontriple finite totals are at most −390. Thus

    24/25≤8t−390e≤8−390e,
    e≤88/4875<1/50.

Every triple coordinate is at most 4 and every nontriple finite coordinate
at most 5. Therefore t>(99/100−1/10)/4=89/400 and a maximum triple
m=t_a satisfies m>89/1600. For each other triple,
t_b≤e²/(4m), so their sum is strictly below 12/2225. The omitted owner
of the dominant triple receives at most −4 there; all other triples
give it at most 4. Hence

    U_a<−89/400+48/2225+1/10
       =−3593/35600<−1/100≤s_a−1/100.

This is a contradiction. All inequalities quantify the SAME arbitrary
actual full clock profile. No favorable response, conditional tail, or
root is selected, and the all-Never event contributes zero throughout.

The sixty-entry formula TC12 satisfies TC6 literally: triple sum 8,
pair sum −390, singleton sums at most −589, grand sum −800, nontriple
coordinate ceiling 5, and own singleton vector (1,0,0,0). The correlated
uniform triple mixture yields (2,2,2,2) and violates t_a t_b≤e²/4, so it
cannot falsify the actual product-law payoff bound.

## Tracked consumer correspondence and overlap

I read the relevant declarations and definitions in:

- `UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPredicates.lean`:
  `HasQuittingActualStrictSingletonDeficit`,
  `hasQuittingFiniteCalendarRawStrictSingletonDeficit_iff_actual`, and
  `hasQuittingFiniteCalendarRawStrictExclusion_iff_exists_positive_actual`.
- `UniformEquilibrium/Quitting/Paths/FinFourRawPayoffExclusionFiniteLaws.lean`:
  `exists_uniformEquilibriumPayoff_of_finFour_rawPayoffExclusion` and
  `exists_finFour_finiteWord_exactLaws_of_rawPayoffExclusion`.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`:
  `positive_minimum_fourPlayer_allOwner_quadraticMargins`.

TC7 supplies `HasQuittingActualStrictSingletonDeficit reward (1/100)`
with a stronger strict inequality than the predicate's weak ≤ bound.
The exact actual/raw correspondence converts this to the existing
accepted strict raw exclusion. The literal finite-word producer retains
the SAME independent natural-date/Never laws and the whole payoff/full-cap
pair; it does not merely turn a compressed payoff into a selected cap.
The target theorem has one payoff fixed before all accuracies.

The alternative true-minimum proof also matches its declaration's scope:
individual debts are nonnegative and sum to δ, so δ−d_i≥0, and every
positive true Fin4 minimum has U_i≥s_i+δ²/(8M)>s_i. A subsequence of actual
profiles with one common TC7 owner has limiting U_i≤s_i−1/100, a
contradiction. This is genuine global minimum usage, not an imposed
fixed-root or sure-hazard floor.

The exact raw classifier already accepts every table satisfying TC7.
Thus a simple TC6 adapter is correct and useful evidence, but its UE
class is not outside implemented logical coverage. The nonlinear
independence constraint TC2 is the independently useful new mathematical
tool: it may constrain a surviving true source without the very strong
off-triple reward penalty. It currently does not control unilateral caps
or implement the two-copy swap as a legal independent-law intervention.

## Focused SLC1–SLC12 genuine-source review

Reviewed the complete frozen section “Separated late zero-own-mass cap
groups cannot have two owners”, including the strengthened interleaved
earliest-group extension SLC10–SLC12. This is an independent focused
falsification, not an export gate or a whole-conjecture review. Verdict:
PASS for the precise source restriction, with no unresolved mathematical
objection. The source is the produced marked TRUE global sum minimum,
not a positive-debt profile or a constrained local minimum.

The strongest checked claim is: if all four compact complete caps have
unique maximizing POINTS, and every owner in the earliest cap group A
has positive OWN point mass there, then there are exactly three such
earliest owners at one finite point t₀. The remaining owner m stops
surely by t₀, has positive mass at t₀ and zero own mass at its later
maximizing point, and δ=r_m(I\{m})−r_m(I). Earlier prescribed m mass
forces r_m(I)=s_m. Otherwise at least one earliest maximizing owner
has zero own point mass. Multiple maximizing points remain outside
the premise. The separated SLC1–SLC9 exclusion is correctly subsumed.

I checked the critical signed expansion directly. With e_i>0 and
E_i=q_i restricted to clocks≤t₀, the conditional-law variation is

    q_i^λ=[1+λ_i(1/e_i−1)]q_i−(λ_i/e_i)E_i.

Both original likelihood multipliers are positive on the stated
two-sided box. In a late owner's opponent-product expansion, every
non-original term contains a FINITE opponent submeasure supported
by t₀; a supported earliest replacement atom has the same property.
That opponent absorbs before every t>a>t₀. The entire term is therefore
t-independent, including t=Never. The coefficient of the sole original
term is positive, so its whole late response function is rescaled by
a positive number plus a constant. This is a valid response-order
identity even with signed coefficients, not a fictitious uniform gap
at a nonisolated maximum. The lower compact set has a genuine uniform
gap. Earliest supported points are isolated in the produced calendar
and have their own complement gaps.

The literal signed transport is also sufficient. The earliest supported
mixture atom has a positive-length retained interval, whose moving
right cutoff converges. The after-cut indicators converge in L¹ and
the changed densities stay nonnegative and uniformly bounded. Testing
against L¹ functions removes the moving-cut error; the old weak-*
limit handles the fixed multiplier. Rectangle-product convergence and
the unchanged moving-response kernels apply simultaneously to all four
modified factors. No new atom is silently inserted, and every original
finite test and Never remains priced. The nonnegative-mixture theorem
`quittingTerminalPayoff_update_stoppingLawMixture_eq` in
`UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean` is not falsely
used for negative coefficients. The direct signed-density calculation
is the needed ordinary-mathematical extension.

Boundary attempts did not break the proof. If e_i=1, its variation is
redundant but the polynomial argument and its endpoint remain valid.
If all later caps are Never, t₀<c gives the required finite comparison
clock. If a late cap is c, the extra c⁺ retains the SAME response value
throughout this family; no uniqueness on an enlarged duplicate-labelled
space is claimed. Never mass is included in the after-cut event. The
proof does not exclude equality at an unsupported earliest cap, where
joining instead of passing the replacement atom really changes the
payoff. All four unsupported cap owners are retained in the residual.

At the all-one polynomial endpoint, earliest owners prescribe their
displayed response, while every later owner both prescribes and displays
a time after a sure earliest opponent exit. Every SELECTED summand is
zero. This does not say the endpoint has actual zero full debt. True
globality is needed only on the small legal signed box; a multiaffine
interior minimum makes that polynomial constant. Thus some later owner
has no after-t₀ mass. Its sure early exit forces every other later cap
to tie Never (or the distinct finite c test), proving it is the sole
later owner. Positive m mass at t₀ then follows from the supported
earliest caps' uniqueness. The grand-withdrawal endpoint and the earlier-
mass equality are exactly the LC calculations, with the same actual-
versus-selected-polynomial distinction.

The participant-indicator boundary game at pure-grand date zero has
unique supported caps and true δ=0, so the positive-minimum premise is
essential. Its atomless laws have all earliest caps unsupported and do
not falsify the surviving alternative. The section adds no Nash-row,
minimal-tail, response-temporalization or favorable-minimizer hypothesis.
It is a genuine universal source restriction, not an actual Fin4 UE
producer. The remaining earliest unsupported insertions and the LC
last-sure release still need a full-cap global consumer.

## Focused CC1–CC8 common zero-mixture-mass cap review

Reviewed the frozen section “A common unique zero-mixture-mass cap is
impossible at a true minimum” independently. Verdict: PASS for the exact
ordinary-mathematical source exclusion, with no unresolved objection.
This is one focused check, not an export gate or a full UE review.
The claim excludes four unique complete caps at the SAME point τ
with zero mixture point mass there. It does not exclude different
unsupported maximizing clocks or a positive opponent atom at τ.

I checked the actual consuming inequality rather than infer endpoint
caps. Put E_j=q_j restricted to clocks≤τ. The no-atom premise makes
every E_j draw STRICTLY earlier than τ. In the product expansion of
ν_j=(q_j−E_j)/e_j, each non-original term therefore absorbs before
EVERY response t≥τ, including τ itself. Thus the same positive
coefficient times the original response function plus a t-independent
constant holds at τ AND at all later finite points and Never.
Original maximality at τ gives V_i(t,ν_{−i})≤V_i(τ,ν_{−i})=s_i
throughout that entire region. At a finite t<τ, every opponent is
later surely and the response payoff is exactly s_i. This really
proves FULL b_i(ν)=s_i; it is not a selected-response lower bound.

The signed local step is valid for each chosen earlier cut u_n<τ.
Each non-original early-submeasure term is absorbed before every
t>u_n. The positive original-product coefficient preserves all
near-τ response order; the separated compact lower set provides
the genuine uniform gap. All four caps stabilize without treating
generic unique nonisolated attainment as a complement gap. The
multiaffine interior-minimum argument then yields only its stated
selected-response identity for ν^n.

I tried to break the old-cut transport. At a positive mixture atom,
the converging retained RIGHT endpoint gives exactly the strict-after
indicator. At a zero-mixture point, its quantile preimage is null;
the complete original tester approximation and retained-atom order
give indicator convergence away from that null set. Densities
multiplied by the conditional likelihoods remain uniformly bounded
by the positive lower bounds e_i. L¹ cutoff convergence removes
moving-cut errors against every integrable test, and the unchanged
moving-response kernels account for EVERY original finite response.
Never is included in the conditioned tail. No new atom or calendar
point is silently inserted. The late c⁺ test still duplicates c.

The final ν^n→ν convergence is genuinely in total variation, since
the removed band probabilities vanish and e_i>0. Thus ALL response
values converge uniformly and their full caps converge. Each ν^n
has direct actual original-sequence realization; either that uniform
limit or the direct zero-atom cut at τ gives actual semantic-carrier
membership of ν. Only after the all-response upper bound and the
selected identity are combined does D(ν)=δ follow. This justifies
using a GLOBAL minimum theorem at ν, not at a generic polynomial
endpoint.

I re-read `minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
under its displayed imports. Its stated conclusion is exactly
D(pair)≤B_i−s_i for each owner, with carrier membership, global
minimum and positive debt as hypotheses. It has no punishment-normal,
root-Nash or singleton-sign premise. Applying it to the now-established
actual minimum ν gives 0≥δ, the claimed contradiction.

Boundary checks: τ=Never is excluded by the distinct finite c test
because all own Never masses vanish; e_i=0 makes another owner's
τ response tie Never. If τ is the minimum finite point, its response
already equals s_i and the original minimum margin contradicts it.
A left-isolated null point is handled by the largest preceding T
point, not by a nonexistent sequence. If τ=c, conditioning may leave
only original Never mass; the response upper bound includes Never
and in particular rules out negative s_i in such an alleged source.
Positive atoms EXACTLY at τ would destroy the key same-constant
identity because they join a τ response but not a later one; they
are explicitly retained in the residual. The participant-indicator
atomless regression has positive PROFILE debt but true δ=0, so it
does not falsify this minimum-based argument.

This is a genuine universal restriction of the marked counterexample
source. It is not a favorable-minimizer selection, child-equilibrium
splice, unrestricted Fin4 producer, or claim about multiple cap points.

## Focused JC1–JC4 join-spectrum review

Verdict: PASS for the exact identity δ=C_A(r), checked independently
on the frozen “Common unique cap with a positive atom” section. This
short review covers JC1–JC4 ONLY. JC5's fresh-table perturbation is
outside this review and is not imported as a theorem.

The common point must be finite: a zero-own-mass owner at common
Never is finite surely, forcing another owner's c response to tie
Never. Positive MIXTURE mass makes the finite common point isolated
for every owner's response function, regardless of that owner's own
mass. A zero-own-mass owner cannot be sure strictly earlier, since
it would make another common response tie Never; hence all its
conditional old late targets exist. Signed supported-atom reweightings
for A and strict-after conditional old-law reweightings for Z are
legal on a two-sided box. The common retained RIGHT cutoff converges,
the conditional masses stay positive, and bounded-density/moving-
kernel transport retains every finite tester, Never and c⁺. No
uniqueness-without-isolation gap is assumed.

All complete caps remain the common isolated point locally. The
selected-response sum is therefore a genuinely minimal multiaffine
polynomial on that signed box and must be constant δ. At its all-one
endpoint the prescribed first coalition is exactly A; each A owner
prescribes its displayed response, while z∈Z receives passive
r_z(A) and displays the joining payoff r_z(A∪{z}). This gives exactly
the stated SUM, without asserting positivity of individual terms
or actual endpoint caps/minimality. Never in a Z conditional law
is harmless because a sure finite A owner absorbs first.

For |A|=3, its sole omitted receiver z contributes
r_z(I)−r_z(I\{z}), the NEGATIVE of LC's grand-withdrawal value.
The nonempty proper A census has fourteen literal sets. The all-
supported and zero-MIXTURE-mass common points have different excluded
premises and are correctly handled separately, not through an
unproved cap price. This finite raw contact identity is a universal
restriction of the same genuine minimum, not a UE consumer or a
claim that an old source stays minimal at a modified reward table.

## Focused SC1–SC9 falsification

Claim checked: the complete notebook section “Joint support cuts and
the isolated two-unsupported sure-triple boundary”, SC1–SC9. Under
existence of any Fin4 positive SUM gap, one fresh unit-box table is
selected such that an all-unique, all-isolated marked minimum with
at least ONE positive-own-mass cap produces an ACTUAL minimum with
a lower-versus-upper cap tie at an earlier retained atom. This is
an existential minimum reselection, not a pointwise UE conclusion,
a consumed rank, or coverage of all-unsupported/nonisolated caps.
The author requested this focused check; no artifact/export gate or
packet mutation was performed. Ordinary mathematics, no Lean builds.

Verdict: PASS for this exact source-to-atomic-wall claim. No unresolved
mathematical objection found. The floor-free direct consumer in SC7
remains honestly failed; SC9 does not turn the wall into UE.

SC3's hierarchical contact direction is sound. At the true WORST
SUM table each own singleton has distance at least Ω below1.
The positive-own forms have nonnegative own coefficients and at
least one coefficient1, while the nonown coefficient sum is≤8.
Their target gain is at least Ω−16β≥3Ω/4. For own-free forms,
partial interpolation toward R₀ preserves the strict target rise:
the mixed no-floor joins target2|Q|, and pair withdrawal plus its
TWO outside joins has target−2+2+2=2. The floor-free triple ledger
is correctly NOT assigned this target. I checked the finite count
82+152+715+12+15=976 and coefficient bound8. Whole-law reward
Lipschitz gives the new d interval; 32α<σ keeps noncontacts outside
it. No fixed-profile Danskin differentiation or MAX transfer occurs.

SC2's endpoint roles are correctly separated into early unsupported
floors and tied unsupported joins. If a later conditional is absent,
the original sure owner forces every supported cap to t₀ and every
OTHER cap no later than t₀. A supported Never cap with a surely
finite opponent would tie c, so the t₀=Never case really supplies
all existing Never atoms and an own-sum endpoint. No unproduced
late mass is assumed.

SC4's positive-own ledger and pair ledger are indeed members of
the selected family. The old supported set and sure owner belong
to B, so |B|≥2. Any earlier displayed cap adds a genuine own-floor
term; after it is excluded, only m can be later than t₀. Pair and
grand cases are forbidden separately, leaving exactly B={m,a,b},
outside z, and two supported recipients a,b. This does not presume
that B itself was the old minimizing first coalition.

SC5's actual punishment graft survives the zero-own cap of z.
Every opponent still has positive strict-late mass; otherwise its
sure early law would force m's late cap to tie c/Never. The finite
leakage η_k controls ALL prescribed payoffs and every non-m cap
uniformly over arbitrary replies. The exact h cap decomposition is
max(H_k,A_k+α_k cap_m(w)). Its strict old head gap identifies the
old normalized tail cap limit, while original tail≥P_m and literal
near-punishment grafts give the two opposite inequalities. Finite
punishment witnesses follow from individual cap censor convergence,
without an attained punishment infimum or child Nash. In SC6 the
displayed old m response remains a maximizer of that conditional
tail, so its selected endpoint value really is P_m; normality gives
d=P_m−s_m≤0. This excludes old early m mass and forces pure t₀.

SC8's left-cut transport keeps all upper response orderings by one
positive affine map on t≥t₀, INCLUDING t₀; its early terms are
strictly earlier, unlike the late-conditioning terms. Original
positive t₀ mixture mass isolates t₀ and makes the lower tester
set compact and uniformly gapped. The selected sum is therefore
constant on its two-sided box, and algebraically along the entire
forward diagonal path. All actual caps equal the old selected upper
caps until the first lower wall. Compactness and uniform cap control
make a wall an actual equality, not only a nonattained supremum.

A wall only at λ=1 would have a lower cap equal to its singleton
since all laws now start at t₀. All caps would still be selected
and actual D=d, so the checked true-minimum margin excludes it.
At a wall λ*<1 the original opponent product survives with weight
at least (1−λ*)³. Old uniqueness gives a positive-measure old event
where the lower response and old cap have different coalition
kernels, so this distinction persists. No payoff-gradient independence
or automatic progress rank follows from it.

The no-wall normalized branch has x,y strictly in(0,1), supported
Q_a/Q_b/Q_z root caps and the distinct late m cap, all strictly
maximal locally. The conditional tail is retained, not reselected.
Thus the displayed F(x,y) is genuinely bilinear and actual D near
the old root. At x=1,y=0 its algebraic value is precisely the
forbidden pair-withdrawal-plus-two-outside-joins SC4 label. The
same holds at the other pair corner. No actual corner cap is needed.
This rules out the normalized branch and forces the interior wall.

Finally, at that wall the original pure m still stops at t₀ and
every other owner retains positive strict-late mass beyond t₀.
Hence every owner has positive late mass after the newly active
earlier tester. The independently reviewed EA all-active conditioning
exclusion applies, forcing its MIXTURE point mass positive. Since
λ*<1 retains old laws and all targets are old restrictions, that
atom is an original retained atom. This confirms SC9's ATOMIC
earlier wall, without consuming the remaining simultaneous caps.

## Focused independent SQ1–SQ6 full-cap and value check

Reviewer: CODEX_BROUWER. Verdict: mathematical PASS for exclusion
of the stated single-head/ACTUAL-empty-tester SC subgeometry. This
is ordinary mathematics, not a full UE producer or Lean certification.
No author note or frozen export was edited.

One narrow source-reference correction is required: the exact tracked
`minimumTerminalSemantic_singletonMargin` file is
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`,
not the displayed path missing `Diagnostics`. The declaration's
hypotheses are carrier membership, a GLOBAL SUM minimum and strictly
positive SUM debt; no root Nash or sign assumption is needed. Those
hypotheses are correctly retained throughout SQ.

### Exact claim and what SC does not supply

At the fresh SC table, an actual positive minimum with pure m at
root t₀, positive a/b root masses, zero z root mass, displayed unique
upper caps and old positive postroot masses cannot have at most ONE
pre-root head owner when an ACTUAL empty test exists after its ENTIRE
head and before the root. Lower caps may already be tied. SC has NOT
produced the single-head or empty-test conditions exhaustively. The
result is a strict excluded source subgeometry, not an unconditional
raw-table class or another supplied domination field.

### Independent checks of finite head spreading and every response class

The preliminary finite-law repairs change only masses tending to
zero; product coupling controls prescribed payoffs and ALL full caps
uniformly. A retained root atom gives the needed original date and
strong head/root cutoff convergence. In the repaired literal laws,
the sole head owner j produces only singleton j before the root;
otherwise m is sure at the root. Replacing j's ENTIRE head by an
independent uniform law over M dates preserves EVERY prescribed
terminal payoff exactly. Root and tail dates retain the same relative
chronology and all Never masses. No shared head draw is introduced.

For an upper responder other than j, the head event remains singleton
j with the same total probability; on its complement the translated
root/tail game is identical. For responder j, its prescribed head is
deleted from both comparisons. Hence ALL upper/Never tests map exactly,
and their supremum converges to the original full cap because one old
displayed upper maximizer supplies a lower witness. No only-selected-
test assumption replaces this upper supremum.

For every new early finite response of i≠j, the exact three-term
formula in SQ4 includes the head tie mass a. Its error from the
segment between s_i and K_i is ≤2R h_k/M. The new empty date attains
K_i exactly. For i=j, every early response is its own singleton.
Those cases, all upper tests and Never exhaust the literal calendar.
The actual original tester ξ independently proves K_i≤b_i; the global
singleton margin proves s_i<b_i. Thus BOTH directions of cap convergence
hold, and the head-spread limit has the original prescribed payoff and
FULL cap vectors, genuinely in the original carrier at debt d.

### Marked limit, normalization wall and final pair corner

The new aggregate head interval has length h/4 and only j contributes
density4; maximum head atom length tends to zero. The actual empty
deadline supplies its zero-mass right endpoint. Retained root/tail
intervals and complete upper test kernels are unchanged. Any earlier
active point would therefore be zero-MIXTURE-mass, while EVERY owner
has strictly positive old mass after it. The reviewed all-active EA
consumer excludes the earliest such point even if several caps tie.
This also excludes the boundary equality K_i=b_i; a strict empty-
tester inequality was not smuggled into SQ1.

Consequently all old upper maximizers are full, unique and isolated
at the head-spread minimum. Conditional normalization to clock≥t₀
has genuine two-sided old-cut likelihood transport: strict late
mass is positive for every opponent and the head event is an old
submeasure, not a new atom. Every upper response, including root and
Never, follows one positive affine map along the WHOLE forward path.
The selected multiaffine sum is constant algebraically and actual only
until a lower wall. At any interior wall, the remaining head is still
atomless and every owner still has positive mass after each lower
test, so EA contradicts actual minimum membership. A first endpoint
wall would pay the singleton and violate the true-minimum margin.

With no wall, the normalized endpoint is an actual minimum with the
SC root geometry; a/b's root rates remain strictly between zero and
one and z still has zero root mass. The previously reviewed SC9
bilinear selected-response identity therefore applies, with the same
actual true punishment-tail graft rather than a child Nash. Its pair
corner equals the forbidden floor-free pair label. No actual corner
cap/minimum is asserted. These branches exhaust SQ's hypotheses and
exclude the stated source geometry.

### Exact no-tester countertest and value boundary

I independently recomputed SQ6's complete sparse table. With player0
sure at1 and player1 half0/halfNever, recipient2's prescribed payoff
is1/4, deadline0 pays−1/2 and EVERY deadline≥1 or Never pays1/4.
Its full cap is1/4, other caps/payoffs0, and debt SUM0. After uniform
head spreading, the actual empty deadline M pays1/2; earlier head
tests cannot exceed1/2 and all root/tail/Never tests still pay1/4.
The new debt SUM is exactly1/4 despite unchanged prescribed outcomes.
All sixty reward entries are specified. This is a genuine falsifier
of deleting the ACTUAL tester assumption, not of SQ's positive-minimum
claim or of UE. The derived full-cap upper control is the substantive
increment; overlapping heads or accumulating no-gap heads remain open.
No unresolved mathematical objection was found.
