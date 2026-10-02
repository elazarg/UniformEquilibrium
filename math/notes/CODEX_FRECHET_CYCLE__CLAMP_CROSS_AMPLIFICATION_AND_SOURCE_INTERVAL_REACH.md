# Cap-response clamps, shared cross amplification, and source interval reach

Identity: CODEX_FRECHET_CYCLE.

## Status and question

Ordinary mathematical derivation, not independently reviewed or Lean-checked.
Internal continuation of the
[same all-owner certificate](CODEX_FRECHET_CYCLE__SILENT_PREFIX_ALL_OWNER_MULTIPLIERS.md),
using the unchanged, independently reviewed
[enlarged-calendar source](CODEX_FRECHET_CYCLE__ENLARGED_CALENDAR_NEAR_OPTIMALITY_AND_CROSS_AMPLIFICATION.md).
No full-regret descent, chronological consumer, or new equilibrium class is
claimed. The source is a GLOBAL finite-calendar maximum-regret minimizer,
silently shifted as in those notes; it is not an auxiliary-Nash minimizer or
a total-debt minimum.

Question: can the SAME multiplier's charged cap-response replacement be split
into actual advancing and delaying laws while retaining original-source reach
at the second observer's paid first disagreement? The exact answer is below.
The advancing arm has direct original-source reach. The delaying arm retains
an exact source interval-crossing event, not necessarily original reach.

## 1. Data and the exact split

There are four independent complete stopping clocks T_i, with Never=∞;
|r_i(S)|≤M, M>0, and the payoff at all-Never is zero. Singleton signs are
arbitrary. Let μ be the actual silent source from the all-owner note, using
dates 1,...,K and Never. Let U_i be its prescribed payoff, V_i(t) its pure
response value, B_i its complete cap, d_i=B_i−U_i, and η=η_K=max_i d_i.
Retain the silent cap margin B_i−r_i({i})≥σ>0 for every player.
All unrestricted behavioral caps are represented by the finite complete menu.

The controller domain is X_(K+2), with finite dates 0,...,K+1. The COMPLETE
tester set is T_(K+2)={0,...,K+2,Never}. We retain the same probability λ
over these testers, owner masses θ_i>0, and error R, satisfying

    Σ_(i,t) λ_(i,t)(η−g_(i,t)(μ))≤R,
    Σ_(i,t) λ_(i,t)Dg_(i,t)(μ)[ν−μ]≥−R
                   for EVERY ν∈X_(K+2).                 (1)

The actual global source and silent cap margin in the input note produce
(1), including its simultaneous positive owner masses. Here g_i,t=V_i(t)−U_i.
All initial, after-support, and Never testers remain in (1).

Fix an owner j and a cap-attaining response r∈{1,...,K+1,Never}. Define
actual independent child profiles μ⁻, μ⁺ by changing only j's law to

    T_j⁻=min(T_j,r),       T_j⁺=max(T_j,r).              (2)

These are marginal pushforwards, not shared randomization. Since the unordered
pair {min(T,r),max(T,r)} equals {T,r}, their measures satisfy
μ_j⁻+μ_j⁺=μ_j+δ_r. Every payoff and fixed tester gain is affine in this one
changed marginal. Hence every endpoint gain increment splits exactly into
the sum of its two clamp increments. In particular, with

    a⁻=U_j(μ⁻)−U_j(μ),       a⁺=U_j(μ⁺)−U_j(μ),

one has a⁻,a⁺≥0 and a⁻+a⁺=d_j. Each inequality follows by replacing only
some old stopping choices by the maximizing choice r. One arm has a≥d_j/2.
For a δ-near-cap r the exact repaired statements are a⁻,a⁺≥−δ and
a⁻+a⁺=d_j−e_j, where e_j=B_j−V_j(r)∈[0,δ]; consequently max(a⁻,a⁺)
is at least (d_j−δ)/2. Near-cap arms are not individually declared profitable.

## 2. Both arms are tested by the SAME certificate

For either child μ*, write a=U_j(μ*)−U_j(μ) and
C_(i,t)=g_(i,t)(μ*)−g_(i,t)(μ). Every owner-j tester has increment −a.
Using (1) on that actual one-law endpoint therefore gives

    Σ_(i≠j,t) λ_(i,t) C_(i,t)≥θ_j a−R.                (3)

This holds for BOTH clamps of EVERY j with the same λ. For τ>0 the mass
of source testers below η−τ is at most R/τ. Since |C|≤4M, put

    b=(θ_j a−R−4MR/τ)/(1−θ_j).                        (4)

If b>0, some i≠j and t in the COMPLETE tester menu satisfy

    g_(i,t)(μ)≥η−τ,       C_(i,t)≥b.                   (5)

No tester is silently reselected as another player's favorite response.
The new tester K+2 can differ from K+1 after (2), and is retained.

Let V_i* denote response values at μ*. For a source-supported observer
choice s set

    A_s=(V_i*(t)−V_i*(s))−(V_i(t)−V_i(s)).             (6)

Then E_(s∼μ_i) A_s=C_(i,t)≥b and |A_s|≤4M. The good set A_s≥b/2 has
μ_i-mass at least b/(8M). Select its earliest supported member s, with
Never last. It exists even if the good set consists only of Never. Every
good member is at least s. Since (5) implies B_i−V_i(t)≤τ,

    V_i*(t)−V_i*(s)≥b/2−τ=:g.                        (7)

Assume g>0. The first disagreement ℓ=min(s,t) is finite. The observer's
source survival to ℓ is at least b/(8M), and the child's opponents' survival
there is at least g/(2M): the two pure responses coincide before ℓ, and
their conditional payoff difference is at most 2M. Thus

    J_*(ℓ):=Pr_(μ*)(all four clocks≥ℓ)
       ≥F:=b g/(16M²).                               (8)

This is initially a CHILD-reach statement. Its transfer is treated separately.

## 3. Advance: direct source reach, with a linked second observer

A positive advancing gain forces r<∞. The advancing law is implemented
by the original behavior at every date except a single forced-Quit row r;
the old off-date behavior can be restored literally. The change is invisible
unless the original profile reaches r. Therefore

    a⁻≤2M Pr_μ(all T_k≥r).                            (9)

The advancing child stops by r, so a strictly positive contrast (7) forces
ℓ≤r. For each such ℓ,

    Pr(min(T_j,r)≥ℓ)=Pr(T_j≥ℓ).

The original and child profiles have identical laws and behavior strictly
before ℓ, and identical joint reach at ℓ. In particular that ORIGINAL reach
is at least a⁻/(2M), by (9). This direct owner-gain argument is stronger
than needing (8) to recover observer survival.

The new connection is the ancestry of the second observer's paid row in
(3)–(7), not a new generic positive-debt reach lemma. The second row can
begin strictly BEFORE the owner's forced-Quit date. Its payoff contrast is
against the clamped child, although its initial live event is shared with μ.

## 4. Delay: the exact interval-crossing remainder

For a finite cut r, delaying preserves the owner's survival strictly AFTER
r, but not necessarily at r. In fact ΔV_i(t):=V_i⁺(t)−V_i(t) is constant
over all observer responses t>r, including Never: every moved owner clock
T_j<r now stops at r, before either such observer response. Thus A_s=0 if
both s,t>r. A positive selected A_s in (6) necessarily has ℓ≤r. With r=∞
the same conclusion simply says ℓ is finite.

At this selected ℓ define the LITERAL ORIGINAL PRODUCT EVENT

    X_(j,ℓ)={T_j<ℓ and T_k≥ℓ for every k≠j},
    χ_(j,ℓ)=Pr_μ(X_(j,ℓ)).                            (10)

All three other source clocks, including the observer's actual clock, occur
in (10). No conditional child clock is substituted. Because max(T_j,r)≥ℓ,
the disjoint partition by T_j<ℓ or T_j≥ℓ gives the exact identity

    J_+(ℓ)=J_μ(ℓ)+χ_(j,ℓ).                           (11)

Consequently (8) gives J_μ(ℓ)+χ_(j,ℓ)≥F: either original joint reach is
at least F/2 or χ_(j,ℓ)≥F/2. Equality ℓ=r belongs to (11), not the
strictly-after-cut survival-preservation case.

On X_(j,ℓ), j was the original unique first quitter before ℓ while every
other original planned clock survived to ℓ. The delay moves this very mass
across the interval [T_j,ℓ] toward r. Although χ is bounded above by the
original singleton-{j} terminal probability, that marginal loses the key
timing data. The retained object is (10), together with the actual delayed
owner gain a⁺ and its SAME-λ inequalities (3)–(5). It is not a paid row at
an originally reached suffix when J_μ(ℓ)=0.

For example T_j=0 and all other clocks=1, delayed to r=1, gives ℓ=r=1,
J_μ(1)=0, J_+(1)=1 and χ=1. This checks the equality-at-cut convention;
it is not asserted to be a global-minimum or paid-cross example.

## 5. Earliest near-cap test: exact transport only on the after-cut branch

Fix 0<τ<σ and let r_i be each owner's earliest τ-near-cap response in the
translated complete menu. This choice keeps the error in Section 1. Any
receiver t from (5) is τ-near-cap; the silent date zero is not, so t≥r_i.
If r_i>r_j for the delayed
owner's cut r_j, the constancy of ΔV_i AFTER that cut proves

    C_(i,r_i)=C_(i,t).                                (12)

This is an exact cross-gain-preserving reselection, not an appeal to old
cap attainment. The source gain at r_i is at least d_i−τ, hence at least
η−τ−R/θ_i by (1). Its source two-response contrast is still at least −τ.

At r_i=r_j, (12) need not hold. The difference between the joining response
r_j and any later response is exactly the expectation on
{T_j<r_j; T_k≥r_j for k≠i,j} of

    r_i({i,j}∪Q)−r_i({j}∪Q),
    Q={k≠i,j:T_k=r_j}.                                (13)

This is ΔV_i(r_j)−ΔV_i(t), not an omitted source value term. It has no
fixed sign for arbitrary raw rewards. Initial, joining and after-cut branches
are therefore distinct even under earliest near-cap selection.

More importantly, if r_i>r_j then positive A_s forces the SUPPORTED
COMPARISON clock s≤r_j. It imposes no inequality r_i<r_j. Choosing an
owner of smallest r_j does not create a strict backward order of the
owners' response dates: the second observer's earlier disagreement can come
from s, not from its selected near-cap date. This leaves a concrete global
question, not a counterexample to any global source implication.

## 6. Existing reach and two-cut interfaces; exact remaining question

The following declarations were inspected in their source files:

- `positiveDebt_exists_actualJointReach_paidRow_mem_support` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean`
  already gives source support and joint-reach floors from ordinary positive
  debt. Fable's scratch `positiveDebt_exists_commonPrefix_profitableStoppingLawFork`
  in `math/fable/lean/FableCommonPrefixFork.lean` additionally retains a literal
  source prefix and a profitable whole-law fork. No new build or scratch trust
  audit was run here. The shared all-owner cross-test linkage is the extra
  field being tested here.
- `QuittingPositiveJointPrefixReachSource.punishment_nash_of_joint_pos` and
  `.punishment_approximateEquilibriumExistence` in
  `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointPrefixReachEndpoint.lean`
  require an approximate-Nash prefix source with errors tending to zero.
  A positive-regret minimizing source does not supply this hypothesis.
- `quittingTerminalSemanticDebtSum_twoCut_eq` and
  `QuittingPositiveMinimumTwoCutBlock.offMinimum_or_exists_paidSplice` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`
  telescope actual suffixes and require actual entry reach for their splice.
  The χ arm supplies no such reach at ℓ and is not that supplied block.
- `nonempty_sourceFaithfulMinimumCausalization` and
  `QuittingSourceFaithfulMinimumCausalization.responseMenu_transport` in
  `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean` preserve given
  actual profiles and response contrasts. Their minimum is TOTAL debt; no
  identification with our maximum-regret minimum, or consumption of (10),
  is inferred.

The earlier
[pure-pair two-port no-go](CODEX_ADVERSARY__PURE_PAIR_SCREENED_TWO_PORT_CAUSAL_TRANSPORT_NOGO.md)
has a sure nonsingleton screen, making every unilateral continuation invisible.
Here (10) has one original sure first quitter on the selected event. Removing
that quitter exposes its counterfactual continuation. Thus neither that
screening no-go nor generic source-faithful causalization resolves the present
same-source delayed cross comparison.

Exact rational enumeration on 16 signed reward tables checked 64 cap splits,
640 reach identities and 192 after-cut response equalities, including Never.
The proof is the finite expectation and event calculations above; these tests
do not certify global-minimum provenance of their random input profiles.

## 7. Coordinated delayed-owner and early-observer head change

The next test retains the actual mixed source. Consider the delayed arm with
its selected receiver t>r and its good set G from Section 2. Necessarily
G⊆{s:s≤r}, since A_s=0 for s,t>r. Transport just this early observer mass
to t, leaving all other observer clocks unchanged. Interpolate the j-clamp
with parameter α and this i-transport with parameter β, independently,
for 0≤α,β≤1. The point (0,0) is the original source. This paragraph treats
the strictly-after-cut receiver branch; earlier or joining receivers are not
discarded from the source theorem or declared solved by this test.

A calendar safeguard is essential. A selected tester need not be an admissible
controller action. For a uniform version, produce (1) FROM THE OUTSET on
X_(K+3), with complete testers through K+3 and
R=√(192M(η_K−η_(K+3))). The same source and silent-prefix proof apply, and
the owner's cap cut can still be chosen ≤K+1. If the selected receiver is
K+3, replace it by K+2: source values coincide and the delayed ΔV_i is
constant strictly after r. This preserves (5)–(7) and makes the transport
admissible. The newly produced multiplier is common to both variations;
the old multiplier is NOT silently extended to a new controller domain.
Every tester through K+3, and Never, is retained in the full objective.

For a pure clock tuple write F_ℓ(u,s) for player ℓ's terminal reward when
the two changed owners j,i use clocks u,s and the other two ORIGINAL clocks
are retained. Payoffs at all-Never are zero. Define the exact mixed payoff
coefficient

    h_ℓ=E[1_{T_j<r}1_{T_i∈G}
      ·(F_ℓ(r,t)−F_ℓ(r,T_i)−F_ℓ(T_j,t)+F_ℓ(T_j,T_i))].   (14)

This expectation includes both unchanged original clocks. If k is an unchanged
owner, let h_k^(v) denote the same coefficient with k's clock replaced by
the literal pure tester v. Every complete tester gain has the EXACT form

    g_(k,v)(α,β)=g_(k,v)(0,0)+α A_(k,v)+β B_(k,v)
                    +αβ H_(k,v),
    H_(i,v)=−h_i,      H_(j,v)=−h_j,
    H_(k,v)=h_k^(v)−h_k                 for k∉{i,j}.       (15)

Here A and B are the actual one-law endpoint increments. Both changed owners'
response values have zero mixed coefficient because their own prescribed laws
do not affect their own response payoffs. No maximum is replaced by an average:
the complete objective is the maximum of ALL the bilinear rows (15).

For the paid observer the mixed coefficient is favorable for EVERY tester:

    h_i=Σ_(s∈G) μ_i(s)A_s≥(b/2)μ_i(G)>0.                (16)

The two unmatched owners are not automatically controlled. Every donor corner
in (14) has a j clock at most r. Consequently h_k^(v) is the SAME number
h_k^late for every tester v>r, including Never. Averaging over k's unchanged
source law gives the exact identity

    h_k^late−h_k
       =Σ_(s≤r) μ_k(s)(h_k^late−h_k^(s)).                (17)

Thus third/fourth early clocks carry precisely the unmatched late-test curvature.
Joining-at-r remains separate. Only the MIXED coefficients merge after r;
the linear terms and full tester gains in (15) need not coincide there.

Even without an intervening third clock, the delayed owner's coefficient need
not help. On the strict ordered donor event

    T_j=u<T_i=s<r<t,       both unchanged clocks>r,

the four outcomes in (14) are respectively {j},{i},{j},{j}. Its mixed reward
vector is therefore r({j})−r({i}). The favorable observer premium can be
accompanied by the delayed owner's loss of its passive-i reward. Equal donor
times, s=r, or an intervening unchanged clock retain their literal four
coalitions in (14), rather than being assigned this special-case formula.

The SAME multiplier's exact mixed coefficient is

    H=Σ_(k∉{i,j},v) λ_(k,v) h_k^(v)−Σ_k θ_k h_k.        (18)

No sign for (18), much less all rows (15), has been deduced from global source
optimality. In response to this specific expression, CODEX_NOETHER_SUPPORT
pointed out a precise limit of its worst-reward normal account: a reward
direction d at an unchanged source always satisfies
Σ_t μ_i(t)g_(i,t)(d,μ)=0 over i's literal support. Our mixed row for changed
owner i is the nonzero constant −h_i, with average −h_i. Thus no single
same-source reward direction can identify ALL rows (15) with reward-direction
rows. A scalar or counterfactual-source composition would need a new proof;
normality alone supplies no sign for (18).

Exact rational enumeration on ten signed tables verified 240 complete bilinear
gain rows (15), the constant mixed coefficients for both changed owners, and
twenty unchanged-owner identities (17). The actual independent interpolation
used α=2/5 and β=3/7. This tests the full rectangle algebra, not positive
global-minimum provenance of the random sources.

Current next question: can a genuinely global, complete-envelope comparison
orient the missing delayed-owner and third/fourth-clock terms in (15), rather
than merely improving observer i? The favorable coefficient (16), by itself,
does not produce a descent. The independent two-owner re-equilibration test
of CODEX_TARSKI_PREMIUM changes the pair's complete strategies jointly and is
a different candidate operation; it is not assumed in this calculation.
