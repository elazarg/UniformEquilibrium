# Fin4 coverage and completion map

Maintainer: `CODEX_ROOT`

## Status and finish line

Fin4 remains open. We have an exhaustive **source-obligation reduction**,
with two open universal consumers. We also have overlapping solved reward
classes. These are different maps: neither the number of exports nor the
number of source tags counts remaining reward classes.

This note supplies a conservative, disjoint reward-class work queue and a
separate source map. Every possible counterexample is covered by the queue;
some queued games may already be solved by results outside its five named
mechanisms. Incorporating those results can shrink the queue without changing
its exhaustiveness. A complete executable registry of all exported raw
criteria has not been assembled.

There are two sufficient finish lines:

1. Prove both existing universal source capstones below.
2. Prove the native target below on every reward cell, including boundaries.

Either route suffices. Conditional alternative interfaces need not all be
solved. The source declarations cited here were inspected statically; no fresh
Lean build was run. The new bookkeeping and compositions are ordinary
mathematics, not additional Lean declarations.

## Universal native domain

The original domain consists of 60 real rewards: four recipients at each of
15 nonempty quitting coalitions. Live play and Never pay zero. Strategies
are independent complete stopping laws on natural dates plus Never; deviations
replace one owner's entire law. UE means one payoff target fixed before
accuracy, with the full uniform finite-horizon contract.

It suffices, and is necessary for the conjecture, to prove

    A_Z=inf{D_Z(P): P actual, nu(P)=0}=0

for every native table Z with Z_i({i})=0. Here U is prescribed payoff, B the
unrestricted behavioral response cap, D=sum_i(B_i-U_i), and nu the ORIGINAL
joint Never probability. The other **56 coordinates are unrestricted**.
Native AllNever itself is always Nash; A_Z>0 concerns absorbing profiles.

For any nonnegative recipient-row raise s with sigma=sum s_i>0, set
r_i(S)=Z_i(S)+s_i on every nonempty S, keeping Never zero. On the SAME profile,

    B_i^r=B_i^Z+s_i, U_i^r=U_i^Z+s_i(1-nu),
    D_r=D_Z+sigma nu.

Finite deadlines determine the cap because own singleton rewards are
nonnegative; each finite deadline absorbs surely. The reviewed repair bound
A_Z<=D_Z+14M nu^(1/4), M>=1 bounding |Z|, therefore gives

    UE(Z+s) iff A_Z=0.

Indeed A_Z=0 supplies absorbing approximations. If A_Z>0, every profile has
D_r>=min(A_Z/2,sigma(A_Z/(28M))^4)>0. The checked single-pivot normalization
produces from any signed counterexample a NEW literal counterexample with
own singleton vector e_p. Subtracting those recipient rows gives A_Z>0;
conversely Z+e_p converts any native positive gap into a counterexample.
Normalization does not transport a previously chosen source or chronology.

The FULL anchored singleton matrix of every native A_Z>0 table is already
R0 of degree1: apply
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`)
to a restored-pivot table. Recipient-row invariance is
`quittingSingletonMatrix_sub_payoff`
(`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`).
The accepted [strict-column/all-END reduction](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md)
also already proves det Gamma>0 and SOME strictly positive inverse column
for the SAME native table, without perturbation. These are universal matrix
constraints, not restrictions confined to the AllNever source alternative.
The full JOINING pencil condition below still has its stated source scope.

Exact ingredients are
`exists_finFour_no_uniformPayoff_iff_exists_singlePivot`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`),
`quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg`
(`UniformEquilibrium/Quitting/Punishment/FinitePureReplyValue.lean`), and
`quittingFinitePureReplyValue_playerwiseAffine` and
`quittingTerminalPayoff_playerwiseAffine`
(`UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`).
The repair and perturbation arguments are in
[global least-Never reduction](../exports/GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md).

A_Z is 8-Lipschitz in the entrywise native reward norm. A positive gap thus
persists on an open set. For the existence problem we may avoid any specified
finite collection of proper polynomial zero sets, then select sources afresh.
Equivalently, proving A_Z=0 on a dense generic native domain covers its
boundary by continuity. This removes exceptional TABLE loci, not zero
coordinates or singular source configurations at a fixed table.

## Existing exhaustive source map: two open consumers

The exact source-preserving Research reduction is

```text
arbitrary no-UE reward
  -> full-support hard residual and one positive-minimum law source
  -> source-preserving cofinal singleton stream
  -> stabilized forced-pair stream
       -> uniformEscape -> uniformEscape -> ...
       -> minimumReturn -> minimumReturn -> ...
```

The two old monodromy entrance tags are impossible. The remaining entrance
tags reach the common stream. The source, actual profiles, dates, laws,
literal tails and fixed mass/gain floors remain part of the packets.

| Open capstone | Exact stream property | What still needs a universal consumer |
| --- | --- | --- |
| `uniformEscape` | Literal post-date continuation debts stay at least D_*+delta for one delta>0 along the retained stream | Same-tail half-floor return selection, or absorption undercharge with AllContinue/singleton blocker, must yield UE or a valid global contradiction |
| `minimumReturn` | Those literal continuation debts converge to D_* | Normalized whole equality produces a three-role endpoint whose target may ascend or regenerate; strict whole excess gives a point whose only exact cap-Nash root is AllContinue. Neither output yet supplies global descent or UE |

The precise completion contract is already stated by
`FinFourUniformEscapeCapstone`, `FinFourMinimumReturnCapstone`, and
`finFourCompletion_of_capstones`
(`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`).
Each capstone quantifies over EVERY reward realizing its mode. The conditional
theorem proves UE for every bounded Fin4 reward from both premises. Every
finite reward table has a bound. **Neither premise is proved.**

The stronger structural dispatch is
`uniformPayoff_or_sourcePreservingConsumedOutcome`
(`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`).
“Consumed” here means structural information, not a completed UE proof.
A return only to D_*+delta/2 is not arbitrary-accuracy return. Convergence of
reference profiles or literal tails does not make edited whole profiles
near-minimal. Regeneration preserves specified law/source data but supplies
no renewable paid orientation.

The two modes are not asserted to give a disjoint reward-table partition:
the theorem does not identify mode choices across permitted selections.
The graph has three singleton strongly connected components, two terminal,
by its declared four-edge table. This
classifies that reduction graph, not every underlying continuation dynamic.
See the [SCC ledger](CODEX_ROOT__FIN4_SCC_PROGRESS_LEDGER.md) for its internal
cycles and [declaration inventory](CODEX_ROOT__FIN4_PRODUCER_ATLAS_DIRECTED_KNOWLEDGE.md)
for the exact producer chain.

## Native source geometry: three disjoint table branches

This is an alternative research reduction on the native positive-gap domain,
not an identification with the preceding atlas minimum. Let C be the compact
closure of ACTUAL tuples (U,B,e,N), where e is the Never response and N retains
each owner's original Never mass. Put E=C intersect{D=0}, and define

    alpha=min_E nu,
    m=min_{X in E, min_i U_i<=0} nu,
    M_m={X in E: min_i U_i<=0, nu=m},
    delta_m=min_{X in M_m} min_i U_i.

All minima are attained; AllNever supplies feasibility, and repair gives
alpha>0. Assume joining-genericity: all twelve off-diagonal entries and all
four principal triple determinants of L=J-Gamma are nonzero, where
Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}), with diagonals zero.

| Disjoint branch | Forced source geometry | Status / sufficient contradiction |
| --- | --- | --- |
| `N0`: alpha=1 | E consists only of AllNever; m=1, U=0 | Open. A neighborhood good-root theorem near the nonpositive payoff boundary suffices; a good root at 0 alone does not |
| `N-`: alpha<1, delta_m<0 | Every alpha-source is strictly positive; alpha<m<1. Select an m-source with a negative coordinate; EVERY root there is proper with strictly positive successor coordinates | Open. A good root at that selected source, or a valid comparison lowering m, suffices |
| `Nb`: alpha<1, delta_m=0 | Every alpha-source is strictly positive; alpha<m<=1. Every m-source has nonnegative payoff with a zero coordinate; its only good root is AllContinue, and strict-negative all-bad annotations accumulate there | Open. Local good-root control at all nearby strict-negative annotations, or a finite-word comparison lowering m, suffices |

This is genuinely disjoint even if one table has both negative and boundary
m-minimizers: the secondary minimum delta_m sends it to `N-`. Exhaustiveness
follows from the global least-Never dichotomy and delta_m<=0. The strict
inequality alpha<m follows from compact attainment: equality would give an
alpha-minimizer with a nonpositive coordinate. The alpha- and m-sources are
generally DIFFERENT points. Nearby bad annotations need not be actual payoffs.

The [negative-dual/actual-repair reduction](../exports/NONNEGATIVE_MINIMUM_SOURCE_PENCIL_REDUCTION.md)
now narrows the proper nonnegative m-sources for ARBITRARY native tables.
Their zero set T has size2 or3 and admits y>0 with y^T Gamma_T<0.
Under the existing joining genericity, every matrix Gamma_T-tJ_T,
0<=t<=1, has its own strict negative left certificate and degree0.
This principal-pencil fact is distinct from the full Gamma degree1 above.
The old solo-cover/negative-clock criterion remains a sufficient broader
source consumer on its stated raw family; the new theorem excludes the
entire semipositive proper-zero singleton-block case without that cover.

More importantly, the new degree-produced repair turns nearby positive E
points into eligible E points with STRICTLY lower ORIGINAL Never. If
eta=min_(i in T)U_i>0, the produced gain is at least eta nu/(12M).
At a proper selected source this gives a quantitative local lower bound
nu>=m/(1-eta/(12M)) for nearby positive E points. No payoff-fibre minimum
is substituted for the original m.

For the ENTIRE m<1 generic branch, put

    P_m={X in E:nu(X)<=m,U(X)>>0},
    beta=(A_Z/(14M))^4>0.

P_m is compact and, when nonempty, has ONE positive buffer
kappa_m=min_(P_m)min U>0 through level m itself. All-zero E at nu<=m is
excluded by finite two-copy renewal; proper zero limits are excluded by the
actual repair. This removes the former kappa_s->0 seam as s approaches m.
A given positive source with nu0<=m has an actual augmented-carrier Nash
head reaching either eligibility at nu=m or nu>m in at most

    1+floor(log(m/nu0)/[-log(1-kappa_m/(64M))])

retained macroscopic cuts. Replacing nu0 by beta makes the bound uniform
on P_m. The same positive sublevel is closed under auxiliary Nash prefixes
and has finite nonzero-prefix height before root inertia. These results
do not identify that carrier head with the stronger literal source data of
the two atlas capstones, produce a finite-calendar representation of E,
or consume a finite-amplitude jump above m.

Every strict-negative m-source has m<1, since nu=1 forces U=0. In `Nb`,
m<1 now has the same compact positive sublevel; m=1 retains the AllNever
endpoint degeneration. The new uniform bound does not resolve either
branch's finite-amplitude joint-return consumer. `N0` remains open too.

There is a raw security filter on these cases. If for each i some a_i>0
satisfies Z_i(T+i)+a_i Z_i(T)>=0 at every nonempty opponent coalition T,
hazard1/(1+a_i) guarantees0 against every complete opponent law. Every
actual cap and every zero-debt closure payoff is then nonnegative: `N-`
is absent on that class. With all these inequalities strict and Gamma R0,
every ACTUAL ALL-END profile with a zero cap is AllNever. Other zero-cap
ALL-END endpoints must be unattained. Two zero caps force every owner's
finite stopping probabilities before any fixed date to vanish along
realizing sequences; original Never may still be below1. The
[proof and exact boundary test](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md) include
a joining-generic strict-security table with positive inverse pivot columns:
actual exact Nash tuples converge to an unattained two-zero source with
original Never1/40. The table is already absorbing-Nash-covered. Thus the
compact-limit seam is real, while its consumption under a positive absorbing
gap remains open. These are source filters, not a new UE game class.

Here a good root q is an auxiliary Nash root with some q_i=1 or with a
successor payoff coordinate <=0. The precise source comparison and the open
neighborhood consumer are in
[payoff-domain orientation](../exports/PAYOFF_DOMAIN_ORIENTATION_UNIFORM_EQUILIBRIUM.md).
Under the further genericity in Section9 of the
[global source theorem](../exports/GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md),
`N0` requires EVERY matrix Gamma-tJ, 0<=t<=1, to be R0, standard Q and of
degree1. A crossing excludes `N0` only; passing the pencil settles no branch.

The marked actual/mixed endpoint program now has a UNIVERSAL matrix
adapter: the strict positive inverse column is already produced by the
[strict-column/all-END reduction](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md).
That reduction also supplies one fixed positive recipient-weight box K
and t0>0 such that EVERY original SUM-debt minimum at theta_i[Z_i+t],
for theta in K and0<t<t0, has all four NATIVE END caps active and all
original Never marginals bounded away from0. Its universal all-END consumer
remains open. This is a different minimizing objective from native m.

The [compact first-joint-contact reduction](../exports/COMPACT_MINIMUM_FIRST_JOINT_CONTACT_REDUCTION.md)
now gives a common finite head for BOTH actual and nonrealized minima.
Choose a compact all-END full-SUM minimum with least ORIGINAL nu among
those minima. At this SAME source X it produces

    X=prefix(q,Y), Y in C, B(Y)=e(Y), N_i(Y)>0,
    q in[0,1)^4 with at least two positive coordinates,
    Q_i^Z(q)=B_i^Z(X)=e_i^Z(X) for some owner i.

The current finite query is paid in the ORIGINAL raised game, and the row
is the first prescribed joint stage. The source X need not have an actual
calendar. A uniformly charged deletion of tiny leading rows in actual
realizers preserves the entire SAME(U,B,e,N), then a finite affine prefix
ray forces contact by secondary original-Never minimality. The old strict
cap margins and early-collision mechanism are credited and reproduced as
needed; the new consumer is the exact compact contact ray.

The row is NOT asserted Nash, and Y is neither assumed minimizing nor
actually realized. Native Never is a maximizing response; raised literal
Never remains strictly below the raised cap. This removes actual attainment
as a prerequisite for the finite first-contact normal form, not for its
suffix or the actual-calendar Hessian arguments below. The universal
remaining target is to consume this finite paid contact with its genuine
compact suffix and the same original full-SUM objective.

The [actual minimum contact/support reduction](../exports/ACTUAL_MINIMUM_CONTACT_AND_SUPPORT_REDUCTION.md)
now supplies a complete necessary condition for ACTUAL minima of this
original full-SUM problem. Write rho=t sum theta_i. Choose ONE theta in
the old box before t and before any source. For every sufficiently small
t, an actual all-END minimum cannot have all four finite stopping supports
unbounded while its finite cap-contact dates are bounded. The proof uses
eight late hazards, an exact END-level manifold and its tangent Hessian;
it forces the identity

    (theta_i+rho s_i)Gamma_ij=(theta_j+rho s_j)Gamma_ji,
    s_i=sum_j(Gamma inverse)_ji.

One fixed price chosen in the open box makes this impossible for all small
t. This uses only Gamma invertibility, already universally available at
the SAME native table. No new raw-table genericity, joining-rank or
simultaneous-support hypothesis is needed for this exclusion.

If an original minimum is actual, a finite modification also selects a
minimum with a finite cap contact. The strict floor needed is
mu<min(theta_i)A_Z, supplied by choosing t small. Repeated finite contact-time
descent aligns the earliest contact with the first prescribed stage, which
has at least two positive own atoms. It may be reindexed to date0. Every
owner's ORIGINAL raised debt is positive. Existing four-player quadratic
cap margins and the old solo-first collision ledger are reused; the new
content is this same-table contact alignment and the support/price
obstruction. The modifications preserve each owner's bounded/unbounded
support status and the bounded/unbounded status of its contact dates.

The [compact END-contact dichotomy](../exports/COMPACT_END_SEPARATED_CONTACT_EXCLUSION.md)
removes actual attainment from the source-case partition. Avoid the singleton
zero hyperplanes, select the native table afresh, then fix its produced
cheap recipient weights before t and before any minimum. For EVERY marked
representation of an all-END global minimum, exactly one geometry remains:

| Marked source case | Necessary surviving geometry | Open consumer |
| --- | --- | --- |
| Accumulating interior contacts | Distinct native cap-query locations approach the final finite END c from below | Consume their whole-source interaction; contacts need not be prescribed actions |
| Isolated finite END | A last positive common-mixture atom has its retained interval ending at c; no owner has cofinal finite mass | Consume this last-atom source with its genuine earlier history |

The complete exclusion covers two, three or four cofinal physical owners,
including nonatomic and nonrealized clocks. One cofinal owner already forces
interior contact accumulation. Zero cofinality is exactly the isolated-END
last-atom case. Fixed bounded latent densities compile every comparison into
the SAME actual-tuple carrier, retaining all original N and old cap queries.
Two cofinal owners admit an exact timing direction; three or four are excluded
by the finite LP/two-form/Morse argument. An actual calendar is not an input.
The accepted [late-tail debt bound](../exports/GENERAL_LATE_TAIL_DEBT_AND_END_CAP_MINIMUM_REDUCTION.md),
Theorem A, already excludes a sole cofinal owner under A>0; this older
constraint is reused rather than counted as a new exclusion.

The older [native collision floor](../exports/NATIVE_COLLISION_FLOOR_AND_GLOBAL_MASS_DICHOTOMY.md)
also applies to EVERY old conditional suffix of a native E source with
positive original Never. If its total conditional finite mass beta is
nonzero and less than1/2, its pair-collision mass obeys
C>=c_A beta^2, c_A=(A/(400M))^18/16. Each such suffix therefore contains
one date with two distinct owner atoms each at least c_A beta/3.
These bursts occur cofinally as finite tail mass tends to zero, though
their owner pair may change. Purely nonatomic, singleton-only and
vanishing-relative-collision tails were already excluded by this result.
Dense shared bursts remain open. At original full-SUM raised minima its
separate dichotomy is total finite mass O(t) or a pair-macroscopic burst;
the E-only every-suffix floor is not asserted at positive native debt.

These are disjoint modes of a CHOSEN marked representation, not raw reward
classes or an actual-attainment theorem. A last positive atom does not imply
that the preceding marked history is finite or realized on natural dates. For the additional raw condition that Gamma has no
reciprocal zero pair, EVERY actual all-END local minimum with positive
original Never has a finite cap contact:
otherwise at least two owners persist and their entire singleton block
must be zero. The nongeneric contact selector above does not need that
condition. Nonrealized minima and all stated contact consumers remain open.

The [complete actual bounded-contact exclusion](../exports/ACTUAL_BOUNDED_CONTACT_EXCLUSION.md)
now rules out the ENTIRE bounded-contact case at one fixed produced price
vector. Avoid only the singleton zero hyperplanes, select the table afresh,
then choose the prices BEFORE t and before every minimum. Every ACTUAL
all-END global minimum at all sufficiently small raises has UNBOUNDED
finite cap-contact dates, regardless of its persistent-owner count.

The proof produces one common cone-KKT multiplier using late positive and
one-sided zero controls. The strict inverse column keeps every effective
price close to the chosen price and forbids reciprocal balances. With two
persistent owners an exact timing derivative forces such a balance. With
three or four, the multiplier set is a point or segment; finite LP duality
and a two-quadratic-form alternative produce a normal PSD multiplier,
contradicted by five negative directions against codimension at most4.
No2x2/3x3 minor, constant-rank or simultaneous-support hypothesis remains.
This subsumes the intermediate incidence-size and two-persistent stages;
they are not separate outstanding cases or exports.

Unbounded contacts may be unused replies, including repeated equivalent
late queries, and do not imply infinitely many prescribed atoms or UE.
The universal remaining target is still the finite paid contact with its
genuine compact suffix; actual contact sets and suffix realization are
not replaced by a convenient calendar or equilibrium.

The compact deletion identity in Section21 of the
[method note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md) additionally excludes
one complete two-active-owner configuration. Fix the native table and theta
with 0<alpha=min_E nu<1. At all sufficiently small rho, no all-END compact
global minimum can have exactly two physically active laws, the other two
literally Never, and every outside native cap contact a payoff-kernel alias of Never. This includes bounded
physical supports, last atoms and nonrealized clocks. Four legal Never-mixing
directions produce one common contact dual; exact deletion gives F=rho N,
nu=N^2, contradicting the fixed-table alpha envelope. A surviving such two-active source therefore needs a genuinely different
outside response kernel on a positive-probability event. Equal expected
response values alone do not make kernel aliases. Those genuine outside
contacts and alpha=1 remain open; physical inactivity alone is insufficient.

The [oriented-pair dispersion theorem](../exports/ORIENTED_PAIR_UNIFORM_THREE_OWNER_DISPERSION.md)
gives a quantitative restriction under a finite raw pair test. Suppose every
off-diagonal Gamma entry is nonzero, and each unordered pair has a direction
with Gamma_ij(Gamma_ij-J_ij)>0. At A>0 there is an explicit fixed-table c>0
such that EVERY actual profile and its original augmented closure satisfy

    D+beta epsilon>=c beta^2,
    beta=sum_i(1-N_i), epsilon=f_(3)+f_(4).

Thus every nontrivial native E point has at least three finite masses each
at least c beta/2. At original raised full-SUM minima, either beta=O(t)
or the third mass is at least c beta/4. The literal fixed13 family below
satisfies every pair test at A>0, without any perturbation of its31 free
rewards. This quantitative literal statement does not follow from the older
dispersion packet's row-distinctness hypotheses. It excludes concentration
near a one-/two-owner mass face, including dispersed three-cofinal tails
whose third mass becomes negligible. It does not close a raw UE game class
or assert a common three-owner atom.

Section24 of the method note unifies this argument with the older geometric
pair proof and consumes the intervening ratio-one boundary. Write
r_i=J_ij/Gamma_ij and r_j=J_ji/Gamma_ji for a pair. The same dispersion
conclusion holds if all off-diagonal Gamma entries are nonzero and no
unordered pair has equal ratios r_i=r_j>=1. The new boundary proof uses a
macroscopic common atom followed by the ORIGINAL query x+1 and the older
unrestricted every-cut debt bound. Equal viable ratios are exceptions to
THIS dispersion mechanism, not the remaining cases of Fin4 as a whole.
The synthesis reuses the accepted compact geometric-pair lemma; it is not
a second export of that proof. Section27 tests the two outsiders on the
equal-ratio boundary. At alpha=1 a dispersion failure also requires two
strictly opposed outsider inequalities with exactly the same limiting
finite-mass ratio, and total finite mass tending to zero.

Section23 of the method note gives a finite ambient-matrix classification
of proper cofinal support S. Test the linear feasibility problem

    y>=0, supp(y) subset S, sum y=1, Gamma y>=0.

If it is infeasible, every sufficiently late OLD legal query carries a
uniform positive fraction of all remaining finite mass. The entire late
calendar is atomic with a uniform geometric tail bound, and its RESTARTED
conditional suffix has
an actual natural-date realization with full U,B,e and each conditional N
preserved. This gives no actual realization of its earlier compact history
and no minimum property to the suffix. Conversely, vanishing relative atoms
force this ambient face problem to be feasible. A positive inverse COLUMN
alone does not exclude feasibility on every proper face.

The thirteen endpoint zero faces are a conditional refinement of this
program, not thirteen additional universal reward classes. An inherited
endpoint must improve the whole head's constrained obstacle objective,
not just its own debt. The exact objective and observer constraints are
retained in the [actual-minimum note](CODEX_ROOT__ACTUAL_MINIMUM_AND_MIXED_ENDPOINT.md).

## Reward-class work queue

For each mechanism below, admit native Z when there exist a player
permutation pi, a common scale a>0, nonnegative row raises s_i, and its
permitted auxiliary parameters such that its FULL raw premise holds for
r_i(S)=a Z_{pi(i)}(pi(S))+s_i. Use that r's actual reward bound in its tests.
Each theorem concludes A=0 for the native part a pi(Z), which implies A_Z=0.
Let S5 be the union of these five admission predicates:

| Solved predicate | What it adds |
| --- | --- |
| [Supportwise Low/Charge/Orientation](../exports/SUPPORTWISE_NEGATIVE_ORIENTATION_UNIFORM_EQUILIBRIUM.md) | Independent tests on each larger support, with the stated pair and weak-boundary rules |
| [Pair–triple cancellation](../exports/PAIRED_SUPPORT_INDEX_CANCELLATION_UNIFORM_EQUILIBRIUM.md) | Eligible pair–triple bundles with DISTINCT assigned anchor pairs |
| [Shared-anchor rectangle](../exports/SHARED_ANCHOR_RECTANGLE_UNIFORM_EQUILIBRIUM.md) | Joint counting of one pair, both adjacent triples and full support under its capture/axis/edge conditions |
| [Payoff-domain orientation](../exports/PAYOFF_DOMAIN_ORIENTATION_UNIFORM_EQUILIBRIUM.md) | Weak orientation on the relevant hull or first-action neighborhoods, without a same-sign pair premise |
| [Cyclic favorite pairs](../exports/CYCLIC_FAVORITE_PAIRS_UNIFORM_EQUILIBRIUM.md) | Complete displayed family 0<=T<=1/4, using aggregate root replacement beyond those orientation adapters |

These classes overlap and do not form a single inclusion chain. For disjoint
solved cells, assign each table to the FIRST predicate it satisfies in this
order. Let R5 be the complement of S5 in the native domain. R5 is a
conservative residual, not the complement of every result in the repository.
Conditional compilers requiring an unproduced strategy, selector, return or
box do not add a raw solved predicate.

Use the participant-positive graph G_J: ij is an edge exactly when
J_ij>0 and J_ji>0. It has 64 labelled configurations and these eleven shapes:

| Graph shape | Triples with exactly one edge |
| --- | ---: |
| Empty | 0 |
| One edge | 2 |
| Two adjacent edges | 2 |
| Two disjoint edges | 4 |
| Triangle | 3 |
| Three-edge star | 0 |
| Four-vertex path | 2 |
| Four-cycle | 0 |
| Triangle with a pendant edge | 1 |
| K4 minus one edge | 0 |
| K4 | 0 |

No whole graph shape is marked solved by this table. Triple, grand-coalition
and passive rewards remain free. Refine each edge by the directed signs of
(L_ij,L_ji); retain labels or minimize the adjacency/sign string over player
permutations. This is the participant graph, not the singleton matrix graph.

On generic R5, exclude every off-diagonal J_ij=0 and L_ij=0, i!=j,
before selecting sources. Let
T_req be the triples failing ALL of Low, Charge and Orientation in the
pair–triple theorem, applied to r=Z. Let E_A be the pairs admitting its FULL
(F1)–(F3) certificate for triple A, with all permitted ordered roles and
lambda. The following FIRST-failure arms are disjoint and exhaustive:

| Arm | Definition, after all previous arms fail | Universal target |
| --- | --- | --- |
| `R_O` | Some edge has L_ij L_ji<0 | A_Z=0 throughout this residual arm |
| `R_F` | Full support fails all three Low/Charge/Orientation tests | Same |
| `R_T` | Some A in T_req has E_A empty | Same |
| `R_S` | All required triples have an eligible anchor, but two request the same pair | Same |

Why exhaustive: outside `R_O`, every positive pair has strictly positive
joining product. Outside `R_F`, full support has its independent test.
(F1) makes an eligible anchor the UNIQUE edge inside its triple, so each
required triple has at most one eligible anchor. Outside `R_T` and `R_S`,
the assignment is injective; the paired-support theorem gives A_Z=0,
contradicting membership in R5. Only two triples can contain a fixed pair.
Thus a general matching search reduces to unsupported triples or one shared
anchor. The eligibility counts above do not verify (F2)–(F3).

For literal tables add the boundary stratum where some off-diagonal J_ij or
L_ij is zero.
Either prove it directly, or prove all generic arms and invoke the established
density/continuity argument. Each arm still contains arbitrary magnitudes,
larger-coalition rewards and source geometry. These are four research targets,
not four nearly finished lemmas. They can be intersected with `N0/N-/Nb`;
no independence or nonemptiness of the intersections is asserted.

The entire `R_S` arm has a sharper restriction. If012 and023 share anchor02,
their(F1) certificates force T1=Z1(012)>0, T3=Z3(023)>0 and both directed
participant entries on01,03,12,23 nonpositive. Only the single-edge and
matching graphs remain. Full Low fails at large anchor odds and small
central odds; full Charge fails because its middle coefficient at02 is
T1+T3>0. Thus full **Orientation is the only remaining full-support gate**
on this arm. Under A_Z>0, both anchors must additionally receive positive
joining pressure from a central owner; otherwise pure anchor Quit is
absorbing Nash. The [complete proof and exact index countermodel](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md)
also show why both triple certificates plus full Orientation cannot alone
give a nonpositive joint bundle index. The single-edge shape also admits an
exact three-root all-bad boxed countermodel, with no full root, under all
these raw gates. That game too is
already hull-covered, and its bad annotation lies outside the reward hull.
Thus both shapes need actual source geometry or further global input; neither
can be closed by those raw gates alone. No entire `R_S` closure is inferred.

An actual continuation case of `R_O` has now been removed: the
[opposed-pair source exclusion](../exports/OPPOSED_PAIR_FULL_CAP_SOURCE_EXCLUSION.md)
fixes a hard singleton matrix and thirteen higher entries, leaving31 free.
It excludes an open four-payoff region from ALL full zero-debt closure
points, without assuming positive Never. Two forced genuine heads01 then03
produce an impossible third tail. An exact ray passes two compact
Nash-continuation layers but fails the third, even though one permitted
completion has only bad auxiliary roots there. The exclusion persists
locally under perturbation of all56 native coordinates.

For this table family, a zero-debt source in the sign chamber
u=(-A,-B,C,D), A,B,C,D>0, has a UNIQUE first incoming row:

    q2=0, q3=max(0,(2B-14A-7D)/44),
    q0=(B-q3)/7, q1=A+3q3.

These formulas follow from the immediate-Quit inequalities and active
equalities; a computed row outside the hazard cube excludes the source.
The open-region theorem lies in the01 branch and then forces03.
For unrestricted E sources the013 branch genuinely survives: a permitted
completion has an exact positive-Never013 Nash source. It cannot be removed
by source feasibility alone.

The stronger [negative-source dispatch](../exports/OPPOSED_PAIR_NEGATIVE_SOURCE_DISPATCH.md)
uses the SELECTED negative least-Never source under A_Z>0. Its all-bad root
condition is produced from minimality, rather than assumed at an arbitrary
continuation. It leaves exactly these two negative-source cases. The nonnegative
m-source alternatives are also excluded on this whole family by the
[finite solo/clock comparison](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md), Section11.
Thus every selected source under A_Z>0 is in one of these two chambers:

* u=(-A,-B,C,D), A,B,C,D>0, with B<6(A-D),C>5A+4AD-D. The first actual
  row is uniquely01; the initial013 branch is excluded.
* u=(-A,B,-C,D), A,B,D>0,C>=0, with A<1/4,D>5A/(1-4A),
  B>6(D-A), C<D(1-4A)-5A.

The initial zero1 face is completely excluded by a cofinal moving-date
argument. In the first case a nonlinear charged ledger keeps owner2 positive
through every01/03 pair cut and rules out infinite pair alternation.
The [whole-head triple-entry theorem](../exports/OPPOSED_PAIR_WHOLE_HEAD_TRIPLE_ENTRY.md)
consumes EVERY inherited zero1 exit: it compresses a genuine late singleton
row, varies that row and reconstructs all preceding Nash roots, strictly
lowering the ORIGINAL source's Never. It never gives a tail minimum status.
Consequently the first case must reach013 after finitely many actual cuts.
The bound of five pair cycles belongs only to the hypothetical zero1-ending
head used in that proof. The stronger
[first-triple normal form](../exports/OPPOSED_PAIR_FIRST_TRIPLE_NORMAL_FORM.md)
now classifies the ACTUAL first013: its complete history is exactly
01,013 or01,03,01,013. A negative0 entrance to013 and every longer
preceding alternating head are excluded. This follows from exact suffix
certificates without importing outer all-bad conditions to a tail.

At the genuine tail Y=(V,-E,T,F), E>F>0, if V>=E-F stationary child roots
make the explicit01 replacement's quiet2 comparison automatic under A_Z>0. The
necessary bounds are V<0 for the two-row history and V<3(E-F) for
the four-row history. In the immediate0<=V<E-F sector the original
source bounds force T>0 and one more actual013 row; a full01 replacement
then absorbs ALL three retained rows. Thus the immediate nonnegative-V
mode is completely excluded. No separate quiet2 guard or minimizing-tail
hypothesis is supplied.

The [low nonnegative four-row consumer](../exports/OPPOSED_PAIR_LOW_NONNEGATIVE_FOUR_ROW_EXCLUSION.md)
now also excludes the ENTIRE four-row sector0<=V<E-F, including V=0.
The original global budget forces positive owner2 caps through the actual
word01,03,01,013,013,03,01,013. A complete exact interval classifier then
produces the final ratio needed for a ninth actual013 row. Its full01
replacement strictly reduces Never across ALL NINE old rows, contradicting
the ORIGINAL m. Every bracket, quiet comparison, tail sign and account is
produced; no continuation inherits a minimum or an unproved recurring cone.
The1218-line proof is self-contained, and both whole independent reviews
reproduced all four printed programs, including35087 exact nodes with zero
pending or unresolved boxes. The programs regenerate their certificates;
no coefficient or interval-leaf payload is retained.

The four-row source therefore has V<0 OR E-F<=V<3(E-F). Those sectors and
the negative-V immediate history remain open. This is a complete source-mode
exclusion, not UE for the whole31-free-entry reward family.

There is also an explicit zero2 source cone removed in the
[method note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md), Section9. In the second
chamber put k=-Z0(02),c=Z3(23). If Z2(02),Z2(23),Z2(023)<0,
k>0, (c<=D OR c<4) and4A/k<D<(62-10k)A/(3k), cofinal pure2 compression
contradicts the ORIGINAL minimum. The strict c<4 branch uses genuine-source
feasibility to protect quiet3 after cumulative compression; it does not add
c=4 unless the old c<=D condition holds. The other zero2 sources and
strict-negative2 sources remain open.

The nonnegative-source exclusion uses exact or diffuse solo comparisons
for every proper zero set, the old two-copy comparison for all-zero payoffs,
and the old expanding clock to produce a genuine negative-payoff source
with Never<1. The clock guarantees m<1 for the ORIGINAL nonpositive-payoff
minimum, rather than substituting a different minimum. The unified raw
criterion needs only a zero-set solo cover and one negative expanding clock;
it therefore applies beyond the fixed higher-entry family. It is credited
as an application of existing producers, with no new UE reward-class claim.

The old stationary mechanism additionally forces Z2(23)>-5 on every
positive-gap table in this family, because otherwise pure3 is absorbing
Nash. Earlier geometric23 boundary examples with reward-10 fail this filter.
That observation earns no extra UE-class credit.

The second chamber has an exhaustive first-row support partition. Put
alpha=-Z0(02), v=-Z2(02), w=-Z2(23), eta=Z3(23). The actual row has
q1=0,q2>0. For C>0 only these three supports remain:

| First support | Necessary active hazards | Immediate genuine-tail information |
| --- | --- | --- |
| 02 | q0=C/v,q2=A/alpha, requiring v,alpha>0 | Y2<0; sign of Y0 is the sign of5-alpha |
| 23 | q2=D/eta,q3=C/w, requiring eta>D and0<w<5 | Y2>0; sign of Y3 is the sign ofeta-4 |
| 023 | Three active Quit equations; eliminating q0,q2 leaves a quadratic in q3, with zero-polynomial cases retained | Passive1 rewards can change the sign of Y1 in one cut; no caseI buffer is inferred |

For C=0, support2 also remains. Supports02,23 require respectively
Z2(02)=0,Z2(23)=0; support023 requires all Z2(02),Z2(23),Z2(023)=0.
These literal coefficient boundaries are retained, not removed by calling
the source generic. This is an exhaustive incoming classification, not a
consumer for those three strict-negative2 modes or their zero boundaries.
Every candidate still needs the full quiet comparisons and actual E access.

For initial23, put c=Z3(23),w=-Z2(23),K=Z1(23). On0<c<4 its genuine
tail has positive2 and negative3, forcing its payoff1 to be nonpositive.
The ORIGINAL source budget then gives the new necessary inequality

    (4+6c)w<c max(6,K+4).

The entire reverse weak-inequality regime is closed; for K<=2 this includes
w>=3c/(2+3c). A separate whole-head consumer handles a zero1 return
Y=(V,0,T,-F), V>=0,T,F>0: it closes that sector if Z0(02)<=-5,
Z0(023)<=Z0(23), and w>=8c/(c+3). It varies the forced actual pure1 row
and reconstructs the original23, lowering ORIGINAL m through every stated
equality boundary. Complete proofs are in the
[method note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md), Section13. The c=4
face, strict-negative1 reset, and other02/023 branches remain open.

The same method note's Section14 proves a precise obstruction on the
negative-V immediate branch when k=Z0(13)<=0: at the genuine tail its
current013 is the unique child Nash root, and upstream01 is more absorbing
than every competing child root. Two-layer rerooting with owner2 quiet
cannot improve original Never. This is a proof-method boundary, not an
additional game or source exclusion; a genuine tail/full-game change is
needed there.

A different full-SUM source on this SAME fixed family now has an exact
first-head producer; see Section19 of the
[method note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md). Fix the recipient
weights before t, choose a least-original-Never full-SUM minimum, and take
any compact first-contact factorization. For every sufficiently small t,
its first row is EXACTLY(p,0,0,s), with p,s bounded positive and proper,
and both0 and3 are current cap contacts. The genuine compact tail has
B0<0 and B3>0. The proof produces a genericity-free positive alpha-source
collar from Section11, bounds both bad FIRST hazards by O(t), and removes
them exactly by a two-contact deformation with strictly positive objective
derivatives. It neither asserts N1=N2=1 nor controls later bad-owner quits.

The row is Nash in the auxiliary game whose continuation values are the
TAIL CAPS B(Y), not its prescribed payoffs U(Y). It minimizes joint survival
among ALL such cap-Nash roots over that genuine tail: every alternative
scales both the original full-SUM objective and original Never by its
Continue factor. This supplies a whole-source comparison without giving Y
a native-m minimum. The remaining task is to consume this exact first03
head through its genuine compact negative0/positive3 tail. This full-SUM
reduction does not close or replace the distinct native-m cases below.

Along t->0 this full-SUM producer selects one global-alpha source with its
genuine first03 head. Section20 of the method note consumes its ENTIRE finite
caseI later-zero1 exit, retaining every preceding row and the outermost03.
It also consumes immediate01,013 tails with V>=-a, where a is the first
triple owner0 hazard. The source suffix is not
minimizing; the comparison lowers original Never at the global-alpha source.
Longer first013 histories, remaining V<-a tails and negative-owner2 continuations
remain open for THIS approach; native-m history bounds are not transferred.

Section26 of the [method note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md) gives
an exhaustive alternative for the selected fixed13 positive03 sources at
EVERY fixed real k=Z0(13). For all sufficiently small raises, at least one
of the following holds in each genuinely represented tail, with a positive
lower bound depending on the table and the fixed prices.

| Surviving event | Restriction |
| --- | --- |
| Strictly ordered clocks | With probability bounded below, 0 and 1 choose Never and the finite owner2 clock rings strictly before the finite owner3 clock. The first coalition is the singleton 2. |
| Joint exit involving 2 and 3 | At least one of the exact first coalitions 023 and 123 has probability bounded below. |
| Core first coalitions | Both first-exit probabilities, exactly 13 and exactly 013, are bounded below. Some date has three substantial original atoms. |

At k>=-22/5 the first two alternatives suffice. At every such selected
source, the probability of 2 stopping at or before a finite 3 is bounded
below, including ties. Section26 extends the
[positive-head barrier](../exports/OPPOSED_PAIR_POSITIVE_HEAD_FORCES_OUTSIDE_ACTIVITY.md)
by using the conditional Never payoff ranges. For smaller k, each decrease
of the potential on a protected full013 row is bounded by a constant times
the probability of first coalition 13 on that row. Before the potential
can reach zero, the clock must accumulate that probability and a definite
probability of first coalition 013. Compactness transfers the alternative
to the selected small-raise full-SUM minima via their native E limits.

The [ordered activity theorem](../exports/ORDERED_FINITE_ACTIVITY_AND_NAMED_OWNER_DISPERSION.md)
also bounds the joint order probability after EVERY old cut from original
debt and the remaining finite owner2 mass. In particular every nonempty
zero-debt suffix assigns a fixed fraction of its finite tail mass to owner3.
If owner2 is active at native E but never strictly precedes a finite owner3
draw, all finite owner2 mass is at one shared last atom. For all k the only
possible isolated last supports at native E are 023, 123 and 0123. The open
consumers include strictly ordered finite excursions, those last supports,
and the observed core collisions at k<-22/5. These are necessary events
in this family. The general Fin4 capstones are still open.

The NATIVE-m finite-history targets still include the negative-V immediate
history, the four-row sectors V<0 or E-F<=V<3(E-F), and the surviving
negative-owner2 chamber. These targets also obey forced owner2 activity
whenever their source has the stated genuine03 head at k>=-22/5.
The literal raw matrix has an entrywise strictly positive inverse, so all
proper ambient face problems above are infeasible. Every proper nonempty
cofinal tail therefore has a uniform geometric tail bound and an actual
restarted suffix;
diffuse or vanishing-relative-atom cofinal tails require all four owners.
The cofinal pair map in Section23 is exhaustive:01 and23 are impossible;
02 requires Z0(02)<-5;12 requires Z1(12)<-4;03 and13 have the stated fixed
atom-ratio bounds. Each remaining pair has a cofinal owner with NO late
finite cap contact. Therefore a literal zero-debt E source cannot have two
cofinal owners, without any perturbation of its31 free rewards. Together
with the older one-cofinal exclusion, its nonisolated END has either three
cofinal owners on an actual suffix with geometrically decaying atom tails,
or all four cofinal owners. Section23 additionally excludes the entire
cofinal012 E mode: once owner3's finite activity has ended, owner2 strictly
prefers Never at every later query if0 or1 is cofinal, because its passive
rewards on0,1,01 are1,3,4 and all its participant rewards are nonpositive.
Positive late own mass would contradict its zero debt. Thus cofinal2
requires cofinal3, and the surviving proper E triples are013,023,123.
No stationary hazard or finite-controller representation is asserted.
The oriented-pair dispersion theorem also supplies a quantitative third
mass floor on EVERY nontrivial zero-debt old suffix, using the accepted
actual-realizer conditioning argument. Hence each surviving proper E
triple has three uniformly comparable ORIGINAL terminal tails; a third
cofinal owner with vanishing relative tail mass is excluded. For all four
cofinal owners at least three tails remain macroscopic. The older collision
floor simultaneously forces cofinal pair-macroscopic bursts; it does not
turn this into a common triple collision.
Full-SUM minima may have positive native debt, so their surviving pair
modes are NOT removed by this E-only conclusion. None of these cofinal
constraints is a bound on the first013 finite-history length.

Other opposed-pair reward tables, arbitrary-source sign chambers,
nonnegative minimum sources outside this reduction's domain and both
universal capstones remain open.
No whole `R_O` or raw reward-table class is closed by these results.

The cyclic T>1/4 family is a regression test within this map, not the whole
frontier. Current source restrictions and its larger-T hull obstruction are
in the [cyclic frontier note](CODEX_ROOT__CYCLIC_TWO_MATCHING_FRONTIER.md).

## Parallel attack priorities

The following targets are alternative routes and refinements, not additional
disjoint cases to add to the counts above. A result moves the frontier only
when its complete consumer or strict coverage change is proved.

| Target | Established boundary | Next mathematical output needed |
| --- | --- | --- |
| Both source capstones | Their common pure-pair normalization is already available. A sure pair gives zero joint and deleted reach to its later tail; that tail's escape floor is not reached charge | A renewable whole-source return or contradiction, retaining the original entrance or an explicit adapter |
| Native positive-source branch | On the generic m<1 branch, P_m is compact with one kappa_m>0. Actual cofinal extraction crosses m or reaches eligibility at m in uniformly bounded macroscopic cuts; nonzero Nash-prefix chains inside P_m have finite height | Consume finite-amplitude jumps above m and compatible whole-head/tail returns; separately address the m=1 AllNever endpoint |
| Universal all-END minimum source | A strict inverse column and fixed weight box already produce all four active native END caps at EVERY small-raise original SUM minimum, with uniform original Never collar | An unrestricted all-END consumer or renewable whole-source descent; its objective cannot be replaced by native m |
| `R_S` | Only single-edge/matching graphs and full Orientation survive. Both shapes have all-bad boxed examples already solved by the hull theorem; the single-edge example has no full root | Use actual payoff/cap geometry or additional no-UE hypotheses beyond those raw gates for both shapes |
| `R_F` / `R_T` matrix test region | An explicit open singleton-matrix region passes R0/degree/Q pencil tests but has a uniform activity bound for arbitrary homogeneous switching, including unbounded phase counts and signed states when row factors stay bounded | A genuine nonlinear or finite-amplitude mechanism, or a valid actual-source budget beyond the homogeneous state space |
| `R_O` | On the studied raw family every selected source is negative. Case1 has exactly two first013 histories, whose genuine tails satisfy V<0 or V<3(E-F), with no extra quiet2 guard. The immediate nonnegative-V mode, larger zero2 cone and initial23 budget/zero1-return sectors are excluded | Consume the negative-V immediate and bounded-V four-row sectors and surviving negative-owner2 sources; core rerooting alone is insufficient on k<=0 |

The fixed-s crossing was already in Section12 of
[bounded crossing](CODEX_COORDINATOR__BOUNDED_CROSSING_SELECTION.md). The new
actual repair extends its uniform buffer THROUGH m on the generic m<1
branch; it leaves the finite-amplitude endpoint consumer open. The activity bound and shared-index obstruction
are proved in the [method-boundary note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md).
They rule out proposed proof steps; they do not exclude those reward tables
as counterexamples. The two universal source capstones and all four full
residual-arm targets remain open.

The reciprocal shared-anchor tilt criterion is sound, but its prospective
separating families admitted mixed stationary equilibria, including the
entire last parameter strip. It is retained internally in the method note
with no new coverage credit. The opposed-source packets provide actual
configuration exclusions and a global whole-head consumer for the zero1
exit. The single-edge and strict-security countermodels sharpen proof
boundaries, with no additional UE-class credit.

The marked price normalization also fixes the scale of the missing move.
For mu_p(r)=min_{C, d_i=0(i!=p)}(d_p+r nu), compactness gives
mu_p(r)/r->alpha and selected pivot debt o(r). A gain cr therefore requires
a fixed positive Never release; an infinitesimal Never change cannot supply
it. Summability of normalized debts over dyadic prices does not provide
chronologically linked profiles. The short proof is in the method note.

## Rules for closing a case

Every task must identify its parent predicate and all quantifiers, its exact
child predicates, an exhaustiveness argument, and a semantic output. A leaf
closes with UE against all behavioral replacements and a fixed target, or
with contradiction under the positive-gap hypothesis. A negative solution
instead needs one fixed positive exploitability gap for EVERY profile.

A return or rank step is intermediate until it supplies the complete input
of its downstream consumer. Record the actual source, minimizing objective,
law, dates, Never coordinates and gain floor that the step preserves.
Changing a source requires an explicit adapter. Every recurrent component
must be consumed or have a renewable well-founded exit; renaming or local
descent does not close a cycle.

Count progress by an entire predicate newly proved, a strict enlargement with
a separating witness, or an entire source configuration excluded. Do not count
export files, parameters sampled, stationary failures or redirected nodes as
closed classes. Before claiming new raw coverage, audit the other existing
admissions as well as S5. The next broad target is a whole residual arm or a
universal source capstone, with smaller families used to test its mechanism.
