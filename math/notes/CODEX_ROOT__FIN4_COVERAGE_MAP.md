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
| `N-`: alpha<1, delta_m<0 | Every alpha-source is strictly positive; alpha<m<=1. Select an m-source with a negative coordinate; EVERY root there is proper with strictly positive successor coordinates | Open. A good root at that selected source, or a valid comparison lowering m, suffices |
| `Nb`: alpha<1, delta_m=0 | Every alpha-source is strictly positive; alpha<m<=1. Every m-source has nonnegative payoff with a zero coordinate; its only good root is AllContinue, and strict-negative all-bad annotations accumulate there | Open. Local good-root control at all nearby strict-negative annotations, or a finite-word comparison lowering m, suffices |

This is genuinely disjoint even if one table has both negative and boundary
m-minimizers: the secondary minimum delta_m sends it to `N-`. Exhaustiveness
follows from the global least-Never dichotomy and delta_m<=0. The strict
inequality alpha<m follows from compact attainment: equality would give an
alpha-minimizer with a nonpositive coordinate. The alpha- and m-sources are
generally DIFFERENT points. Nearby bad annotations need not be actual payoffs.

There is a raw security filter on these cases. If for each i some a_i>0
satisfies Z_i(T+i)+a_i Z_i(T)>=0 at every nonempty opponent coalition T,
hazard1/(1+a_i) guarantees0 against every complete opponent law. Every
actual cap and every zero-debt closure payoff is then nonnegative: `N-`
is absent on that class. With all these inequalities strict and Gamma R0,
every ACTUAL ALL-END profile with a zero cap is AllNever. Other zero-cap
ALL-END endpoints must be unattained. Two zero caps force every owner's
finite stopping probabilities before any fixed date to vanish along
realizing sequences; original Never may still be below1. The
[proof and scope](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md) retain this remaining
compact-limit seam. These are source filters, not a new UE game class.

Here a good root q is an auxiliary Nash root with some q_i=1 or with a
successor payoff coordinate <=0. The precise source comparison and the open
neighborhood consumer are in
[payoff-domain orientation](../exports/PAYOFF_DOMAIN_ORIENTATION_UNIFORM_EQUILIBRIUM.md).
Under the further genericity in Section9 of the
[global source theorem](../exports/GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md),
`N0` requires EVERY matrix Gamma-tJ, 0<=t<=1, to be R0, standard Q and of
degree1. A crossing excludes `N0` only; passing the pencil settles no branch.

The marked actual/mixed endpoint program additionally assumes a positive
inverse column Gamma^(-1)e_p>0. Its thirteen endpoint zero faces are a
conditional refinement, not thirteen additional universal reward classes.
An inherited endpoint must improve the whole head's constrained obstacle
objective, not just its own debt. Its exact objective and observer constraints
are retained in the
[actual-minimum note](CODEX_ROOT__ACTUAL_MINIMUM_AND_MIXED_ENDPOINT.md).

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
give a nonpositive joint bundle index. Good anchor-dropout faces must be
controlled. No entire `R_S` closure is inferred.

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
The exported region lies in the01 branch and then forces03. The013
branch, nonpositive outsider continuation caps, and failures of the tail
sign guards remain. Other sign chambers and other opposed-pair reward tables
remain open as well.
No entire `R_O` or raw reward-table class is closed by this result.

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
| Native positive-source branch | For each alpha<s<m, compactness gives kappa_s=min_{E,nu<=s} min U>0. Existing positive-buffer extraction produces a finite exact Nash head crossing s, retaining(U,B,e,N) | Control as s approaches m, where kappa_s may vanish, followed by compatible joint head/tail revision at a zero face |
| `R_S` | Only single-edge/matching graphs and full Orientation survive. In the matching shape, the raw gates alone admit a seven-root all-bad boxed example, already solved by the hull theorem | Single edge: force a good face or missing full-root cancellation. Matching: use actual source geometry or additional no-UE hypotheses beyond those raw gates |
| `R_F` / `R_T` matrix test region | An explicit open singleton-matrix region passes R0/degree/Q pencil tests but has a uniform activity bound for arbitrary homogeneous switching, including unbounded phase counts and signed states when row factors stay bounded | A genuine nonlinear or finite-amplitude mechanism, or a valid actual-source budget beyond the homogeneous state space |
| `R_O` | One complete open source region is excluded by two forced actual continuation rows; first-action and pointwise good-root tests do not exclude it | Extend the actual-cut classification to the013 branch and remaining sign guards, then to other opposed-pair tables |

The fixed-s finite crossing is a consolidation of Section12 of
[bounded crossing](CODEX_COORDINATOR__BOUNDED_CROSSING_SELECTION.md), not a
new source branch closure. The activity bound and shared-index obstruction
are proved in the [method-boundary note](CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md).
They rule out proposed proof steps; they do not exclude those reward tables
as counterexamples. The two universal source capstones and all four full
residual-arm targets remain open.

The reciprocal shared-anchor tilt criterion is sound, but its prospective
separating families admitted mixed stationary equilibria, including the
entire last parameter strip. It is retained internally in the method note
with no new coverage credit. The opposed-source packet is the new actual
configuration exclusion, not another renamed normalization or controller
obstruction.

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
