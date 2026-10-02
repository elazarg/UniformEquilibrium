Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Sorin Proposition 4: current complete-DAG adversarial static review

## Verdict

Mathematical/source/quantifier static PASS for the recorded connected
representation → affine step → geometric schedule → actual paper producer DAG,
WITH its already frozen two ite-name overlays and description overlay. No new
definite repair was identified. The original Proposition 4 and Proposition 6
hypotheses/conclusions are preserved. The former's profile is internally
produced; the latter's genuine discounted-feasible-set convexity premise is
neither removed nor silently assumed.

This is not a compiler, transitive-axiom, integration, consumer or whole-paper
seal. Root's reported full build 1205 was live; no result of that build is
assumed. No Lean/Lake, shared write, Git, source snapshot, cache/worktree or
child agent was used. Source reads, hashes and in-memory context folding are
the evidence here. Frozen originals and earlier reviews remain immutable.

## Sources and exact current base

The local Sorin PDF's printed pp.151–152 were read directly: Proposition 4,
its connected-representation/geometric-schedule proof, and Proposition 6 with
its original convexity assumption. PDF SHA256:
`d09a8e78f37f9863ff40e969a90f03799967d05eb70ba28a93afab84ddfce56c`.
The classical connected-case proof source was rechecked at
[Teissier, Proposition 4.2, pp.220–221](https://library.slmath.org/books/Book51/files/07teissier.pdf).
It uses reflected-simplex regions: a boundary point reduces the representation;
otherwise the regions disconnect the source. The draft's normalized barycentric
winner regions implement this connected case, not the more general theorem
about a bounded number of connected components.

Current `Literature/Sorin1986.lean` SHA256 independently verified:
`fba6f32df9e627384edd4e5e21fec63a5e6d14e5eef83e9b07d462b1439bdfa5`.
The six original paper patch hunks match uniquely in memory, yielding
`2c88f34cbf93c047d5d42efbba92016a86ab5b33686c5c054a7fbe9cc6722156`.
The doc overlay then yields
`bfaac016cff33d49bb67f174ed79860bd0fe0ff94b7cad3549f9edc511c3456a`.
These equal the fresh handoff, which supersedes older paper-base hashes in
the historical source records. The current Proposition 15 implementation is
outside all changed hunks. Its private scalar helper keeps its exact interface.

Fresh context record:
`/tmp/sorin-p4-closed-p15-consumer-handoff.3qJCYkPz/SOURCE_SCOPE_AND_CONTEXTS.txt`,
SHA256 `75fb2fdc35012bdf2ef173a7c847579f9610630b79633579612faf71cfadeaa3`.
Ordered DAG record:
`/tmp/sorin-p4-current-dag-audit.3RqIesTx/ORDERED_IMMUTABLE_P4_DAG.txt`,
SHA256 `e9138f031c52cc81f73185fb1d9ddb43227585147199d2844695a72f9e14895c`.
Both records, all patch bodies, source records and all three harnesses were
read fully. Earlier independent detailed reviews were also reread; this review
refreshes their mathematical checks against the actual current paper closure.

## 1. Preconnected representation: no path or compactness premise

Future owner: `MathUE/Topology/ConnectedConvexHullRepresentation.lean`.
`Math.Topology.exists_small_finset_of_mem_convexHull_isPreconnected` takes ANY
preconnected subset of a finite-dimensional real normed space and an actual
point of its convex hull. It produces a NONEMPTY finite subset of THAT source,
representing the SAME point, of cardinality at most max(1,finrank). It does not
assume a finite/closed/compact source, a supplied path, positive dimension,
source nonemptiness, favorable simplex or favorable coefficients.

The canonical `exists_minimal_affineIndependent_finset_of_mem_convexHull` and
`exists_pos_weights_of_minimal_convexHull_family` in
`MathUE/Topology/FarthestPointContactHull.lean` genuinely have the generic
module hypotheses used here; their placement before the inner-product section
does not import an extra metric-contact premise into this API. The selected
family is cardinality-minimal among ALL finite source representations, and its
weights are internally strictly positive. The containing-subset argument to
the positive-weight helper correctly preserves that minimality.

If the family is already small, it is returned. Otherwise the ambient rank
bound forces exactly dimension+1 vertices and more than one vertex; affine
independence therefore supplies an actual full affine basis. For dimension
zero this alternative cannot occur: the first branch returns one point.
An empty source causes no illicit choice because hull membership itself would
already require the nonempty canonical family.

Normalized scores are barycentric coordinates divided by the positive target
weights. Each old vertex is a strict winner for its own label. The reusable
`exists_tied_max_of_isPreconnected` selects a finite maximum at every source
point; absent a tie, each winner fiber is a finite intersection of relatively
open strict inequalities. A continuous map from the preconnected source subtype
to the discrete label type must be constant, contradicting the two internally
constructed different vertex winners. No path or compactness is smuggled into
this argument. The helper's strict-winner premise is discharged by the final
representation theorem, not left as a final favorable witness input.

At a tie, the maximum is positive because barycentric coordinates sum to one.
Its inverse is positive. Subtracting that inverse times each barycentric
coordinate from the original positive weight gives nonnegative residuals;
the two tied residuals are zero. Remaining residuals plus the new source point
have total weight one and represent the original target exactly. Negative
nonmaximal barycentric coordinates are allowed and do not spoil nonnegativity.
The Option-indexed replacement handles an empty remaining family. Erasing two
distinct old vertices and inserting at most one source point strictly decreases
cardinality, even if that new point duplicates a retained point. Contradiction
is against the internally selected global minimum-cardinality family.

Pinned canonical APIs were checked for the preconnected subtype/discrete-map
argument, continuous affine-basis coordinates, full-span rank criterion, zero-
term Finset.sum_erase, finite convex sums and erase/insert cardinalities. No
sign reversal or extra supplied topology/choice object was found.

## 2. Affine peeling: actual source point and residual

Future owner: `MathUE/Topology/ConnectedConvexHullAffineStep.lean`.
`Math.Topology.exists_affine_step_of_mem_convexHull_isPreconnected` retains
0≤weight<1 and weight·max(1,dimension)≤1. It internally obtains the preceding
finite family, finite convex coefficients, and a coefficient maximizing on
that nonempty family. Its coefficient is at least the prescribed weight:
the maximum times family size is at least one, whereas prescribed weight
times family size is at most one. Strict positivity of family size is derived.

Subtracting the weight at that one selected vertex leaves nonnegative
coefficients; division by 1−weight>0 normalizes them. Their sum is a residual
in the SAME convex hull, and the returned affine equality is exact. No supplied
large coefficient, selected stage, maximizer, compact carrier or path enters
the final generic interface. Weight zero is allowed; weight one is correctly
excluded from this division-based step. Dimension zero retains the one-point
correction and is not silently excluded.

The already frozen proof-name overlays replace if_pos/if_neg and both if_true
references by their pinned canonical names. They must BOTH be applied. The
remaining mathematical interfaces are unchanged by those overlays.

## 3. Generic schedule and legitimate infinite telescope

Future owner: `MathUE/RealSeries/GeometricAffineSchedule.lean`.
`geometric_sum_eq_of_bounded_affine_recurrence` is the promoted existing
private Sorin scalar telescope, not an independent second derivation. An
in-memory comparison against the CURRENT paper confirms its proof body is
identical after renaming the bound variable δ to weight and trimming whitespace.

For 0<weight≤1, beta=1−weight belongs to [0,1). Bounded residual states make
the geometrically weighted state series summable. Its successor shift is
summable too. The affine recurrence identifies each weighted stage with the
difference of successive weighted states, so the subtraction of infinite sums
is justified and telescopes to the initial state. No exchange of divergent
series or assumed vanishing remainder is used. The stage-weighted series is
controlled by this identity and positive weight; a separate stage bound is
not needed as an input.

At weight one, beta is zero, the zeroth term uses 0⁰=1, all later weights
vanish, and the recurrence identifies initial state and first stage. There is
no division by beta or by 1−weight in this theorem. Weight zero is deliberately
outside its hypotheses.

`exists_geometric_schedule_of_bounded_affine_steps` takes a generic bounded
region and an actual one-step affine representation at EVERY region point.
It chooses current stage and next residual internally at each subtype state,
then uses Nat recursion. ONE stage sequence precedes all coordinate conclusions.
Neither finite coordinate/stage types nor a nonempty stage instance, supplied
orbit, limiting value, schedule or delivered-payoff certificate is assumed.
The actual initial membership and step relation supply all choices. A generic
step premise is appropriate here; the source-facing paper producer constructs
it rather than exposing it as a favorable certificate.

## 4. Literal Proposition 4 and independent behavioral realization

Owner: `Literature/Sorin1986.lean`, namespace `Literature.Sorin1986`.
The declaration `proposition_4` retains EXACTLY 0<lam and
lam<1/Fintype.card G.Player, concluding equality of actual discounted feasible
payoffs and the correlated feasible hull. Positive player count is derived:
at zero players the two inequalities contradict real division by zero. No
Nonempty-player premise is added. The bound also yields lam<1 and the correct
ambient finrank/max identity. No threshold equality, lam=0 or lam=1 extension
is claimed. The generic weight-one theorem does not change this paper scope.

`property_1_finite` at horizon one and
`finiteFeasiblePayoffs_one_eq_oneStageFeasiblePayoffs` internally supply a path
in the actual one-stage independent-payoff image. The new
`PathConnectedSet.isPreconnected` only converts that available fact for the
generic theorem; the final paper statement assumes no path. Mixed payoffs
belong to the correlated hull, pure payoffs belong to the one-stage range,
and hull minimality gives the exact hull equality. The one-stage range itself
is NOT assumed convex.

For EVERY residual hull point, affine peeling selects a point of that actual
range, whose membership produces an actual independent mixed stage profile.
The finite pure-payoff hull's compactness supplies boundedness internally.
This compactness is an actual-game fact used by the schedule, not an extra
restriction on the generic connected-representation theorem.

`mixedSequenceBehavior` assigns each player/date/public history the selected
stage's PMF marginal, ignoring the history. The existing
`expectedStagePayoff_mixedSequenceBehavior` proves its stage payoff under the
actual history distribution using the independent product action law.
The new private `FiniteStageGame.discountedPayoff_mixedSequenceBehavior`
unfolds the SAME normalized discounted payoff and delegates to that identity.
No correlated stage is incorrectly treated as an independently mixed profile;
correlation in the target is realized by the deterministic time sequence.

The produced behavior delivers the SAME supplied target exactly at the SAME
discount parameter. It may depend on both; no uniform-in-discount common profile
is claimed. The result is payoff FEASIBILITY, not Nash, a unilateral behavioral
deviation cap, uniform equilibrium, finite support in time or periodicity.
The private series identity is valid algebraically for all real parameters in
the existing total-tsum convention; it does not assert convergence or a
probability interpretation outside the valid discount interval. The doc overlay
correctly says no geometric-law or delivery certificate is required, not that
the arbitrary input sequence is absent.

## 5. Original Proposition 6 and closed-P15 compatibility

`proposition_6` retains 0<lam≤1 and Convex of the ACTUAL discounted feasible
set at lam, then every 0<delta<lam yields the original set equality. The entire
preexisting bounded-payoff and actual root/continuation decomposition proof is
unchanged. That proof uses the original convexity hypothesis to identify the
lam-feasible set with the correlated hull. It treats lam=1 separately and
does not divide by 1−lam at that endpoint.

Only the final duplicated choice recursion and payoff-telescope implementation
are replaced by the generic schedule and actual-sequence identity. Reordering
the existing next/current existential witnesses is legitimate and supplies the
SAME actual affine step, target and smaller discount. No new convexity, favorable
profile, stage-value or residual certificate is introduced. In particular this
is not an unconditional claim about arbitrary larger discounts.

The private `discounted_sum_eq_of_affine_recurrence` retains its exact name,
arguments and conclusion and delegates to its promoted MathUE owner. Existing
P15 consumers at 3/4 therefore retain their interface. The P4 patch does not
change the now-closed Proposition 15 statement or body. This is verified static
compatibility, not a new compiler/axiom regression seal; the fresh harness
appropriately prints Proposition 15 again after the promotion.

## Immutable hash map and exact order

All hashes independently verified. Under
`/tmp/connected-convex-hull-representation.hYZuV5t9/`:

- 001_CONNECTED_CONVEX_HULL_REPRESENTATION.patch:
  `2b1d72e843a889ff409fe661a324ed2ef8e872e1371ca73ac1c7ae947b91b87a`.
- 002_MATHUE_UMBRELLA.patch:
  `b9e26c4ab53d9b27deb5e4c47eeaa6c05001da0b22b283d2fe54855c3aee961d`.
- SOURCE_AND_DEPENDENCIES.txt:
  `2329010e6f38a0c2d40d4580d8af7c906d993c83d92d0f5fa72afe25443bdae0`.
- AXIOMS.lean:
  `88ddf6ceb2932393a1bba1f11dfca581ffb8428fb4727a853002cde24efcd758`.

Under `/tmp/convex-geometric-schedule.upl3Iu3u/`:

- 001_CONNECTED_AFFINE_STEP.patch:
  `b1888265a2e06d9f59f80faab34ca10f8bbab82cbaa967ff5fdeb26539526e8e`.
- 002_GEOMETRIC_AFFINE_SCHEDULE.patch:
  `d6f5c9fb008c237f9283bf153ae47312178f40e6f40253dab5e6225a6bcefb5e`.
- 003_SORIN_P4_AND_SCHEDULE_DELEGATES.patch:
  `698e5f93b07b19b9bee19c26c3933603b75498aee9bd9258ba5208c6fd1200ba`.
- 004_MATHUE_UMBRELLA.patch:
  `a92f9e28095f60ed34c02116ae19070b48d2a06eb863d917e6d47128b645d563`.
- SOURCE_AND_DEPENDENCIES.txt:
  `5d69cfd7fab246ec0329913bca518aae39b5d742c038b0525206c9b9dcc548f4`.
- AXIOMS.lean:
  `be82923b9524983f009a8fda8e173d98b975d7aa73eede3ff068a0a6c10a9305`.

Existing overlays, in order after affine 001 and paper 003 respectively:

- `/tmp/sorin-p4-proof-doc-overlays.sum3X38q/001_NONDEPRECATED_ITE_PROOF.patch`:
  `7f8ad16825ef3c3169286403ff461c6778f9d29e91bced6374ff81e3b40efcbe`.
- `/tmp/UE_P4_AFFINE_STEP_ITE_TRUE_OVERLAY_20261002.patch`:
  `5c8ca5087bcd4578d05504967a49144128a095e55cb71ecc7752212acddae1a1`.
- `/tmp/sorin-p4-proof-doc-overlays.sum3X38q/002_ARBITRARY_SEQUENCE_DOC.patch`:
  `b9e3ad80b039e8c36c053e7847b2c3584fd381b9f8f36256e576e2c3172b8749`.

Current generic canonical owner `MathUE/Topology/FarthestPointContactHull.lean`:
`c5cc87c89cb647a91cfb42d65227bf7052f6611146f756b6d6345260c5d51a94`.
Related existing `MathUE/FixedRatioConvexity.lean`:
`db5d8f1e50a9ede0e5fca97820ad34495529c639ceaa3cd72d910dd08bea2f88`.
The new geometry uses the canonical minimal-family/positive-weight foundations;
the schedule moves and delegates the existing scalar proof. No duplicate
generic connected-representation/schedule owner was found in the inspected
production sources. MathUE never imports Literature or game semantics.

Current MathUE.lean base:
`da0db723744cb4fd625a028ce4cca573210df3e588f42dd318d57414df090156`.
Connected umbrella insertion result:
`f4c1d66b67cb247d1c7348ed2e2c1ed52ac5853aa8d809f6f3f803352e529f0b`.
Affine/schedule umbrella insertion result:
`d41f6d00eef360f09222b436b86682551b8ea38ebac35ead3aff3db1197661c4`.
All these contexts matched uniquely in read-only in-memory folding. Umbrella
wiring can remain deferred until root's relevant named module checks pass.

## Harnesses, source limitations and next evidence

Fresh consumer harness:
`/tmp/sorin-p4-closed-p15-consumer-handoff.3qJCYkPz/AXIOMS_P4_ACTUAL_CONSUMERS_AFTER_CHECKS.lean`,
SHA256 `eeb838f56825662c61299182e78568b02f3dde1538fc88ae8705053a1de6cd3d`.
Its two actual-profile consumers simply unfold membership in the actual payoff
range after the P4 or P6 equality. They preserve the original target and rate,
and P6's explicit convexity hypothesis. All nine print targets are appropriate;
the separate connected harness covers the two generic representation theorems.

The paper still has other open declarations; the intended P4/P6 closure does
not appeal to them. Only root's transitive print-axiom results can certify that
no sorryAx entered these consumers. No proof body of an unrelated open paper
claim was changed or treated as a proved premise here. Only propext, Quot.sound
and Classical.choice may appear in the intended successful audit.

The previous independent reviews remain useful detailed records:
`/tmp/UE_CONNECTED_CONVEX_HULL_STATIC_REVIEW_20261002.md` and
`/tmp/UE_SORIN_P4_GEOMETRIC_SCHEDULE_STATIC_REVIEW_20261002.md`.
Their old-base/application-order status is historical; the fresh bases above
are the current ones. The previously requested ite repairs are already in the
ordered DAG. No additional proof or context overlay is requested by this audit.

Remaining evidence belongs to root after the frozen full gate: check the three
generic modules, apply/check the paper delegation, run connected and actual
consumer axiom harnesses, then regenerate/check the appropriate inventories,
imports, trust and full integration gates. Until that happens, this remains
an independently reviewed known-proof formalization draft, not a newly checked
Proposition 4 or a whole-paper completion announcement.
