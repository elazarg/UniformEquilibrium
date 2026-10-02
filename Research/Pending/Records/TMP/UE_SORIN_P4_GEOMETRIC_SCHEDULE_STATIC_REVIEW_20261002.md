Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Independent static review: convex affine peeling, geometric schedule and literal Sorin P4

Verdict: mathematical/source/quantifier PASS. One definite warning-policy
repair remains beyond the supplied overlays: two deprecated `if_true`
references in original001 must become `ite_true`. A separate frozen
proof-only overlay is supplied below. No other definite API failure was
identified; elaboration and axiom checks remain root-owned and unperformed.

All four patches, source/dependency record, full harness, read-only context
checker and both separate overlays were read. Sorin printed p.151 and the
exact canonical declarations used by the adapters were inspected. The
connected convex-hull prerequisite already has its separate independent
static PASS, not a compiler seal. No shared writes, compiler, Git, caches,
worktrees, child agents or math-note edits were performed.

## Frozen hashes and proof-only repair

Main directory: `/tmp/convex-geometric-schedule.upl3Iu3u`.

```text
b1888265a2e06d9f59f80faab34ca10f8bbab82cbaa967ff5fdeb26539526e8e  001_CONNECTED_AFFINE_STEP.patch
d6f5c9fb008c237f9283bf153ae47312178f40e6f40253dab5e6225a6bcefb5e  002_GEOMETRIC_AFFINE_SCHEDULE.patch
698e5f93b07b19b9bee19c26c3933603b75498aee9bd9258ba5208c6fd1200ba  003_SORIN_P4_AND_SCHEDULE_DELEGATES.patch
a92f9e28095f60ed34c02116ae19070b48d2a06eb863d917e6d47128b645d563  004_MATHUE_UMBRELLA.patch
be82923b9524983f009a8fda8e173d98b975d7aa73eede3ff068a0a6c10a9305  AXIOMS.lean
5d60a12e4fae1eb12865605a2347acd551a3a673e0bfe62264eed0953e2fbe53  HASH_PATCHES_IN_MEMORY.pl
5d69cfd7fab246ec0329913bca518aae39b5d742c038b0525206c9b9dcc548f4  SOURCE_AND_DEPENDENCIES.txt
```

Existing overlays under `/tmp/sorin-p4-proof-doc-overlays.sum3X38q`:

```text
7f8ad16825ef3c3169286403ff461c6778f9d29e91bced6374ff81e3b40efcbe  001_NONDEPRECATED_ITE_PROOF.patch
b9e3ad80b039e8c36c053e7847b2c3584fd381b9f8f36256e576e2c3172b8749  002_ARBITRARY_SEQUENCE_DOC.patch
a26f86cf04df79af947c386eae7be3344f7c88fc6846b8c5a5914f2ea4d63f98  SOURCE_AND_DEPENDENCIES.txt
```

New separate repair:
`/tmp/UE_P4_AFFINE_STEP_ITE_TRUE_OVERLAY_20261002.patch`
SHA256 `5c8ca5087bcd4578d05504967a49144128a095e55cb71ecc7752212acddae1a1`.

Apply this only after original affine-step001 and existing proof overlay001.
Exact generated source base after that existing overlay:
`eb71f6f81a35b15dd059cdcddd17c69ba7d47a5eb903ff2cce88e31a7c55ad79`.
Exact resulting source:
`c4d959753e0425d48918874a55a806742a99dd77ca6ddad089aa5cb0e1123f17`.
Both new contexts matched exactly once in memory. Original patches remain
immutable. No source snapshot or shared source file was created.

Defect evidence: pinned Lean4.34 `Init/ByCases.lean` explicitly marks
`if_true` deprecated in favor of `ite_true`, since 2026-07-21. Original001
uses it in hremainderSum and hnextValue. The existing overlay fixes only
if_pos/if_neg. Replacing these two proof names is necessary under the
project's warnings-as-errors policy. No hypothesis, construction or result
changes. The final in-memory source has no remaining short deprecated
if/dif aliases among those scanned.

## 001: internally chosen affine step

Owner: proposed `MathUE/Topology/ConnectedConvexHullAffineStep.lean`.
`exists_affine_step_of_mem_convexHull_isPreconnected` accepts any finite-
dimensional real normed space, preconnected source, actual hull point,
0≤weight<1 and weight*max(1,dim)≤1. It does not require compactness, a path,
supplied coefficients or a favorable source point.

The connected representation owner selects a nonempty family of at most
max(1,dim) actual source points. `Finset.mem_convexHull'` then supplies
nonnegative coefficients summing to one. `exists_max_image` chooses a
largest coefficient internally. If n is the selected cardinality,
1≤n*largestCoefficient, while weight*n≤1 and n>0. The displayed arithmetic
therefore gives weight≤largestCoefficient with the correct signs.

Subtracting weight only at that chosen point leaves nonnegative numerators.
Division by 1−weight>0 normalizes their sum to one. The finite weighted sum
is a genuine convex-hull residual and reconstructs the SAME original point
as weight*current+(1−weight)*next. `mul_div_cancel₀` has exactly the needed
identity b*(a/b)=a, and the primed finite conditional-sum lemma matches
member=current rather than the reversed equality form.

Weight zero is retained and harmless. Dimension zero is handled by the
one-point bound; no positive ambient dimension is added. Weight one is
correctly excluded from this division-based API. The later generic schedule
has its own weight-one handling and does not call this affine step there.

## 002: canonical scalar telescope and actual residual recursion

Owner: proposed `MathUE/RealSeries/GeometricAffineSchedule.lean`.

`geometric_sum_eq_of_bounded_affine_recurrence` promotes the old private
paper scalar theorem. An independent in-memory comparison confirmed its
proof body is byte-identical after renaming delta to weight and trimming
outer whitespace. It is not a second mathematical derivation.

For beta=1−weight in [0,1), bounded state makes beta^t*state_t summable by
the geometric majorant. Its successor shift is summable. The recurrence
identifies weight*beta^t*stage_t with the difference of successive weighted
states. Thus the two legitimately summable series telescope to state_0.
No illicit exchange of divergent infinite sums or missing residual limit
is used. Multiplication through the real tsum is the existing canonical
identity. Stage summability need not be assumed: positive weight and the
bounded recurrence already imply the relevant weighted summability.

At weight=1, beta=0 and the recurrence says state_t=stage_t. The t=0 term
uses 0^0=1 and all later coefficients vanish. The same proof covers this
endpoint; no division by beta or by 1−weight occurs in the telescope.

`exists_geometric_schedule_of_bounded_affine_steps` takes an arbitrary
coordinate index, stage type, bounded region and an actual one-step affine
relation at EVERY region point. From the input point's membership, it
chooses current stage and next region point, builds a subtype-valued
Nat recursion, and applies the scalar theorem to every coordinate. The
result selects ONE complete stage sequence before every coordinate.

No finite/nonempty coordinate index or supplied nonempty stage type is
needed: the one-step relation at the actual initial member supplies the
choices. It assumes neither an orbit nor a delivered-value certificate.
The one-step relation is a legitimate generic-helper premise; literal P4
constructs it internally and does not expose it as a source assumption.

## 003: exact literal P4 and actual behavior

Owner: `Literature/Sorin1986.lean`, under its new MathUE imports.

`PathConnectedSet.isPreconnected` converts the paper's real-parameter path
definition using the preconnected image of [0,1]. Its image subset and
endpoint witnesses use the supplied path equations with the correct
orientation. This paper adapter needs no extra topology hypothesis.

`proposition_4` keeps EXACTLY its original hypotheses and conclusion:
0<lambda<1/playerCount implies discounted feasible payoffs equal the
correlated feasible hull. If there are zero players, Lean's real 1/0=0
makes the two inequalities contradictory. Positive cardinality, positive
real cardinality, reciprocal bound≤1, lambda<1, and the max-dimension
identity are all derived internally, not added as API hypotheses.

`property_1_finite` at horizon one and
`finiteFeasiblePayoffs_one_eq_oneStageFeasiblePayoffs` supply actual source
path connectedness. The hull identity is proved from actual independent
mixed payoffs belonging to the correlated hull, hull convexity, and
`lemma_1_pure_subset_D1`. There is no supplied convexity of the independent
one-stage payoff image.

For EVERY hull point, the affine-step owner selects a current payoff in the
actual one-stage range and a residual in the same hull. Range membership
then selects an actual independent mixed profile realizing that current
payoff. The finite pure-payoff hull is compact, hence norm bounded, which
supplies the schedule's coordinate bounds. No arbitrary correlated action
is played as one independently mixed stage profile.

The schedule produces actual mixed profiles, and `mixedSequenceBehavior`
maps each player/date/full public history to that date's prescribed marginal
PMF. The existing `expectedStagePayoff_mixedSequenceBehavior` proves the
exact stage payoff identity on the actual repeated-game distribution.
The new private `FiniteStageGame.discountedPayoff_mixedSequenceBehavior`
merely unfolds the canonical normalized discounted payoff and reuses that
identity; it introduces no alternate law or finite-history approximation.

The profile's delivered target is the SAME supplied hull payoff at the SAME
fixed lambda. Reverse inclusion remains `lemma_1_Dlambda_subset_C`, with a
DiscountRate internally built from the derived bounds. There is no appeal
to open P7/P11/P15, a favorable profile, or an equilibrium certificate.

The private actual-sequence identity is algebraically stated for any real
parameter using the existing total tsum definition. It does not assert
convergence/probability normalization outside valid discount rates. The doc
overlay correctly explains that the sequence may be supplied arbitrarily;
only geometric-law/delivery certificates are not required. It avoids the
misleading original sentence suggesting no schedule argument is present.

## P6 delegation and held P15 compatibility

The private `discounted_sum_eq_of_affine_recurrence` keeps its exact name,
arguments, inequalities and conclusion and delegates to the new owner.
The pending P15 vertex producer's call at 3/4 therefore retains its scalar
interface. No prior P15 fixture or final equality patch is edited.

`proposition_6` keeps all hypotheses and its conclusion. Its preexisting
actual affine decomposition and reward bounds are unchanged. Only local
choice recursion and the repeated profile-payoff telescope are replaced
by the generic schedule and private actual-sequence identity. Reordering
the existential next/current data is legitimate and uses the same
decomposition; there is no changed continuation or discount parameter.

The supplied read-only Perl checker was inspected, then run to fold exact
contexts in memory only. Confirmed future chain:

```text
036c9709b57efefbd72721f03e8c329161e28f3aa3d617614a61fd452c70ca3b  paper after matrix/scalar/upper/vertices/lower001
805186f6568a7730ca41b013039118f09a02b277d9dad677754e02c0a4ecbca8  after P4 original003 (six unique hunks)
1ab3ce53497517384d3bd61551ca4e3887fd882981ae0caf763cf3ce566c4e16  after doc overlay002
73577852b891aeee01dfc22b207c6786038ea3d06c153b5cd0808bba574e0128  hypothetical held-P15 context fold only
37358bbd1037f92f51b9378e4a3faa49b4f32112536efb158f2813741b5052d6  umbrella after scalar and connected prerequisites
702bd92ae11190797082c3c0ebbcb4287ff4ba50ea2b74930b1414dd5062358b  after original004 (two unique hunks)
```

The held P15 patch matched its one exact context after the P4/doc edits.
This is TEXTUAL compatibility only; it was not applied or authorized for
application, and P15 must remain held until predecessors and axiom gates pass.

## Evidence limits and next checks

The final affine-step proof needs both proof-name overlays: the existing
if_pos/if_neg repair and the new two-site if_true repair. The optional paper
doc clarification targets a different file. The first two are warning-policy
repairs; the doc change is not mathematical.

The six harness targets cover affine peeling, scalar telescope, schedule,
path adapter, P4 and P6. Public P4/P6 transitively consume the private
actual-sequence adapter; the retained private scalar facade is consumed by
pending P15. Root still must check coercions/rewrite inference, norm/Fintype
instances, recursion unfolding, import/warning policy, and transitive
axioms. Only propext, Quot.sound and Classical.choice are expected, not
observed here. Other unrelated Literature sorries are not thereby removed.

These are feasibility results, NOT Nash/UE or unilateral-deviation claims.
No finite calendar, periodic schedule, constructive runtime bound, or
lambda=1/playerCount boundary claim is added to P4. No whole-paper or
whole-project seal follows from this review.
