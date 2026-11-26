# Independent reviews of the two-row continuation results

This record concerns [the retained continuation proof](../notes/CODEX_ROOT__TWO_ROW_CONTINUATION.md)
and the conditional-average extension linked below. It combines final review
reports, with the scope of each approval stated separately. These are
mathematical and exact-arithmetic reviews; no Lean command ran. No claim of
arbitrary Fin4 closure is approved. Section hashes include the heading and
end immediately before the next level2 heading, or at end of file.

## Affine stationary region

Reviewers: crossfield_conley_transport and positive_collision_literature.
Retained section SHA256:
`a5786c3b04a2af6c2ed6e1e303b6ce91bce4f34be7d95bb184f53dd56e91892e`.
Both gave FINAL PASS for delta in [0,38/25] and epsilon in
[737/1000+3delta/50,2], with arbitrary signed row offsets and all behavioral
deviations. Each independently ran the entire retained
[stationary checker](../experiments/CODEX_COORDINATOR__TWO_ROW_AFFINE_FRONTIER.py),
SHA256 `d1695483f9210cd76c5703d9d98a8791cc02eec316bfb38bdd89c3a7203e1e8b`.
Both runs exited successfully after all 9644 main rectangles and 760 refined
endpoint rectangles, including every horizontal seam and endpoint test.

Each reviewer independently reconstructed all sixty rewards and verified the
stationary fields, the shifted variable q2=t-3delta/100, and the exact positive
epsilon-recovery coefficient. Both audited the outward interval arithmetic,
exact polynomial residual bound, and automatic derivatives. Floating roots
only propose rational data; they are not acceptance evidence.

The inner-quarter-box self-map supplies an actual root; outer-box uniqueness
identifies it at every horizontal seam. The refined left-endpoint root is
explicitly included in the main outer tube. Thus the two endpoint inequalities
belong to the same continuous curve. No monotonicity of epsilon recovery or
matching between different delta slabs is needed for the stated quantifiers.

Proper hazards ensure absorption after deletion of any one player. Both
reviewers checked the actual stationary payoff identity, Bellman argument for
complete behavioral deviations, arbitrary signed offsets, and the uniform
finite-horizon bound. They compared the retained stationary prose with the
approved author proof; only headings, reproduction paths, and the clarification
of the producer's scope changed. The checker bytes are identical.

## Periodic regions

The common retained section "Periodic regions with changing supports"
has SHA256
`788063df91cf1e3a3ea5deead7d25a299fba94b42183ec4278982579ca4edf1f`.
The corner checker has an independent full rerun. Low and the enlarged
middle, upper and high covers have complete author executions and independent
mathematical, exact-algebra, source-correspondence and coverage audits, with
the individual scopes stated below. No independent complete rerun of Low or
an enlarged cover is claimed. Approvals concern the specified raw family,
all unilateral behavioral deviations, arbitrary signed row offsets, and one
fixed uniform-payoff target per game.

### Corner

Fresh reviewer: corner_final_review, with no construction contribution.
FINAL PASS for delta in [0,1/500], epsilon in [0,1843/2500]. The independent
full run of the [corner checker](../experiments/CODEX_COORDINATOR__TWO_ROW_CORNER_PERIODIC.py)
accepted 255 closed cells and 251 rejected parents, exiting successfully in
approximately 852 seconds. All four initial closed delta strips completed.
Checker SHA256:
`a7ca99c74294ff248292722745e46335b5460a4c0a0df7728bb8792b7e023a70`.

The reviewer independently rebuilt all sixty rewards and the sixteen
payoff/gap polynomials. The exact polynomial comparison, arithmetic audit
and derivative checks included signed extensions. The proof audit checked
actual-graph Newton existence, quiet-point/domain containment even on full-only
branches, persistent-hazard bridge bounds, all six derivative directions,
common-root injectivity, and complete-history continuous selection.
The corner's final self-map bound holds for every counterfactual history;
the reviewer checked it together with the exact recursive cover and geometric
opponent absorption. Separate correspondence approval covers precisely the
corner and common proof in the retained draft.

### Upper

Reviewer: upper_cover/cover_audit. FINAL PASS for
delta in [7/10,6/5], 0<=epsilon<=737/1000+3delta/50+1/2000. The completed
author run of the
[upper checker](../experiments/CODEX_COORDINATOR__TWO_ROW_UPPER_PERIODIC.py)
accepted 2764 cells with 764 rejected parents and 4323 attempts, exiting
successfully after all 25 slabs in approximately 3355 seconds. Checker SHA256:
`ef2eec38bd2213f7368208e8e5a1af9334302f8ff73ecea199c2a377c3de37b5`.

Independent AST and byte comparisons verified that all 28 function/class
definitions and the entire acceptance prefix equal the earlier retained
upper checker. That kernel was fully reviewed by
positive_collision_potential_global, including an independent full run of
its smaller cover. That earlier review reconstructed the raw reward
polynomials and audited graph residuals, point anchors, root-image
intersections, gap recentering and support signs. This checker propagates
stagewise derivative hulls of a locally Lipschitz selected graph; it does not
claim globally smooth counterfactual histories. The proof's mean-value
argument handles support seams without assuming that an exceptional line
avoids the nonsmooth set.

The new independent review reconstructed the 2000 initial rectangles by exact
rational arithmetic, checked both children of every recursive split and
failure propagation, and parsed all 25 completed slab records. Each slab's
leaf-minus-parent count equals its initial-cell count; globally 2764-764=2000.
The source hash remained unchanged. Strictly positive dyadic lower endpoints
give beta=2^-512 uniformly for persistent hazards. The reviewer checked this
bound, full behavioral deviations, signed offsets and finite-horizon
convergence. This was a static/exact audit plus completed-record inspection,
not a second full execution. Upper_cover separately checked correspondence
of the consolidated proof with the final source and reviewed proof.

### Middle

Reviewer: middle_cover/middle_audit. FINAL PASS for delta in [3/25,7/10],
0<=epsilon<=369/500+3delta/50. The retained
[middle checker](../experiments/CODEX_COORDINATOR__TWO_ROW_MIDDLE_PERIODIC.py)
is byte-identical to frozen V10, SHA256
`2eb5aa22e2f612bbdce35837aee77d1947862c45688e78b26dea86dc5ac8abf7`.
The actual execution joins a completed V7 prefix on [3/25,4/25] with counts
353 accepted/53 rejected/551 attempts and a completed V10 suffix on
[4/25,7/10] with counts 3080/981/7317. Both source versions have identical
acceptance and proposal functions; canonical V10 reproduces the prefix mesh.
Together they give 3433 accepted cells,1034 rejected parents and7868 reported
attempts. The default whole-cover command was not executed as one run.

The independent static review manually differentiated all twelve Jacobian
entries, checked the exhaustive multiaffine vertex audit, private floating
namespace isolation, complete-history kernel, strict-full rule, every anchor
and common-root link, and the selected-centre final estimate. The six finite
calendar families have period at most33. Ranking and radius updates only
propose rational certificates; every attempt receives a fresh exact check.

The completed integrity audit checked all58 slabs at296 exact vertical
probes, reconstructed the accepted closed rectangle union, and matched
completion counts and frozen source stamps. The 2399 initial rectangles
split into300 prefix and2099 suffix rectangles, agreeing with leaf-minus-
parent counts. It did not rerun the local interval inequalities or reconstruct
individual failed attempts. The reviewer approved the completed prose against
both executions, with the explicit condition that canonical Middle be replaced
by the frozen V10 bytes. That promotion condition is now satisfied.

The review also checked reversed chronology, private independent hazards,
Nash inequalities, geometric absorption under every unilateral behavioral
replacement, arbitrary fixed signed offsets and the fixed uniform target.
This is independent mathematical and coverage review, not a full independent
rerun of the enlarged Middle cover or a Lean check.

### Low

Reviewers: jacobian_speed and jacobian_speed/low_audit; additional canonical
source correspondence by global_chain. The canonical
[Low checker](../experiments/CODEX_COORDINATOR__TWO_ROW_LOW_PERIODIC.py)
is retained without changing the reviewed bytes.

The Low review passes for all thirteen closed delta bands covering
`1/500 <= delta <= 3/25`, with
`0 <= epsilon <= 737/1000 + (3/50)delta + 1/10000`.
The completed exact cover has **5364 accepted cells, 4883 rejected parents,
and 25094 calendar attempts**. The difference `5364 - 4883 = 481 = 13*37`
accounts for every initial rectangle. Bands 0--11 contribute
`4622/4178/21412`; band 12 contributes `742/705/3682`, in that count order.
Band 12 has delta scope `[1/500,2/625]`: its completed initial slices 0--34
cover epsilon `[0,7/10]` and contribute `470/435/2275`; separately completed
slices 35--36 cover `[7/10,18/25]` and `[18/25,184323/250000]` and contribute
`272/270/1407`. Their tree-count differences are 35 and 2, respectively.
Only completed scopes are counted; later partial work is discarded.
Calendar attempts may include up to four exact radius trials.

The retained canonical checker has SHA256
`1e2fd801e32a4d060d39b1d1831fd1ba01de88299721f64dba34f73ce6de5e8f`.
Actual execution used original source SHA256
`8e5e6d7936585511873533447c4bdfae26847ea92072127e2b0d8235ef3238ff`
for baseline band 0 under CPython 3.12, and V4 source SHA256
`548b998ecc42755fe79d02b5c2ec7bbbc30aa6bd6bc208805887a1b84a9d27f0`
for band 1 under CPython 3.12 and bands 2--12 under PyPy 3.12-v8.0.1.
The suffix wrapper, SHA256
`1c9d6c9cbe71784de7311662bcd1a570bb7d9d7c08540a040c5cfed1fb914718`,
pins V4, runs its unchanged polynomial audit, and calls unchanged `cover`
only for those two slices; its scoped success marker was followed by exit 0.
Canonical `--baseline-proposals` restores the original ranker; default mode
retains V4.

The mathematical review found no blocking objection in the exact thirteen-band
partition, both calendar rankers and period bound 64, or the shared
complete-history acceptance argument. The previously reviewed strict-full
rule, graph and point/domain anchors, mixed-support bridges and Schur tests,
common uniqueness links, and final contraction/self-map checks are retained.
The Low persistent-hazard bound `10^-7` supports the shared absorption,
Bellman and fixed-payoff uniform-equilibrium argument. Numerical calendars,
centers and radii remain proposals subject to exact acceptance.

Literal/AST source review and a finite audit of 1040 scoring traces checked
canonical correspondence, including ties, caught failures, driver scopes and
the unreachable private ranker binding. This preserves the corresponding
mathematical calls within the same interpreter, subject to resource budgets;
no cross-interpreter equality of floating proposals is asserted. An independent
non-provisional ledger audit checked the source/wrapper hashes, startup
identity stamps, exact rational endpoints and ceilings, cumulative counter
differences, unique assigned scopes, per-band difference 37, and total
difference 481. Its saved final output has SHA256
`2d466721bf82c1f18c41e8380097489d5b5684f992c46ff197b0b508c80c10e5`;
the independent completion review has SHA256
`9570bc90a3482f34c796ee6d27db6d9785194c085b260721e42a452cb1d54600`.
This independently verifies completion evidence; it is not a second full
cover execution, a completed rerun of the canonical source, or a Lean proof.

### High

Reviewer: global_chain. FINAL PASS for the certificate mechanism, exact algebra
and complete driver of the
[high checker](../experiments/CODEX_COORDINATOR__TWO_ROW_HIGH_PERIODIC.py),
SHA256 `5c02cd160f440388a6357e4d0b8756c36b6bffd403ed50c3412f420f178fe9eb`.
The author's unchanged full run subsequently completed delta in [6/5,3/2],
0<=epsilon<=737/1000+3delta/50+1/10000, with 2249 accepted cells,
198 rejected parents and 6009 exact attempts in approximately 2560 seconds.
All 30 tiles completed, exit code was zero, and 2249-198=2051 equals the
independently enumerated number of initial rectangles. This is one full run,
not an independent full rerun. The maximum accepted period was 13; the proved
calendar bound of 18 covers every offered word.

The independent audit symbolically expanded all raw reward, gap and explicit
hazard-Jacobian polynomials and checked every identity. It executed the exact
initial-cover driver with certificate calls replaced by rectangle recording,
then verified all closed joins and ceilings by rational arithmetic. It audited
complete histories, common-root injectivity, selected-centre return estimates
and the strict-full relaxation: only unused quiet charts can have signed
persistent hazards; their anchors and common links remain mandatory. Mixed
seams retain physical persistent charts, endpoint linkage and negative Schur
checks. The audit also checked reversed chronology, opponent absorption,
all behavioral deviations, arbitrary signed offsets and the fixed target.

Upper_cover and global_chain separately checked the Upper and High portions
against their frozen sources. The common proof now also includes completed
Middle and Low evidence. The region-specific arguments and their original
review scopes are preserved; the fresh whole-family assembly review is
recorded below against the final common-section hash.

## Outer region and whole-family assembly

The literature and periodic reviewers independently checked the singleton
contradiction against the exact bare-no-UE declaration and matrix definition
cited in the note. It applies at epsilon=10201/5400 as well as above it and
needs no sign condition on original own rewards.

The five closed periodic bands join at delta=1/500,3/25,7/10,6/5,3/2.
Their upper edges strictly exceed the affine stationary frontier on their
respective intervals. The overlaps3/2<38/25 and10201/5400<2 complete the
whole quadrant with the affine, singleton and dominated-row arguments.
The total14065 accepted cells minus7130 rejected parents equals6935 initial
rectangles. Attempt counters are not aggregated because their meanings differ.
The resulting global conclusion is UE existence, not a globally bounded-period
or exact-terminal-Nash construction: the singleton branch uses a contradiction.

Fresh reviewer final_family_review approved the final literal whole-family
assembly, and its separately tasked outer_assembly reviewer independently
checked all sixty rewards, affine recovery, sure-owner identities, Bernstein
coefficients and exact closed joins. The fresh reviewer reran the lightweight
symbolic/raw-table and initial-driver audits for all five checkers, the final
Low completion-ledger audit and the1040-trace canonical correspondence audit.
It read the exact continuation/selection proof and attempted to falsify the
graph-conditioning, signed-chart, common-root, finite-selection and
exceptional-line steps. No unresolved mathematical objection remained.
The final review SHA256 is
`7b0ad9e6aa5153862b3f6158d08d1f00c383542fb300eb7ca5fd2b1f4c8ba8c2`;
it binds the literal periodic-section hash above and the note SHA256
`6399c3f337cac490f51b0666610555e8aa01072b9301dedf19911cec5487bfdb`.
This is a final mathematical and correspondence review, not a new heavy cover
rerun or Lean execution. Export admission is assessed separately.

The separate [scope audit](CODEX_ROOT__TWO_ROW_CONTINUATION__BY_SCOPE_AUDIT.md)
checks complete applicable raw-producer selection sets at the interior
fixture, including nonstationary punishment and adaptive-ledger criteria.
Its [standalone exact checker](../experiments/CODEX_COORDINATOR__TWO_ROW_SCOPE_CHECK.py)
requires Python3 and SymPy; the coordinator reran it successfully with
SymPy1.14.0. Source SHA256:
`d5a2ed1e25f8b2d854001447c21711da8425eac26dd47e5a83fc5b87d2a2b892`.
The review SHA256 is
`48f89537cf6d9759766bff6d79c0a199f673a135e770b5708c21f7e31f9efe9e`;
scope_audit/quiet_scope independently approved the final artifact correspondence.
The review explicitly does not claim geometric disjointness from every earlier
qualitative neighborhood without a supplied radius. No inspected prior proof
supplies membership of this fixture or the completed entire family.

## Conditional-average extension of the raw class

The section "A larger class from conditional averages" in
[the root notebook](../notes/CODEX_ROOT__PROOF_MECHANISM_DIVERSIFICATION.md)
has SHA256 `e935a2bbd0ff82b1207733ee2fb1a8c7ed152666d54d004999e535431a6a1244`.
Author product_cover_fresh_review and independent reviewer
positive_collision_literature both checked this exact retained section against
the complete proof and gave PASS. The latter independently reconstructed all
raw averages, both P/Q/F identities, axis formulas and rank8 parameterizations.
Positive_collision_potential_global independently checked the main construction
and the enlarged row2 cone, then supplied the additional s2>=0 boundary case;
that contribution is not counted as an independent review of the added case.

The empty-T averaging equations are essential and correctly retained. The
larger row2 cone increases its stationary field term by term. The three-way
boundary alternative is sufficient: off the sole2 axis every player retains
absorbing opponents; on the axis, s2>=0 supplies the direct terminal and
finite-horizon bound. No opponent-deletion assertion is made for player2 in
that last case. The general EndpointCompiler declarations cited in the note
match this distinction exactly.

The eight-dimensional row families and resulting48-dimensional raw family
were checked by injective parameterization. These are coupled directions,
not independently free raw entries. The revised comparison ray changes
actual best responses and lies outside the earlier dominated-row class under
all relabelings and positive recipient scalings. The endpoint-only boundary
counterexample is valid but is not a no-UE game. The full comparison with
other producers remains unfinished; only internal retention is approved.

## Stationary exploitability gap at an interior point

Reviewers: upper_cover and upper_cover/cover_audit, independently of the
construction. Both approve the proof, including the compactness argument
for a positive stationary exploitability gap. The reviewed literal proof has
SHA256 `7e097bda0c4e4f58f61fef0813f138e91e99d878521afe0ed4345eb93add7950`;
the retained section "No exact stationary equilibrium at an interior
parameter" appends one separator newline and has SHA256
`2547b0484a3454df57db9560a2c4b7beb1e7b760a9a913345ce0f7e269025f54`.
The [exact checker](../experiments/CODEX_COORDINATOR__TWO_ROW_STATIONARY_EXCLUSION.py)
is byte-identical to the independently rerun source, SHA256
`cab19c289b1fa748463e6ac841b0e0cb78cd21d981c7247b4453896b062e204c`.

Scope: delta=1/8, epsilon=139/200, arbitrary fixed signed recipient offsets,
with at least one strictly positive original own singleton. That sign
condition is essential: with all own singletons nonpositive, AllContinue
is terminal Nash. No behavioral-profile gap or failure of UE is asserted.

The fresh static review independently inverted Gamma over the rationals and
checked its entry, row-sum and column-sum bounds. It verified the
near-origin error bounds and complementarity argument, all 81 endpoint/proper
status boxes, strict interval sign exclusions, and the mean-value zero
exclusion with arbitrary rational preconditioners. It checked that failed
floating proposals cannot accept a box, both closed split children are
retained, and incomplete runs cannot print success.

Upper_cover independently executed the full checker, including the imported
raw/Horner/Jacobian identity audit and the exact origin audit. The run exited
successfully in approximately58 seconds with exactly the author's counts:
12199 visited boxes,2757 sign exclusions,3367 Newton exclusions,16 origin
leaves and6059 splits. The leaf-minus-split identity is81. The source was
unchanged throughout both executions. This is an independent complete rerun.

Both reviewers separately checked the stationary-approximation limit.
At a nonzero hazard limit the one-date deviation inequalities imply the
excluded endpoint conditions. At zero, immediate Quit and Never comparisons,
together with the strictly positive inverse, contradict the normalized
hazard limit. Signed offsets cancel only in comparisons where absorption is
certain. The fixed-profile terminal limit of finite-average inequalities
justifies the stationary uniform-horizon consequence without assuming a
uniform absorption rate along the sequence. The final comparison paragraph
explicitly repeats the positive-own-singleton hypothesis. No Lean command ran.

## Periodic absorption bounds

Reviewer: positive_collision_potential_global. FINAL PASS for the section
"Absorption cannot vanish along periodic Nash profiles", SHA256
`700451ad0941b63b7bab5caf7e917008c3a2dd6a25f427f1c6c60e423b8a8e05`.
The reviewer independently derived the4M eta telescoping estimate, the
support inequalities, and both joint and opponent-deleted absorption bounds.
An independent Fraction elimination at all four matrix corners and the
retained exact checker verified the inverse bounds and numerical constants.
The coordinator also ran the retained embedded checker successfully.

The rectangle is exactly delta in [0,38/25], epsilon in [0,4141/5000].
The lower bounds are per period, even when period lengths vary; no uniform
per-date lower bound is claimed. The fixed-period compactness consequence
follows from the closed endpoint/Bellman equations and uniform absorption.
This review excludes any separate index calculation and supplies no new
equilibrium existence region by itself.
