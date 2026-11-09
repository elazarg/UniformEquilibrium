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
`efc069349fe5d80a6be532614c5a81507e1b4c75329b3b3b78b69b74caa45f7c`.
The corner and middle checkers are byte-identical to their independently
rerun versions. The enlarged upper and high checkers each have a complete
author execution and independent static/exact audits, not independent full
reruns. The individual scopes are stated below. Approvals concern the
specified raw family, all unilateral behavioral deviations, arbitrary signed
row offsets, and one fixed uniform-payoff target per game.

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

Reviewer: positive_collision_potential_global. FINAL PASS for
delta in [99/1000,101/1000], epsilon in [0,93/125]. The independent full run
of the [middle checker](../experiments/CODEX_COORDINATOR__TWO_ROW_MIDDLE_PERIODIC.py)
accepted 78 cells with 38 rejected parents and 206 attempts in approximately
194 seconds, matching the complete author run. Checker SHA256:
`55af0e0c2d7f8bdf430aeab08af3a8e21c2d2635726f095f49bc2977493fdb83`.

Exact extraction verified all forty adjacent initial epsilon intervals,
including both closed calendar joins. Only [3467/5000,1389/2000] uses the
period38 word; the other cells use period34. That bridge passes as one closed
cell. The audit checked complete histories, all common-root links, and the
selected-centre final estimate: possible central histories bound the anchor,
while every smooth history contributes to the variation and contraction bounds.
No continuity of calendar choice between parameter cells is required.

The middle reviewer separately approved its portion of the earlier common
proof against this exact checker and complete proof. The mathematical text
for this region is unchanged. The reviewers
checked physical chronology (the backward calendar is reversed), private
independent hazards, Nash inequalities, fixed cyclic values, absorption under
every unilateral replacement, signed offsets, and uniform finite-horizon
convergence.

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

Upper_cover and global_chain separately checked the upper and high portions
of the consolidated periodic proof. The retained section equals their common
reviewed draft after replacing the upper-count placeholder by the completed
counts and appending one separator newline. Global_chain checked that exact
correspondence against the retained section hash above. The unchanged corner
and middle arguments retain their earlier independent review scopes.

## Outer region and assembly

The literature and periodic reviewers independently checked the short
singleton contradiction against the exact bare-no-UE declaration and matrix
definition cited in the note. It applies at epsilon=10201/5400 as well as
above it and needs no sign condition on original own rewards.

The overlaps 3/2<38/25 and 10201/5400<2 justify the stated containing region
for unfinished parameters. The periodic upper edges strictly exceed
the affine stationary frontier on their respective delta intervals, closing
every epsilon>=0 there. The upper, high and dominated-row intervals join to
close every delta>=7/10 and epsilon>=0. The known ray is an additional covered subset.
No inventory-wide comparison or assertion that every point
of the remaining region is uncovered is made. The result remains internal;
it is not an export of the whole two-parameter family.

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
