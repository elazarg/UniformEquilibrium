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

## Periodic band with an optional active player

Reviewer: positive_collision_potential_global. FINAL PASS for
delta in [0,10^-5] and epsilon in [.34,.36]. The reviewer independently ran the
entire retained [periodic checker](../experiments/CODEX_COORDINATOR__TWO_ROW_SUPPORT_BAND.py),
SHA256 `b10ebdfa4a39592dedebdd28d03abc36c88ee307583ddf8547846b7ce105db29`.
All twenty closed parameter cells passed. This band replaces the smaller
support-change test; its duplicate checker is not retained.
Retained section SHA256:
`18b5983991e658ba8e18571cc69da0d58acd22065bf29b723b4755425597f124`.

The audit checked implicit-root existence and uniqueness, the strict quiet
and full-support shortcuts, and the negative Schur complement in mixed cells.
The bridge contains both persistent root tubes, so the selected Nash branches
agree at zero optional hazard. Local Lipschitz gluing validates the derivative
hull. Intermediate signed bridge hazards are not interpreted as probabilities.

Point-orbit roots are explicitly included in the corresponding domain tubes.
The six derivative columns retain both direct parameter effects and the
initial moving-fibre slopes. The stagewise mean-value reset and final weighted
return inequalities therefore apply to the same selected maps. Every cell
checks contraction below 7/40, residual/radius below 2/5, and q0,q1>3/40000.
The reviewer checked chronological order, actual terminal payoffs, all
behavioral deviations, signed offsets, and the uniform-equilibrium consumer.

The shared raw table and retained proof match the approved band. Different
cells need not select the same cycle. The note was corrected to state only
cellwise selectors allowing activation, without claiming a globally identified
cycle through the band. The final correspondence check covered this wording
and the shared raw-table reference.

## Outer region and assembly

The literature and periodic-band reviewers independently checked the short
singleton contradiction against the exact bare-no-UE declaration and matrix
definition cited in the note. It applies at epsilon=10201/5400 as well as
above it and needs no sign condition on original own rewards.

The overlaps 3/2<38/25 and 10201/5400<2 justify the stated containing region
for unfinished parameters. The known ray and periodic band are additional
covered subsets. No inventory-wide comparison or assertion that every point
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
