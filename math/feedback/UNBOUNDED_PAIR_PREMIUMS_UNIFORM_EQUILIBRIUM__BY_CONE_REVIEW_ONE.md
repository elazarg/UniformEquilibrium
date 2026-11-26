# Independent full mathematical review of unbounded pair premiums

Verdict: PASS for the two stated raw-table regions and their unrestricted
behavioral uniform-equilibrium conclusion. I found no unresolved mathematical
objection. This is an ordinary mathematical review; no Lean compilation or
formal verification is claimed. Fin4 remains open.

Reviewed candidate: `math/notes/CODEX_COORDINATOR__UNBOUNDED_PAIR_PREMIUMS.md`,
SHA256 `73299073b6177910a2d6ab1a0f4b2a67eec56669058116750ae7b1d43ca5c715`.
The verdict follows these exact bytes if the file is moved unchanged.

Reviewed executable certificates:

- `math/experiments/UNBOUNDED_PAIR_PREMIUMS_POSITIVE_CHECK.py`, SHA256
  `2f899cee1985c1e598bbe5fa9e1c39527d22585bdd662949307f67b50c53bb86`.
- `math/experiments/UNBOUNDED_PAIR_PREMIUMS_NEGATIVE_CHECK.py`, SHA256
  `4e726f3ebec6e2b8832bcf111d36932ae248e2887ad909cbacbc2baaaccfcd6f`.
- `math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py`,
  SHA256 `724f1829449c8f7bbdbe5effdb9cc6ee26be065892e7beedd7a9ae5ce7440eaa`.

## Scope and produced inputs

The complete theorem covers K>=100,p>=2K and
K>=0,p<=-max(200,2K), for the displayed singleton/core rewards, seven
nonpositive row0 joining coordinates, 21 unrestricted other joining
coordinates, and arbitrary original own-singleton levels. It does not cover
the whole (K,p) plane. No strategic input remains assumed: the positive
region produces its scalar return by interval-certified endpoint signs and
IVT; the negative region produces its eight variables by a uniform weighted
contraction. Both supply the actual calendar, all continuation annotations,
all active comparisons, all quiet comparisons, a fixed target, and the
approximation/properness bounds used by the semantic consumer.

## Independent checks of the proof

I rederived the three active core successor formulas by enumerating the
literal opponent coalitions, and independently checked their symbolic
identities. I also checked the polynomial elimination
F1-9F2/4=alpha E0+beta. The positive compactification keeps y,z,w strictly
physical for every physical parameter. Its artificial edges u=0 and t=1
are used solely for a uniform sign calculation, not as strategies.

For the positive pair word I checked active indifference, telescoping
survival, both singleton masses and the collision mass. The quiet0 value is
bilinear with the four stated corners. The quiet3 surplus is affine in B;
on the nontrivial triangle edge its three Bernstein coefficients are exactly
those in the packet. The last coefficient is u times the certified scaled
expression, so its vanishing at artificial u=0 does not invalidate any
physical strategy. The triangle comparison uses both p>=2K and 2L>=X and
holds at every suffix, not merely at the initial pair point. Thus an
arbitrarily long finite pair word remains legal. Its entrance converges to
the stated C; only the solo2 Continue/prescribed identity acquires the
claimed vanishing residual. The return root is chosen before accuracy.

For the negative region I verified that matching the scaled row3 equations
is equivalent to physical matching whenever s>0, that the first row2 and
last successor row3 vanish identically, and that the parameter rectangle
covers the entire claimed raw region, including K=0. The row0 propagation
is the literal coalition polynomial. The certificate includes positivity
of all physical complements, all row0 annotations, and every outer guard.

I audited both interval implementations. The positive checker uses exact
Fraction interval endpoints. The negative checker rounds every value and
derivative operation outwards to 2^-80; midpoint Jacobians are used only to
propose rational center/inverse/radii data. The residual enclosure, image
inclusion, and weighted contraction tests are separate conservative tests.
The interval radius lower bounds appear on the restrictive side of the
strict tests, while upper bounds are used for the encompassing state box.
Invertibility of the rational preconditioner follows from its exact
Gauss-Jordan construction. The parameter mean-value bound is valid on the
whole rectangle. No floating-point diagnostic decides acceptance.

For the common consumer I checked the complete response maximum, the
finite repair including the 43-root threshold, and both solo subdivisions.
The immediate Quit errors enter a maximum, not a cumulative sum. With at
most one Continue residual per period, unrolling yields e+eta/rho for the
cap and eta/rho for the prescribed payoff. Every deviator faces opponents
with at least rho absorption probability per period, irrespective of its
private timing law. This supplies uniform expected absorption time, removes
any terminal Never ambiguity in the native translation, and bounds the
finite-horizon difference uniformly over all behavioral deviations.
There is no restriction to stationary or periodic deviations, no shared
randomization, and no accuracy-dependent target.

## Falsification attempts and boundary evidence

I specifically tested the possible failures at K=0, p=2K, arbitrarily large
physical parameters, artificial compactification edges, the negative row1
repair, large positive free joining rewards, and a deviation that waits
through arbitrarily many periods. The strict certificate/triangle guards,
solo0 subdivision, and opponents-only absorption resolve these issues.
The original own levels may be negative: the argument translates terminal
payoffs only after proper opponents are established, and compares finite
horizons using the bounded original rewards directly.

I independently reran:

    python math/experiments/UNBOUNDED_PAIR_PREMIUMS_POSITIVE_CHECK.py
    python math/experiments/UNBOUNDED_PAIR_PREMIUMS_NEGATIVE_CHECK.py
    python math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py 400 200
    python math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py -300 150
    python math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py

The positive sign calculation accepted 9,16,4 boxes at depths 4,4,2.
The negative calculation passed its one box; its diagnostic inclusion ratio
was approximately .414914, contraction bound .081049, and minimum guard
.0001140169. The exact decisions use integers/rationals, not these decimals.
The two new separating completions excluded all 80 nonzero stationary
patterns and all 65 sure-root patterns with counts (5672,729) and
(1448,331); the unchanged default gave (978,369). I audited the polynomial
necessary conditions, Never lower bound, singleton-pattern shortcut, origin
cube exclusion, rational Bernstein conversion, and exact subdivision.
These are exclusions of those strategy/root mechanisms, not counterexamples
to UE and not stationary exclusions for the whole two-parameter class.

## Coverage and source audit

The two-parameter regions contain games outside the preceding fixed K=100
family. I independently enumerated all 24 relabelings and positive row
scalings preserving the displayed singleton matrix; only the identity
permutation and unit scales survive. Thus the new examples cannot be
recovered from that scalar family by these equivalences.

I checked the named finite-selector obstructions in Section 6. Direct exact
matrix calculations give the unique nonnegative-inverse principal triple
023 and its exterior row (-3,6,2)/5, the mixed-sign inverse column2, and
the unique attached-pair labeling (3,1,0,2). The positive singleton graph
forces every admissible nonempty marked set to be the full set; the
positive participant vector at123 then rejects every first-block choice
and positive weight selection. The three pair partitions each fail the
stated mandatory positive joining difference, so allowing arbitrary cone
proof weights does not repair them. The unique positive and negative
singleton pairs intersect, excluding the signed four-cycle templates.
I inspected the raw hypotheses of the ordered-anchor, attached-pair,
finite-invariant-cone and signed-inverse-column packets when checking these
claims. This is a strict increment among these named mechanisms, not a
claim to have classified every possible sufficient theorem.

The exact source declarations inspected were
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Their complete-behavior and terminal-to-uniform scope matches the use here.
The packet also proves the required finite-horizon statement directly.

The assembled artifact supplies the mathematical definitions, exact
algorithms, raw separating games, complete behavioral consumer and
formalization handoff without a proof dependency on conference files or
untracked scripts. It meets the mathematical export gate for the stated
new existence regions, subject to the independently required second full
review and ordinary final repository checks.
