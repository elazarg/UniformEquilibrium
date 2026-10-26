# Independent full review of the two unbounded pair-premium regions

Reviewer identity: `CONE_FULL_REVIEW_TWO`.

Verdict: **PASS**, as ordinary mathematics for the stated raw-table family
and both stated regions. No unresolved mathematical objection was found.
This is not a Lean verification or a solution of arbitrary Fin4.

## Exact artifact and scope

I reviewed the complete assembled proof intended for
`math/exports/UNBOUNDED_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM.md`, at SHA256
`73299073b6177910a2d6ab1a0f4b2a67eec56669058116750ae7b1d43ca5c715`.
During review these identical bytes were at
`math/notes/CODEX_COORDINATOR__UNBOUNDED_PAIR_PREMIUMS.md`.
Approval applies to those bytes, including the final singleton relabeling
and positive row-scaling comparison.

The claim checked is existence of one fixed uniform-equilibrium payoff for
every stated completion when either `K>=100, p>=2K`, or
`K>=0, p<=-max(200,2K)`. All unilateral behavioral replacements are included.
The seven upper-bounded row0 coordinates, 21 other unrestricted native
coordinates, and four arbitrary original own-singleton levels retain their
stated scope. The four forced native diagonal zeros are not independent
reward restrictions, and the theorem does not claim an open 60-coordinate
family or coverage of the entire `(K,p)` plane.

## Independent proof checks and attempted falsification

I read the entire proof, inspected both arithmetic implementations, and
independently ran both exact certificates. I also derived the active root
equations directly from the coalition table and checked the scaled negative
equations by symbolic rational identity. The positive pair probability
identities, all four quiet-row0 corner values, and the quiet-row3 gap identity
were checked independently as symbolic identities.

The potential failure points examined were:

- **Arbitrary finite pair length.** The hazard recurrences telescope to the
  stated survival probabilities. The actual pair points lie in the displayed
  triangle because `p>=2K` and `2L>=X`. The row3 comparison is affine on each
  vertical segment, and its second edge has the three stated positive
  Bernstein coefficients. This prices every suffix, not a bounded sample.
- **Unbounded parameters and artificial boundaries.** The positive compact
  parameter box includes only algebraic `u=0` and `t=1` endpoints; physical
  tables have `u>0,t<1`, restoring strict positivity of the final row3
  coefficient. In the negative construction `s=0` is likewise auxiliary,
  while `u=0` is the genuine allowed `K=0` boundary. No improper limiting
  profile is used as the actual strategy.
- **Uniform root production.** The positive interval subdivision proves both
  endpoint signs and every guard on complete boxes, so the least return root
  exists before accuracy is chosen. The negative implementation uses outward
  dyadic intervals, exact rational inverse proposals, and conservative radius
  tests. Its accepted Jacobian bound is a contraction on the exact rational
  radius box, and the image lies strictly within half that box for every
  parameter. Midpoint estimates select data but never justify acceptance.
- **Negative intermediate values.** Every active core comparison is exact;
  quiet row0 has a nonpositive Quit offer and positive annotation. The solo2
  row1 offer remains legal even at `K=0`. The finite solo3 repair preserves
  its guards, and the final repair root is legal under the exact 43-step
  inequality, including the wash-equality boundary.
- **Unrestricted deviations and fixed target.** Before absorption there is
  one surviving public history. The max recursion therefore controls every
  quitting date, Never, and their private mixtures. Immediate Quit errors
  enter a maximum; they are not incorrectly summed over the finely split
  calendar. There is at most one interface error per period. Opponents of
  every deviator absorb with period survival at most `1-min(a,b)`, proving
  both cap convergence and the uniform horizon comparison. For the positive
  region only the finite core and solo0 subdivision vary with accuracy;
  the return and target are fixed. In the negative region the prescribed
  terminal target is exact for every subdivision. Proper opponents justify
  the original own-level translation for every deviation.

These checks did not find a falsifier, an unpriced action, an unsupported
limit exchange, or a strategic witness left as an assumption.

## Coverage and source audit

The previous scalar collision theorem fixed `K=100`; it did not vary the two
pair coordinates independently. I checked all 24 simultaneous relabelings
and all possible positive row scales preserving this singleton matrix:
only the identity and unit scales survive. Thus the two supplied separating
tables at `(200,400)` and `(150,-300)` are not disguised scalar-family games.

I independently reran and inspected the exact stationary/sure-root exclusion
checker. Its necessary inequalities correctly distinguish stationary
opponents from roots against arbitrary actual continuation caps. The cap
floor includes native literal Never `-1` at these examples. Both complete
pattern censuses terminate, with no unresolved branch:

| `(K,p)` | stationary patterns/nodes | sure-root patterns/nodes |
|---|---:|---:|
| `(200,400)` | `80 / 5672` | `65 / 729` |
| `(150,-300)` | `80 / 1448` | `65 / 331` |

I checked the complete finite choices behind the other stated exclusions:
all principal triples, all attached-negative-pair labelings, all three pair
partitions, and the inverse-column signs. The only nonnegative-inverse
triple is `023`, with exterior inverse row `(-3,6,2)/5`; the sole attached
labeling is `(3,1,0,2)` and fails its participant-premium premise. The
positive singleton graph is strongly connected, so the positive participant
vector on `123` obstructs every ordered anchor/weight choice as stated.
The core joining charge at `12` equals 7. The mutually positive and mutually
negative pairs intersect, obstructing the compared signed four-cycle
templates. The three pair partitions each fail a mandatory joining-gap
condition, independently of any proof-weight selection. Every triple also
contains a negative required joining gap, so the all-positive-gap
triple/singleton collision-box criterion does not supply these examples.

I compared the relevant accepted scalar collision, signed inverse-column,
invariant-cone, positive-inverse, attached-pair, triple/singleton,
same-sign-pair-core, and signed four-cycle criteria. Their premises do not
erase the demonstrated increment. The examples' stationary exclusions also
exclude stationary producers and the sure-root exclusions include actual
punishment-tail caps. These are complete exclusions for the named criteria,
not an assertion that every imaginable sufficient theorem has been listed.

I inspected the tracked declarations
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Their meanings agree with the packet's response recursion and semantic
endpoint. The packet also proves its direct fixed-target horizon consumer,
so it does not rely on an unstated adapter. No Lean build was run.

The raw input-to-root-to-strategy-to-uniform-payoff chain is complete.
The export gate is met by a nonredundant existence-class extension, not by a
new verifier or an assumed continuation. Arbitrary Fin4 and the actual
global-minimum problem remain open.

## Reproduction and integrity

From the repository root I ran:

```sh
python math/experiments/UNBOUNDED_PAIR_PREMIUMS_POSITIVE_CHECK.py
python math/experiments/UNBOUNDED_PAIR_PREMIUMS_NEGATIVE_CHECK.py
python math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py 400 200
python math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py -300 150
```

The positive certificate accepts 9, 16 and 4 boxes at depths 4, 4 and 2.
The negative one-box certificate passes its exact inclusion, contraction,
and guard inequalities. Printed floating diagnostics are not used for
acceptance. The reviewed checker hashes are:

| Artifact | SHA256 |
|---|---|
| `UNBOUNDED_PAIR_PREMIUMS_POSITIVE_CHECK.py` | `2f899cee1985c1e598bbe5fa9e1c39527d22585bdd662949307f67b50c53bb86` |
| `UNBOUNDED_PAIR_PREMIUMS_NEGATIVE_CHECK.py` | `4e726f3ebec6e2b8832bcf111d36932ae248e2887ad909cbacbc2baaaccfcd6f` |
| `CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py` | `724f1829449c8f7bbdbe5effdb9cc6ee26be065892e7beedd7a9ae5ce7440eaa` |
