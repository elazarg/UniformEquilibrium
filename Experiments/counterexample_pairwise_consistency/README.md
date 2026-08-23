# Pairwise consistency program for the quitting terminal exploitability witness

## Purpose

This experiment treats the remaining finite-quitting terminal exploitability witness as
a constraint system.  Pairwise inconsistency of any two necessary condition
clusters rules out the full regime.  Pairwise consistency does not prove joint
consistency, but an explicit pair model is a valuable regression and tells us
which genuinely ternary seams remain.

The terminal exploitability gap and the bounded charge of every exact
punishment-floor prefix are not separate pair tasks: together they are already
the complete open counterexample problem.  This program instead tests four
concrete pressure clusters derived from them.

## Condition clusters

All clusters must use one common finite player set, reward table, payoff
normalization, and positive margin whenever the margin occurs.

- **T — phantom tail.** A summably absorbing exact dynamic-debt tail approaches
  all-Continue, retains a positive prescribed owner value, has vanishing honest
  late-tail payoff, satisfies exact debt conservation, and has the logarithmic
  owner-opponent clock bound.
- **P — packet defect.** A normalized singleton packet satisfies its target,
  solo, and punishment inequalities and has a positive refusal defect.  At the
  counterexample-table level the refusal margin is uniform over the compact
  normalized packet family.
- **W — periodic windows.** Every canonical compatible periodic window of the
  tail is terminally exploitable by one common positive margin.  On an infinite
  set, the obstructing player and refusal-versus-phase branch are fixed.
- **C — cap and charge geometry.** The augmented tail caps remain in the boxed
  punishment-floor carrier, their limit is a zero-charge all-Continue exact
  self-loop, and exact punishment-floor paths have bounded charge.

The master launch packet is not an implementation dependency of these
experiments; the current executable scope is recorded in this directory and
in `Experiments/PROPOSALS.md`.
The mathematical audit of the first returned answer is
[`CP172_ANSWER_REVIEW.md`](CP172_ANSWER_REVIEW.md); in particular, it corrects the
phase-underfunded/refusal-floor-missing branch split.
The second returned answer's four-player collision completion is retained and
triaged in [`C172_CANDIDATE_REVIEW.md`](C172_CANDIDATE_REVIEW.md).  It evades the
singleton-lock screen but has not yet established punishment floors or finite
universal capacity.
The third returned answer is audited in
[`GP172_ANSWER_REVIEW.md`](GP172_ANSWER_REVIEW.md).  Its reusable addition is a
quantitative vanishing-collision estimate for normalized late absorption; its
four-phase Poincaré map is reconstructed exactly in
[`CP172_POINCARE_MAP_AUDIT.md`](CP172_POINCARE_MAP_AUDIT.md) with certificate
[`poincare_four_phase_audit.py`](poincare_four_phase_audit.py).  The completed
table has both a contracting phantom branch and a positive absorbing periodic
equilibrium, so it is a solved-game regression rather than a counterexample.

## Pair matrix

| Pair | Main compatibility question | Initial expectation |
|---|---|---|
| `T × P` | Can the same singleton rows support both the positive phantom owner and a strict packet refusal defect? | Highest-value possible contradiction. |
| `T × W` | Can a uniform periodic exploitability margin persist under summable absorption and the logarithmic clock bound? | Strong shared-tail problem. |
| `P × W` | Does a stabilized periodic obstruction force, or contradict, singleton complementarity? | Needs an honest packet/window bridge. |
| `P × C` | Can strict packet refusal coexist with a punishment-rational zero-charge cap? | Likely consistent; seek an exact regression. |
| `T × C` | Can the phantom tail and its augmented cap geometry coexist without realizing the cap as a suffix? | Much is formally compatible; isolate the realization boundary. |
| `W × C` | Can blocked periodic evaluation coexist with the cap self-loop, and what attachment datum is missing? | May prove that the meaningful seam is ternary. |

## Result ledger

| Pair | Status | Exact output | Consolidation decision |
|---|---|---|---|
| `T × P` | Consistent for exposed equations | [`TP_TAIL_PACKET_CYCLIC_FOUR_REPORT.md`](TP_TAIL_PACKET_CYCLIC_FOUR_REPORT.md), `../../Research/Counterexamples/Pairwise/TailPacketCyclicFourWitness.lean`, [`tail_packet_cyclic_four_exact.py`](tail_packet_cyclic_four_exact.py) | Same table has a table-wide packet margin and exact phantom tail; tail occupation is pure and unfunded. Optimized and packet-from-tail provenance remain open. |
| `T × W` | Consistent for exposed equations | [`PAIR_T_W_POSITIVE_HAZARD_REPORT.md`](PAIR_T_W_POSITIVE_HAZARD_REPORT.md), [`pair_t_w_positive_hazard_probe.py`](pair_t_w_positive_hazard_probe.py) | Exact positive-hazard regression; normalized drift need not be `o(m)`. Optimized-minimizer provenance moves to a later condition. |
| `P × W` | Consistent | [`PW_PACKET_WINDOW_REPORT.md`](PW_PACKET_WINDOW_REPORT.md), `../../Research/Counterexamples/Pairwise/PWPacketWindowConsistency.lean` | Exact occupation-linked regression: packet refusal predicts the stabilized window refusal branch; `delivery → target` is false. |
| `P × C` | Open; exposed packet/cap equations consistent | [`PAIR_P_C_CYCLIC_PACKET_CAP_REPORT.md`](PAIR_P_C_CYCLIC_PACKET_CAP_REPORT.md), [`pair_p_c_cyclic_packet_cap_probe.py`](pair_p_c_cyclic_packet_cap_probe.py) | Full table-wide packet margin and local cap coexist, but a repeatable three-edge charge cycle defeats universal capacity. Collision rewards must kill every rotation. |
| `T × C` | Open; exposed cap-tail equations consistent | [`TC_PHANTOM_CAPACITY_REPORT.md`](TC_PHANTOM_CAPACITY_REPORT.md), [`pair_t_c_capacity_probe.py`](pair_t_c_capacity_probe.py) | Universal capacity fails off-tail in the witness. New singleton-lock screen: every positive-solo owner needs a strict joining outsider. |
| `W × C` | Interface-disconnected | [`PAIR_W_C_ATTACHMENT_SEAM_REPORT.md`](PAIR_W_C_ATTACHMENT_SEAM_REPORT.md), [`pair_w_c_attachment_seam_probe.py`](pair_w_c_attachment_seam_probe.py) | Even shared exact cap-window actions do not identify realized periodic continuation with cap annotation. The minimal ternary datum is an exact endpoint return or co-realizing suffix. |

## Shared-data rule

Two unrelated witnesses for the same reward table are weak evidence; witnesses
on different reward tables are not evidence at all.  Each pair investigation
must state exactly which objects are shared or canonically derived:

- same players and reward table;
- same positive margin where applicable;
- same tail for `T × W` and for cap data claimed to arise from `T`;
- same target or an explicit map when packet and cap coordinates are compared;
- same prefix endpoint and a proved seam law for any attachment claim.

Direct sums, coordinate shifts, rescalings, or copied witnesses must be checked
against quitting payoff zero on the Never event and against all joining
deviations.  They are not automatically harmless.

## Required output states

Every pair receives exactly one of the following statuses.

1. **Inconsistent.** A mathematical proof derives a contradiction from the
   exact two clusters on their shared data.  A Lean probe should be supplied
   when the statement fits the current API.
2. **Consistent.** An explicit exact model, preferably with rational rewards
   and hazards, realizes both clusters on the required shared data.  The model
   must be checked symbolically or in Lean; numerical near-equalities do not
   establish consistency.
3. **Interface-disconnected.** The pair has no nonvacuous shared equation
   without a named third object.  The report must state the smallest missing
   datum and formulate the resulting ternary problem.
4. **Open.** Neither a contradiction nor a witness was obtained.  The report
   must leave a precise residual system, not merely a narrative of failed
   attempts.

“No contradiction found” is not `Consistent`.

## Quantitative seam to track

For a window with pass absorption `m`, start annotation `v`, end annotation
`v'`, and periodically restarted delivery `nu`, exact Bellman telescoping gives

```text
nu-v = ((1-m)/m) (v-v').
```

Thus summability supplies only an `O(m)` numerator and does not make the
normalized delivery error vanish.  Any `T × W` closure must prove an `o(m)`
estimate, exploit the sign of this quotient, or give an exact model in which
the quotient persists.

For player `i`, the refusal evaluator has the analogous deleted-clock ratio:
its numerator telescopes against the opponents' pass mass
`1-product_t product_(j != i)(1-a_(j,t))`.  The selected owner's exact debt
ratio controls that denominator, but does not by itself control the normalized
annotation drift in the numerator.  Reports must retain these two ratios
rather than replacing them by unnormalized tail convergence.

The packet refusal defect may be the limit of the periodic refusal branch if a
packet/window occupation bridge exists.  In that case `P` and `W` reinforce
one another instead of contradicting one another; the useful output is then
the exact bridge and the additional cap/charge condition needed to turn the
refusal into progress.

## Experimental discipline

- All probes and reports remain in this directory until review establishes a
  reusable theorem or regression.
- Production modules must not import Experiments.
- Existing production theorems may be imported into an isolated Lean probe.
- Any finite solver search must record its exact domain, tolerances, and
  rational-reconstruction checks.
- Packet occupation, annotation/payoff equality, general cap realization, and
  arbitrary periodic suffix attachment may not be assumed.
- A solved pair should state whether its proof survives player extension and
  whether it respects cardinal-minimality of a hypothetical counterexample.

## Consolidation protocol

After all six reports are reviewed:

- any inconsistent pair closes the full regime;
- exact consistent pairs become permanent regression tests if mathematically
  informative;
- interface-disconnected pairs determine the triple interfaces;
- only meaningful surviving triples are launched, with priority to `T × P × W`
  and `T × W × C`.

Joint consistency is never inferred from pairwise consistency alone.

## Triple ledger

| Triple | Status | Exact output | Remaining interface |
|---|---|---|---|
| `T × P × W` | Consistent for exposed common-data equations | [`TPW_CYCLIC_FOUR_TRIPLE_REPORT.md`](TPW_CYCLIC_FOUR_TRIPLE_REPORT.md), `../../Research/Counterexamples/Pairwise/TPWCyclicFourTripleWitness.lean`, [`tpw_cyclic_four_triple_exact.py`](tpw_cyclic_four_triple_exact.py) | A one-date suffix of the cyclic tail has a fixed player-2 last-phase obstruction while the same table retains its uniform packet defect.  The tail occupation satisfies the floor but is underfunded.  Optimized provenance and the occupation bridge remain absent; global terminal instability and capacity explicitly fail on the discarded stationary self-loop. |
| `T × W × C` | Open at the full triple; exact attachment equations tested | [`TRIPLE_T_W_C_ATTACHMENT_REPORT.md`](TRIPLE_T_W_C_ATTACHMENT_REPORT.md), [`triple_t_w_c_lock_clean_probe.py`](triple_t_w_c_lock_clean_probe.py) | A lock-clean rational model has one exact tail, blocked windows, zero-seam exact cap transport, and bounded selected cap charge.  Universal capacity and optimized provenance remain unproved.  If a positive-charge cap segment is exact, finite capacity forbids a return connector; `T × W` must produce the connector or a cap-co-realizing suffix. |
| `P × W × C` | Open; exact occupation-linked negative control | [`PWC_CYCLIC_REFUSAL_CAPACITY_REPORT.md`](PWC_CYCLIC_REFUSAL_CAPACITY_REPORT.md), [`pwc_cyclic_refusal_capacity_probe.py`](pwc_cyclic_refusal_capacity_probe.py) | The linked refusal packet/window data lifts to a repeatable charge-`3/2` floor cycle in the collision-flat table, so that table fails capacity.  The general residual is an exact charged lift, including collision deviations and floors, followed by a renewable return.  One positive edge can merely spend bounded potential. |
| `T × P × C` | Open at the full triple; exposed common-data equations consistent | [`TRIPLE_T_P_C_PACKET_CAPACITY_REPORT.md`](TRIPLE_T_P_C_PACKET_CAPACITY_REPORT.md), [`triple_t_p_c_packet_capacity_probe.py`](triple_t_p_c_packet_capacity_probe.py) | One lock-clean table has a phantom tail, a table-uniform packet defect, exact bounded selected-cap transport, and no pure coalition lock.  Its tail occupation is underfunded.  Strict joining edges do not produce a mixed root or return; `O`, universal `G`, and optimized `M` remain. |
