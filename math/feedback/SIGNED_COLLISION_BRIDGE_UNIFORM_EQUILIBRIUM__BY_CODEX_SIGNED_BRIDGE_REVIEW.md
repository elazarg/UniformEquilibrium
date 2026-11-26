# Independent review of the signed collision bridge

Reviewer: `CODEX_SIGNED_BRIDGE_REVIEW`.

**Verdict: mathematical PASS and export-gate PASS for the repaired raw class
with Z3(123)=+1.** No unresolved objection remains. This is an ordinary
mathematical existence result for the stated class, not arbitrary Fin4 closure
or a new Lean-checked theorem.

The complete artifact reviewed is
[the signed collision-bridge packet](../exports/SIGNED_COLLISION_BRIDGE_UNIFORM_EQUILIBRIUM.md),
SHA-256 `057fc7863bffd309e081001e4cbbcbab3fd2a1f4a661c1c2561c60c285bb14f4`.
It was promoted unchanged to the export path above.
The retained checker is
`math/experiments/SIGNED_COLLISION_BRIDGE_EXACT_CHECK.py`, SHA-256
`3620d57cce45480a4980209cf95a6c8ba2e71ccb4b335312b43f1cb3d3742288`.
I did not author the producer, its algebraic certificate, or its finite
consumer. This review covers their assembled proof, including the final
seven-coalition calibration and weight obstructions.

## Exact claim and produced inputs

There are 32 fixed native entries, including the four own-singleton zeros,
and 28 variable native coordinates: nine nonpositive and nineteen arbitrary.
The arbitrary coordinates comprise K=Z3(03) and eighteen unqueried entries.
All four original own levels are arbitrary. These conditions are disjoint
and specify a nonempty raw family independently of any strategic witness.

For every table in the family and every 0<delta<a, the proof constructs a
finite periodic profile whose prescribed terminal payoff is the SAME vector
W=(kappa0,kappa1+A1,kappa2+A2,kappa3). Its full terminal regret vector is
(0,0,0,max(K,0)delta). The downstream argument proves the uniform-payoff
claim at that fixed W. Every algebraic parameter, root, continuation value,
finite block, and period is produced. No strategic input remains assumed.

The eighteen unqueried entries genuinely lie outside every prescribed
coalition and every unilateral join available on the chosen supports.
All opponents-only laws absorb almost surely, so arbitrary row translations
add kappa_i to all compared terminal payoffs without translating AllNever.
For each table the original rewards are bounded; the proof does not require
a common bound over the unbounded family.

## Independent verification and falsification of the proof

I reconstructed the active root payoffs directly from the sixteen raw
coalition probabilities using a separate exact SymPy calculation. It verifies
the triple123, pair12, solo2 and solo0 active identities. It also independently
verifies, as full rational-function identities rather than only modulo P,

    A1(1-h)-3h=9P(w)/(4D(w)),
    A2(1-h)-V2-h=P(w)/D(w).

The quintic is strictly increasing on the positive axis and has opposite
exact signs at the printed rational endpoints. Its specified root therefore
exists uniquely. The denominator signs and all strict guard bounds hold on
that interval. I checked the printed numerical enclosures against exact
rational interval bounds; they are valid enclosures, not root approximations
used as proof. The retained Fraction-only checker passes and its interval
and quotient-ring operations were inspected. Its modular divisions check
invertibility and do not assume irreducibility of the quintic.

The finite consumer survives these specific attempts to break it:

- The negative player1 value is actually crossed. The 43 regular wash roots
  preserve s>=v and t>=3v/100, and the last root is legal because
  (97/100)^43<109/400<(3E2+x)/(4x). The resulting survival is exactly
  1-x/3 and the endpoint is exactly V. There is no continuation after an
  infinite block.
- The final solo3 aggregate admits a finite subdivision with q<=V2/3.
  Its endpoint is exactly A by both closure identities.
- After the first solo0 seam, the geometric growth rule reaches a in finitely
  many steps and bounds Kq by the existing player3 coordinate. It works for
  every finite real K. The other variable joining rewards only improve
  inequalities. Every hazard remains strictly below one.
- Prescribed values are not confused with full response caps. At every root,
  including the seam, Continue against the prescribed next value equals the
  current value. The actual cap therefore satisfies the max recursion for
  D=B-v. Opponents-only survival contracts over a period. The sole positive
  local argument is max(K,0)delta at the first seam; repeated periods do not
  add that error. The exact initial cap excess is the vector claimed.
- Arbitrary behavioral replacements reduce to laws of the first quitting
  date, including Never. The argument does not restrict deviations to a
  finite menu, a stationary law, or the displayed controller.
- The absorption-time bound is uniform over unilateral deviations because
  each deviator faces a fixed positive opponents-only quit probability per
  period. It gives the stated finite-horizon error at the same W for all
  sufficiently large horizons. Negative own levels do not invalidate this
  comparison because opponents-only absorption is proper.

The equality Z2(12)=0 is genuinely structural in this construction; changing
all displayed coordinates freely is not proved. The packet correctly retains
that limitation and does not call this independent variation of all60 rewards.

## Implementation and accepted-class overlap audit

The old table with Z3(123)=-5 was already covered by ordered nonpositive
anchor blocks, including a selection with blocks ({0},{1,2,3}) and weights
1 then (1,1,3). It would not pass this gate. This verdict applies only to the
repaired +1 table and the final hash above.

The repaired class passes the substantive increment test for the following
reasons, checking existential selections rather than just one witness.

1. **Ordered anchors:** the fixed positive singleton graph is strongly
   connected, so the passive singleton inequalities force every nonempty
   marked set to be all four players. The first block meeting 123 then has
   a positive weighted participant sum because its participant vector is
   (11,2,1). This excludes every marked set, ordered partition, and positive
   block weight throughout the entire raw family.
2. **Premium traps:** 123 is a trap whose all-positive participant vector
   defeats every nonzero nonnegative upper-average weight. The joining
   charge from 12 to 123 is 7>0, defeating the required negative face-charge
   test with a strict margin. The singleton charge at {1} also equals zero.
   Thus this is not merely an excluded boundary point of a strict-charge
   class recoverable by an arbitrarily small perturbation.
3. **Raw passive inverse children:** all four possible triples are checked.
   Only 023 has an entrywise nonnegative inverse, and its outside inverse row
   is (-3,6,2)/5. The other triples have negative inverse entries. Changing
   labels within a chosen triple cannot repair these signs.
4. **Other singleton-selected producers:** there is exactly one mutually
   negative pair, 13, whose joint participant reward Z1(13)=-100 defeats
   the attached-pair premise. The no-negative-pair and two-negative-pair
   classes fail their respective tests. Principal13 also blocks the
   all-principal projective Q-bar condition. The fixed singleton signs do
   not fit the reciprocal-opposition four-cycle families under any player
   permutation. The favorite/matching families require unavailable row
   and pair sign patterns.
5. **Fixed-matrix premium/passive families:** negative participant entries
   Z1(12)=-100 and Z3(23)=-100 and the nonadditive passive entry Z0(12)=-12
   exclude the relevant positive-premium/additive-passive classes. The fixed
   singleton matrix has distinct row sign/magnitude patterns, so this is
   not repaired by an unexamined nontrivial matrix-preserving relabeling.
6. **Global and support-filtered weights:** the fully printed completion
   satisfies 10r(12)+10r(012)+r(23)=(-235,-910,-66,-29). No nonzero
   nonnegative payoff weight can make all proper-coalition rewards
   nonnegative. For the native support-filtered inequalities, J_w(123)=3w0
   first forces w0=0; H_w({1})>=0 forces w2=w3=0; H_w({3})>=0 then
   forces w1=0. This rejects every weight, including each member of any
   finite family subject to those same necessary tests.
7. **Stationary and sure-root selection:** I ran and inspected the separate
   exact rational exclusion for the complete printed reference completion.
   All80 nonzero stationary support patterns and all65 sure-root patterns
   are excluded, using978 and369 interval nodes respectively. This includes
   the induced Nash rows usable by the compared punishment-tail consumers;
   failure of stationary repetition alone was not used to infer that fact.

The first three obstructions depend only on the fixed entries and hold for
the whole family. The completion-specific comparisons show that the new
class is not contained in the other compared raw families. Some allowed
completions could also be covered by other methods; the theorem does not
need or claim pairwise disjointness from every old existence class. Neither
this audit nor the packet claims an exhaustive census of all conceivable
supplied-certificate interfaces. Such an interface may verify the newly
produced profile without already producing it from this raw table.

## Source correspondence, gate, and reproduction

The source audit used `quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean`,
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`, and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The child comparison matches
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The packet supplies its own fixed-target finite-horizon proof, so it does
not assume a payoff-selection conclusion beyond these interfaces.

The packet is self-contained: its mathematical proof and complete boundary
table do not depend on conference notes or temporary programs. All strategic
inputs are produced, the original information and deviation model is
preserved, and the formalization handoff lists the concrete statements to
prove without assuming a return witness. The repaired class narrows the
surviving raw-game cases beyond the compared implemented and accepted
producers. It therefore meets the existence-class export gate.

The retained exact algebra check is reproduced with
`python math/experiments/SIGNED_COLLISION_BRIDGE_EXACT_CHECK.py`.
I also used a separately written scratch raw-coalition algebra check; the
proof record does not depend on retaining that duplicate program. No Lean
files were changed, no Lean build was run, and no L/A/C seal is asserted.
