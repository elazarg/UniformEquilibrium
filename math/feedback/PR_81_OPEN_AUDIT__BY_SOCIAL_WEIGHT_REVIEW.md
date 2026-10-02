# Open PR #81 mathematical-content audit

Reviewer: SOCIAL_WEIGHT_REVIEW

PR: #81, “Compile rational strict inert inputs to exact Fin4 counterexample
certificates”

Head inspected: 834edf4343da35c24ab12f4da1e8c6f0c136c2d0

Current main inspected: 831e82aec87cf7b92e7767c8e3d3626abb27f626

## Recommendation

**CLOSE AS A FRONTIER PR; SALVAGE TWO GENERIC SEARCH UTILITIES SEPARATELY IF
THEY ARE STILL WANTED.**

The strict-inert headline does not consume or contradict strict inertia. Its
global input is already a FinFourMinimumAtomProducer whose hard residual
contains a positive unrestricted terminal exploitability witness. The output
certificate therefore certifies a counterexample that the input has already
assumed. In the arbitrary-real-table arm, it may even certify a different
rational table. Bundling the unused strict object beside that certificate
does not create a new mathematical implication.

The PR nevertheless contains two useful generic exact-search additions that
are absent from current main:

1. soundness from the proof-free Boolean lower-tree verifier without replaying
   the generator origin; and
2. a direct fixed-table dovetail over dyadic scales and local resolver stages,
   avoiding the global reward-table enumeration.

Those are exact-search trust/usability improvements, not a strict-inert
consumer. They should be extracted into a small rebased PR if operationally
valuable.

## Exact mathematical content

### Independent lower-tree verification

Research/Quitting/FinFourIndependentCertificateSoundness.lean attempts to
prove:

- an accepted lower tree directly lower-bounds the analytic single-shell
  quantity;
- the lower bound transfers to the unrestricted behavioral exploitability
  infimum;
- a positive accepted scale gives a terminal exploitability gap; and
- the gap rules out a uniform-equilibrium payoff.

This is mathematically sound in outline. The checker is proof-free finite
data, and the proposed proof terminates trust at the checked Boolean
verification theorem rather than at a generator-origin equation.

### Fixed-table semidecision

Research/Quitting/FinFourFixedTableCounterexampleSearch.lean fixes one
normalized rational reward code and dovetails only:

- the positive dyadic scale index; and
- the exact local resolver stage.

If the table has positive unrestricted exploitability infimum, a sufficiently
small scale cannot return the upper arm, so some finite stage returns a lower
tree. Conversely, every emitted tree is independently checked and gives a
positive terminal gap. This is a valid semidecision for one supplied
normalized rational table. Nontermination has no meaning, and it is not a
decision procedure.

Current main already has the global semidecision and its mathematical
soundness/completeness in
Research/Quitting/FinFourCounterexampleSemidecision.lean. The direct
fixed-table stage function and verifier-only trust boundary are the PR's
genuinely distinct content.

### Strict-inert wrappers

Research/Quitting/FinFourProducerAtlas/StrictInertExactCounterexampleSearch.lean
has two logically different wrappers.

1. The arbitrary-real-table wrapper invokes the already checked theorem
   exists_finFourCounterexampleStep_of_real_infimum_pos. Its output rational
   table need not equal the strict source table. The strict packet is merely
   stored beside an independently known search output.
2. The normalized-rational fixed-table wrapper does preserve the table, but
   positivity of the exploitability infimum comes from the minimum source's
   retained terminal-gap witness, not from strict inertia.

In both wrappers the strict field is unused in the proof of certificate
existence. The zero-minimum and uniform-payoff “regressions” are immediate
restatements of the source structure's positive minimum and no-uniform-payoff
witness. They do not rule out a previously viable strict-inert branch.

Therefore this layer is a source-attached certificate compiler, not a
consumer, producer from local strict-inert data, or counterexample
construction.

## Current-main overlap

Current main contains:

- FinFourCounterexampleSemidecision, including global emitted-certificate
  soundness, positive terminal gaps, no-uniform-payoff consequences, finite
  discovery of every enumerated rational positive-infimum code, and
  existence of an emitted rational counterexample from a real positive
  infimum;
- all minimum-source and strict-inert input structures used by the wrapper.

Current main does not contain declarations named
FinFourFixedTableCounterexampleCertificate or
FinFourExactScaleCertificate.lower_verifies_infimum_sound, and a narrow
symbol search found no exact equivalents of those two generic utilities.

Thus the useful delta is search API/trust separation, not conjecture-facing
mathematics.

## Check status and defects

The head's Focused Lean and CI checks failed. The exact source-artifact check
passed.

The focused log identifies two local errors in
FinFourIndependentCertificateSoundness.lean:

1. verifies_components asks for right-associated conjunctions, while Boolean
   simplification produces a differently associated conjunction;
2. verifies_no_uniformEquilibriumPayoff lets Lean infer positivity of
   epsilon rather than epsilon/8 before supplying the epsilon/8 gap theorem.

Both are small elaboration/surface repairs: reassociate the conjunction
explicitly and state the positive gap expression explicitly. They do not
falsify the mathematical claims. Nevertheless, the PR has no successful Lean
gate at its current head.

## Unresolved gap

No theorem in the PR derives a positive global exploitability gap from:

- the strict inert inequalities;
- the normalized toll;
- a local reward-table screen; or
- a source-free strict-inert packet.

That is the only direction in which this work could have consumed the strict
inert chamber. The PR deliberately relies instead on a source object that
already contains the global terminal witness.

## Close/keep conclusion

Close #81 in its current form. If independent checker soundness and the
fixed-table command are desired, rebase and extract only those modules,
repair the two elaboration errors, and describe the result as an exact-search
interface improvement. Do not retain the strict-inert wrapper as evidence of
Fin4 frontier contraction.

