# Independent review: unequal-high three-state Nash–Bellman closure

Reviewer: CODEX_RADO_BOUNDARY. Date: 2026-09-08.

Frozen mathematical note:
`notes/CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_THREE_STATE_NASH_BELLMAN_CLOSURE.md`
SHA `1ae929df8073aa37ca383c7bdcb8dec4c29809fa61627444af7f2842f83657af`.

Frozen executable certificate:
`experiments/CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_THREE_STATE_CERTIFICATE.py`
SHA `3579aaf338c399781297c54cb8967606361a7d398bfae14a42129c8557222fe0`.

Mathematical verdict: PASS as exact ordinary mathematics, with no requested
repair. The raw table produces an exact absorbing period-three equilibrium
against all behavioral deviations and one fixed payoff for each start phase.
The finite-censor formulas also pass. This is not a Lean-checked instantiation.

Separate importance/admission verdict: KEEP INTERNAL. This genuinely removes
the outstanding literal candidate, but the present result does not justify
a standalone export under the tightened importance gate. Section 7 explains
that decision; it is not a correctness objection or strategic-input failure.
No other review was read before forming either verdict.

## 1. Exact scope checked

The table is the specified fifteen-row unequal-high paired table, with own
singletons one, within-partner singleton receipts four, other singleton
receipts zero, within-pair member rewards two, high directed cross rewards
(8/5,8/5,2,2), and all listed passive/triple/grand entries unchanged. The
grand row is (−1,−1,−1,−1), and live/Never payoffs are zero. Its normalization
by four has the previously checked canonical table hash
`5cda685b991381e2f2f56631bf78f138d497f43ce095cd793c8d060f92e88318`.

The nine actual hazards occur in chronological active sets

    023 | 012 | 013,

in the exact variable order displayed in the packet. Each active hazard is
in (1/100,1/4); the other three phase/owner hazards are exactly zero. Root
actions and all subsequent private draws are independent. The statement
allows every unilateral behavioral replacement, not merely periodic or
finite-memory deviations. No stationary nonexistence, global root count,
root maximality, or seed-to-cycle connection is needed or claimed.

The exact zero in the declared rational box is selected once from this raw
table, before accuracy or horizon. The three actual phase vectors each lie
in (1,3/2)^4 and each is a fixed original-game UE payoff. The finite-law
assertion from phase zero holds for every integer cutoff T≥2.

## 2. Exact arithmetic and rate existence

I read all 309 lines of the note and all 168 lines of its certificate, checked
their hashes, and ran the stated command with bytecode writing disabled.
Every rational assertion passed. The output included

    ‖J(x0)⁻¹F(x0)‖∞ < 1/10⁹,
    sup_X ‖Id−J(x0)⁻¹DF‖∞ < 1/100,
    Newton-image displacement < ρ/50,   ρ=1/10⁶,
    7/10<D<4/5,
    F01,F13,F22<−1/6,
    every deleted one-stage survival <5/6,
    every actual phase value in (1,3/2).

The imported arithmetic helper was inspected at its actual used definitions
`Ival` and `fraction_matrix_inverse` in
`Experiments/certsearch/krawczyk_cycle_certifier.py`, SHA
`1dcd5a4e9305254334d5bab0cd2b01e80fd5ee42a0eff16a4ba520b5f9633459`.
Interval addition/subtraction/multiplication are outward exact rational
operations; division rejects zero-straddling intervals. The inverse routine
uses exact Gaussian elimination and explicitly checks B·J(x0)=Id. The
imported experiment's main is not executed. The four-player evaluator is
the packet's own sixteen-coalition evaluator, not the helper's three-player
specialization. Float conversions are confined to printed locators.

The forward-derivative implementation uses the correct product rule and
initial coordinate derivatives. Its interval matrices enclose DF on all of
X. Maximum row sums of interval absolute bounds control the ℓ∞ operator
norm. For T(x)=x−BF(x), the derivative bound and center correction therefore
give T(X)⊂x0+[−ρ/50,ρ/50]^9⊂X. The closed cube is complete, T is a strict
contraction there, and its unique fixed point has F=0 since B is invertible.
This is a genuine root producer, not a supplied-zero or numerical-convergence
assumption. Uniqueness is asserted only in X.

## 3. Independent falsification checks of the literal polynomials

The owned reproducer
[UNEQUAL_HIGH_THREE_STATE_AUDIT.py](../experiments/CODEX_RADO_BOUNDARY__UNEQUAL_HIGH_THREE_STATE_AUDIT.py),
SHA `b73f901b184c94e67014956475770f53713ebf2ebdb52e8b2621f04ad528b6d8`,
independently reconstructs the root rewards by enumerating Boolean actions.
It computes Quit/Continue endpoints by forcing the queried root coordinate
to one/zero and composes the three one-stage affine laws in reverse
chronology to recover each cyclic numerator. These checks passed:

- All twelve cleared endpoint polynomials and twelve value numerators at
  six exact rational profiles, including all-zero, all-one, and mixed
  boundary profiles, match the packet evaluator. The denominator matches.
- All 81 center-Jacobian entries agree with exact central differences.
  This is an exact derivative check, not a finite-difference approximation:
  every cleared polynomial has degree at most two in each individual
  variable, since D,W,Q,H,d are separately multiaffine.
- All 36 comparisons obtained by separately changing each of the three
  quiet owners' grand-coalition coordinates agree with the literal law.
  The only affected cleared endpoint is that owner's quiet endpoint, with
  coefficient D times the product of its three opponents' active hazards.
  The grand-coalition terms are therefore present with the correct sign.
- At cutoffs T=2,3,5,8, the existing exact full finite-law evaluator verifies
  all sixteen prescribed-payoff censor identities. Its caps include all
  finite dates, after-support Quit, and Never. At the rational center the
  caps differ from the nominal phase values by less than 10^−10.

The last center check is deliberately NOT called exact Nash: the rational
center is not the certified zero. Root existence comes from Section 2, and
the exact finite-cap equalities follow from the symbolic argument next.
The regression supplies independent transcription/index/derivative tests,
not a replacement for the full interval proof.

## 4. Every endpoint and unrestricted complete response

The packet's G and c are actual current absorption reward and joint Continue
probability. The cyclic numerator W and D=1−c0c1c2 therefore give the actual
terminal payoff V=W/D. The deleted formulas are literal Q (Quit now), H
(nonempty opponents absorb while the owner Continues), and d (all opponents
Continue). Thus F/D=Q−H−dV_next, with the correct next phase.

At each active interior hazard, F=0 and the actual Bellman mixture yield
V=Q=H+dV_next. At each quiet owner its hazard is zero, so V=H+dV_next and
F<0 gives Q<V. These are all twelve phase/owner comparisons, not only
the nine equalities solved by contraction. No grand or triple response is
discarded because it is absent on path.

Iterating the Continue equality and then using Q≤V bounds every finite
deadline, including arbitrarily many cycles. The uniform d<5/6 bounds
the unabsorbed remainder by a constant times (5/6)^n. For Never the remainder
vanishes, proving that Never itself attains V. It is correctly NOT assigned
payoff zero: the opponents absorb almost surely. Averaging over the complete
planned stopping law bounds any randomized history-dependent behavioral
deviation. Hence all full caps equal V and original terminal regret is zero.

## 5. Finite censorship and fixed original payoff

Censoring each private clock after T dates independently produces a genuine
finite product law with exact remaining Never atoms. For prescribed play,
conditioning on joint survival through T proves

    U_i^T=V0_i−C_T V_(T mod3),i.

For a response before T, prescribed opponents have exactly their old law up
to the response date. For any response at/after T, the all-opponents-survive
event gives singleton payoff one for finite Quit and zero for Never. Both
are bounded by the actual future phase value, which is strictly above one.
The Continue recursion through the head therefore caps all such responses
by V0_i. This step uses DELETED survival, not joint C_T.

The reverse cap inequality is also valid: players 0,2,3 can Quit at date
zero, and player 1 can Continue once and Quit at date one. Active endpoint
equality and the phase-zero Continue identity make these payoffs exactly
V0_i. All those dates lie below T precisely because T≥2. Thus B_i^T=V0_i,
and full regret equals C_T V_(T mod3),i. Rowwise joint survival is at most
deleted survival, giving the claimed bound (3/2)(5/6)^T. Delivery tends to
the SAME V0, not a target reselected for each cutoff.

For the infinite profile, every unilateral terminal time is bounded above
by the opponents' first stopping time, which has a geometric tail uniformly
over the deviator. Bounded rewards then give uniform convergence of finite
average payoffs to terminal payoffs. The same exact periodic profile works
at every accuracy, from any chosen initial phase.

Actual consumer declarations inspected:
`quittingRootSuccessorPayoff_eq_endpointMix` and the endpoint-Nash facts in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`;
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate` in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`; and
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The actual hypotheses are policy recursion, root Nash, and deleted-cycle
contraction; the packet produces each one. No phantom all-Continue root,
generic predecessor seriality, or unproved source-path connection is used.

## 6. Strategic inputs and source completeness

For this fixed literal table there is no unproduced strategic input. The
root, continuation values, complete caps, and fixed UE payoffs are all
derived from the exact table and finite rational certificate. The seed and
all-root-face numerical search are discovery provenance only. Their lack
of exhaustive root counts or a certified path into the cycle is harmless
because the actual cycle is jointly reselected and certified outright.

No author or export file was changed. The two frozen hashes were rechecked
after reproduction. No Lean file, build, commit, or other review was used.

## 7. Independent importance/admission decision

This is a correct and useful removal of the actual table from negative
candidacy. It crosses the limitations of the previously tested matching
grammars on this table and supplies an all-behavior zero-error output where
only a small-positive four-phase upper profile had been produced. It merits
reviewed internal retention; the independent check was worthwhile.

It is not, however, a new general periodic mechanism. SPINOZA's reviewed E1
work already uses overlapping period-three supports, prescribed triples,
cleared Nash–Bellman polynomials, and rational interval root certification.
The precise E1 affine/invisible-coordinate class and the common-c, oriented-h,
rectangle, and named stationary sources do not cover this literal table, as
checked in the separate
[source-coverage precheck](CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_PERIOD_THREE_SOURCE_COVERAGE_PRECHECK__BY_CODEX_RADO_BOUNDARY.md).
Noncoverage establishes a new solved input, not export importance by itself.

The packet supplies neither a raw selector for the full twelve-member box,
a proved strategy-class completeness theorem, nor a structural alternative
that narrows an arbitrary-game producer obligation. It also does not answer
the named escape-aware question's positive-gap or total-decision branches.
On the evidence supplied, I do not affirm the independent importance needed
for a standalone export of this one-table instantiation. No parameter-radius
optimization, cosmetic class wrapper, or additional generalization is being
requested merely to pursue admission. KEEP INTERNAL is a value judgment,
not a missing-proof or conditional-construction objection.
