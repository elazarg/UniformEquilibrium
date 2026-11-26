# Independent review of mixed-pivot global context rigidity

**Mathematical PASS; export admission WITHDRAWN.** The
[internal theorem](../revisit/ACTUAL_MINIMUM_GLOBAL_PAIR_STAR_RIGIDITY.md)
is still valid at SHA256
`fd25918270847c38eae4cb76a9c085a8212643a09fa60ad48cac580673c3842c`.
Its complete boundary table is now solved by the
[signed solo/triple producer](../exports/SIGNED_SOLO_TRIPLE_UNIFORM_EQUILIBRIUM.md).
The general conditional theorem is not proved redundant, but this solved
control no longer certifies its additional counterexample coverage. Retain
the proof internally. The final review below includes the explicit admission
withdrawal; the [source audit](SIGNED_SOLO_TRIPLE_UNIFORM_EQUILIBRIUM__SOURCE_AUDIT.md)
records the new construction and the named prior producer comparisons.

# Final independent review of signed-pivot global context rigidity

Reviewer: FINAL_GLOBAL_REVIEW, 2026-11-09.

## Verdict and exact bytes

**CURRENT VERDICT: mathematical PASS retained; conditional export admission
WITHDRAWN.** A subsequently proved exact two-phase absorbing equilibrium
covers the completed witness table. The final reassessment below supersedes
the admission affirmation recorded in the original review. I find no
unresolved mathematical objection to the complete rigidity candidate itself. This is an ordinary mathematical review,
not a Lean build, an arbitrary-game producer, or a claim that Fin4 is solved.

The complete 1037-line candidate is
`math/revisit/ACTUAL_MINIMUM_GLOBAL_PAIR_STAR_RIGIDITY.md`,
SHA256 `fd25918270847c38eae4cb76a9c085a8212643a09fa60ad48cac580673c3842c`.
The independent completion checker reviewed and executed is
`math/experiments/FIN4_SIGNED_PIVOT_COMPLETION_CHECK.py`, SHA256
`0b4c126ec0ec9001a5c6a82a2cdf8863984d0972174c4bb65df6ba0727c45f10`.
The accompanying source audit is now superseded by the
[signed solo/triple audit](SIGNED_SOLO_TRIPLE_UNIFORM_EQUILIBRIUM__SOURCE_AUDIT.md),
which incorporates the exact new equilibrium and the prior producer screens.
The admission reassessment below records the effect on this theorem.

I read `AGENTS.md`, `math/AGENTS.md`, `math/GOAL.md`, `math/SOURCES.md`, and
`math/exports/README.md`. No tracked file, Lean file, Git index, branch, or
worktree was changed by this review.

## The theorem actually reviewed

The input is an actual independent complete-law profile with every original
Never mass positive, all four full behavioral caps attained by Never, zero
observer debts, and global minimality of the fixed objective d_p+r nu on a
carrier containing every actual observer-optimal profile. Its eventual
nonempty dates have exactly the pivot and one observer active. All three
observer labels recur; every inactive-observer and pivot Quit comparison is
strict at every sufficiently late nonempty date. The raw Ratio hypotheses
are Gamma invertible, G_i nonzero, rho_i>1, and all c_ij>0 for distinct
observers. The pivot row h and pivot participant rewards may have either
sign. Earlier pivot contacts are allowed.

At any fixed r with all three C_i(r) nonzero, such a minimum must eventually
follow one directed three-cycle, and that cycle's explicit price matrix must
be symmetric. For the stated open dense raw test, both orientations fail
symmetry throughout a sufficiently small positive r interval chosen before
source selection, so the entire specified mode is impossible there.

The conclusion is about actual minimizing sources. It is not a theorem that
all tables in Ratio have UE, that all actual laws have this calendar, or that
an actual-law fixture is a minimizing source.

## Review of the global mathematical mechanism

1. **Complete semantics and finite splices.** The unique live history makes a
   behavioral deviation a mixture of deadlines and Never, with no public
   correlation. The root payoff, cap, Never-value, and survival recursions are
   literal. Positive original Never makes every head survival positive,
   gives summable hazards, and passes ALL-END and observer optimality to
   conditional tails. It does not make those tails minima or their caps
   nonnegative. The proof does not use either false implication. Empty-date
   deletion preserves the attained cap because Never is retained.

2. **Exact run chart.** I checked the geometric pivot atoms, first-coalition
   probabilities, and cap equations directly. The reduced four-equation
   endpoint constraint correctly uses the penultimate last-label cap in
   place of a tiny final active derivative. Its kernel calculation is valid
   for both ijki and ijkj. The positive lower bound on the relevant c-term
   persists when theta approaches zero. For each actual finite run theta is
   strictly positive, so the reduced constraint recovers the omitted exact
   final cap. No infinite run is executed.

3. **Uniformity across unbounded waiting.** The projective change of variables
   gives an exactly linear map when the observer run mass g is zero. Its
   arbitrary subproducts are bounded by the convex-combination/telescoping
   coefficients, not by an unjustified product of one-step norm bounds. The
   nonlinear remainder has the factor g, including its state derivatives.
   The Duhamel and chain-rule bounds therefore use the summable observer
   masses, not a potentially nonsummable sum of cap sizes. This yields the
   needed uniform C2 convergence over arbitrary finite bridges. The fixed
   neighborhood can be chosen smaller than the common analytic chart so
   all bridge prefixes remain inside it.

4. **Timing variation.** For a run of length at least two, moving weight
   between its first and last observer atoms is a two-sided variation. The
   exact factor (E_i/G_i)g is positive even when E_i and G_i are negative.
   The bridge and endpoint correction preserve this factor; division by it
   does not require it to dominate a squared tail scale. The resulting
   derivative is -C_i(r)+o(1), with the penalty already fixed. Thus all late
   runs are singleton whenever every C_i(r) is nonzero.

5. **Constrained second variation.** The quadratic identity is formulated in
   global absolute atoms, where closed total marginal tangents make the
   quadratic joint-Never term vanish. The weighted Never-payoff correction
   restores the penalty contribution on the cap-constrained curve. The
   augmented objective has zero ambient differential at zero data, so its
   Hessian does not acquire an omitted term from second-order cap-solving
   controls or from the atom/hazard coordinate change. I checked the signs
   of the ordered-pair terms and the coefficient identity involving K.

6. **Sparse global control and context rigidity.** The memory remainder is
   O(epsilon) uniformly, including arbitrarily many zero-control dates.
   Compact accumulation contexts can be requested in any finite order,
   since each selected neighborhood occurs infinitely often. This does not
   assume bounded recurrence gaps. A closed observer-coordinate path leaves
   only an O(epsilon) pivot residual; the later four-run correction has
   O(epsilon) controls and O(epsilon^2) cost. Different contexts for one label
   yield opposite-work out-and-back excursions; the setup and reverse setup
   cancel with the same assigned contexts. Invertibility of c guarantees a
   nonzero price-row difference. Rectangles then force price symmetry.

7. **Exact eventual calendar.** Unique accumulation context for each label
   implies the transition equation on every infinitely repeated edge. The
   recurrent three-vertex graph is strongly connected. The branching
   contradiction is valid for unequal as well as equal lambda values.
   Consequently every vertex has one successor and the recurrent graph is a
   directed three-cycle. There are finitely many other edges, each used only
   finitely often, so the actual word is eventually that cycle. The proof
   gives eventual exact periodicity, rather than only a periodic limit.

8. **Transfer to an actual minimum.** Fixing the polygon, mesh, context
   tolerance, and strictly negative work margin before moving the cut late
   is essential and is done here. Only waiting distances then vary. The six
   implicit endpoint equations have a uniformly invertible cap block and
   scalar payoff/survival blocks tending to identity. Bridge C2 bounds give
   convergence of their two-jets. Every chosen window is finite, so its
   positive atoms and strict comparisons provide some two-sided feasible
   interval; a uniform interval radius is unnecessary. Fixing every entrance
   cap preserves the entire earlier head, including pivot ties. The whole
   objective variation is multiplied by positive head joint survival. A
   negative second derivative contradicts minimality on that finite curve.

I specifically attempted to break steps 3, 6, and 8 with arbitrarily long
waiting, very small selected masses, and earlier pivot contacts. The proof
uses uniform derivative bounds but only pointwise feasibility radii, which
is sufficient. I found no illicit exchange of an infinite calendar with a
finite comparison or a requirement that tail minima be inherited.

## Generic perturbation and exact fixture

The genericity polynomial uses the three A numerators and squared skew
numerators for both orientations. Its denominators do not vanish on Ratio.
The displayed mixed-pivot example makes every factor nonzero. Therefore the
polynomial is nonzero on the ambient raw coordinate space and its complement
is dense in every open Ratio region. Taking the product over four pivot
relabelings is legitimate: a product of nonzero real polynomials is nonzero.
The new table is chosen first; then the common sufficiently small penalty
interval; then the source. No minimizing law is transported through a reward
perturbation. The absorbing-gap Lipschitz estimate is valid for full
behavioral caps. The signed-to-native translation preserves debts on
absorbing prescribed profiles only; native AllNever remains exact Nash.

I reran the full embedded SymPy program. It reconstructs the first-outcome
identity, the two nonzero orientation skews, all singleton-source matrix
checks, and the actual three-date polynomial contact equations. It verifies
the seven-equation Jacobian -60372/7 and all displayed strict leading gaps.
The actual-law iteration follows from eta(t) in (1/3,2/3), summable hazards,
matching boundary vectors, and vanishing continuation remainder. It works
with arbitrary fixed finite values of the other 32 native rewards at a
sufficiently small scale.

For the SAME complete 15-row table the verified coefficients are
C1=(51r-4)/6, C2=-(287r+78)/45, C3=-(133r+9)/13, so all are negative on
0<=r<4/51. The pure123 actual fixture has no repeated runs; it therefore
avoids the timing-only obstruction. Its pivot Never product gives
r(t)=(30/7)t+O(t^2), so it can meet the old saturation equality at every
sufficiently small penalty fixed in advance. The current theorem adds a
restriction on that equality boundary. The fixture itself supplies neither
minimality nor a positive absorbing gap.

As a separate falsification attempt, I generated 20 fresh rational Ratio
tables with asymmetric positive c entries, varying signs of G and h,
arbitrary pivot participant rewards, and arbitrary passive pair rewards.
For each I built closed tangents on a nine-date noncyclic word and checked
the full fixed-r quadratic identity directly from independent first-outcome
expansions. All passed. I also checked 640 reduced four-run Jacobians at all
compact endpoint choices theta=0 or lambda; all were nonsingular. These are supporting falsification checks; the general proofs above do not
follow merely from the finite samples.

## Source overlap and conditional admission

The old positive-h chamber was degree-zero and already excluded. The new
literal matrix has determinant 6, strictly positive inverse, R0, and degree
one. Its inverse-positive triples have strictly negative passive inverse
rows; the signed-cycle prerequisite fails under all 24 roles. I inspected
the precise relevant singleton declarations, including
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`,
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`,
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`,
and `SignedFourCycleSingletonData`, in their files named by the packet.
The positive determinant is essential: positive inverse alone is not the
implemented UE criterion.

The completion program independently terminates with all 80 stationary
patterns excluded (2071 exact Bernstein nodes), all 65 sure-coordinate
patterns excluded (294 nodes), and all 14 proper universal child quiet-lift
selectors excluded by actual exact child profiles. I checked the necessary
sign reductions: the sure-owner test uses the actual punishment lower bound
L=(-10,-3,-3,-3), and nonsure owners facing a sure owner have H_i=0. Thus
this comparison is not merely against stationary or Never punishment tails.
The origin bound for stationary supports and the integer Bernstein splits
are valid and leave no unresolved boxes.

The same checker passes whole-weight dual obstructions, all 14 nondiscrete
response partitions even with positive constant row scaling, all 15 marked
invariance countercontrols within playerwise reward boxes, and the complete
weak/closure role checks described by the source audit. I compared the
critical return sign lists and the two surviving weak three-owner roles with
the actual raw hypotheses in the scalar, two-pair reset, core-free,
negative-value, and general three-owner return sources. The latter two roles
fail respectively the physical rate x=-2 and the strict-negative pair of
coefficients C=-14/1475, a0=-8759/2950 in required U0=C+lambda*a0>0.
The zero J03 boundary is consequently handled by full source conditions,
not a failed strict-sign screen alone. I also checked the all-coalition cap
hypothesis of the calendar-polytope packet and the two nonpositive participant
rows in the stated actual-marked-source neighborhood. The raw obstructions
to those families are independent of virtual marked controls.

The virtual marked controls are not claimed actual strategic continuations,
and universal child-lift failure is not failure of a selector choosing one
favorable child equilibrium. The audit does not prove absence of every
conceivable equilibrium architecture. I affirm the named full-selection
comparisons and their stated scope, not a universal-library negative claim.

I also compared the accepted Never-mass saturation theorem and the retained
general-Ratio saturation corollary. They impose an endogenous equality and,
in their relevant formulations, exclude earlier pivot contacts. They do not
supply this all-calendar context rigidity or exclude the equality-boundary
actual geometry just constructed.

**Why the exceptional conditional gate passes:** the remaining actual-source
obligation admits arbitrary recurrent pair-star calendars, including the
endogenous equality boundary. The new theorem derives an eventual exact
three-cycle and explicit conservative-price equalities from minimality,
using finite feasible comparisons it constructs. It then excludes this
entire specified mode generically, on raw data that escape the audited
existing producers. This is a substantive global restriction on the
possible minimizing-source geometry, not a supplied improving-direction
verifier, a finite-word census, or a restatement of an open repair oracle.
The same completed table demonstrates actual guarded recurrent geometry
and nonredundancy of the named raw-source tests; it is deliberately not
promoted into an unrestricted counterexample.

The strategic inputs not produced are explicit:

- actual attainment of the observer-constrained global minimum, rather than
  only a point of a compact semantic closure;
- positive original Never masses and ALL-END for that actual minimizer;
- selection of a pivot and raw table in Ratio;
- eventual exact pair-star support with all three observer labels recurrent;
- strict late inactive-observer comparisons AND strict late pivot comparisons.

The general source theory has conditional alternatives providing some of
these properties; it does not jointly supply this list for arbitrary games.
A positive absorbing gap is likewise not supplied for the explicit fixture.
The current export must therefore remain an **exceptional conditional
source-mode theorem**. It must not be reported as a newly solved raw UE
class, a completed source-to-UE chain, an unconditional eliminated source
branch, or arbitrary Fin4 closure. Nonrealized sources, other sign chambers,
mixed supports, quiet ties, and late pivot contacts remain outside the
claimed conclusion. Within this scope, I affirm admission.

## Semantic source inspection and handoff

I inspected the cited behavioral/stopping-law payoff and cap equalities in
`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`,
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`. I also inspected
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
and the polynomial response identity source. This was static source
inspection, not fresh Lean verification.

The packet's proposed formalization order is appropriate: exact run maps and
reduced chart, projective bridge estimates, constrained quadratic identity,
sparse context controls and finite IFT transfer, then the finite recurrent
transition graph and rational genericity tests. Its theorem shape does not
smuggle the improving comparison into a strategic structure field.

Final recommendation: promote only the exact reviewed theorem and retain the
compact completion checker and source audit durably outside the frozen
packet. Preserve all stated nonclaims in the accompanying status report.


## Superseding admission reassessment: exact equilibrium at the witness

The subsequent constructive attack supplies an exact periodic absorbing Nash
profile for the SAME completed table. Let b be the smaller root of

    175496570 b^2 - 12603641 b + 64295 = 0,

isolated in (55265/10^7, 55267/10^7), and put

    s=(-348 b^2-1080 b+35)/(2(-174 b^2+139 b+35)).

Alternate the root hazards (0,s,0,0) and (5/24,b,0,5/7). I independently
recomputed both phase payoffs and every endpoint comparison from the literal
15-row table. The four active comparison numerators reduce to zero modulo
the displayed quadratic. Each of the four inactive comparison ratios is
strictly negative by rational interval bounds on the isolating interval.
All active hazards lie strictly between zero and one. Every player faces at
least one opponent who acts with fixed positive probability per period, so
opponents absorb almost surely under every complete deviation. The bounded
continuation remainder therefore vanishes, and the exact local Nash
comparisons imply full behavioral terminal Nash. They also justify the
recipient-wise original reward shifts and the original uniform-payoff
consumer. This is an exact construction, not merely a numerical lead.

The independent reconstruction is retained as
`FINAL_GLOBAL_DYNAMIC_CHECK.py` beside this review. It ran successfully.
In particular, the passive payoff of owner1 at the second phase is
-2x+z-2xz, with Gamma13=+1; it vanishes at x=5/24, z=5/7. The previously
suggested sign obstruction using Gamma13=-1 does not apply to this table.

Consequently I withdraw the earlier exceptional-admission affirmation. The
prior named-producer exclusions can all remain true, while the newly found
producer covers this witness and an open neighborhood once its strict raw
criterion is established. The fixture no longer certifies that the global
rigidity theorem operates on otherwise surviving counterexample territory.
This discovery does NOT refute that theorem: its fixture was explicitly
nonminimal and no positive absorbing gap was claimed. Nor does the new
equilibrium prove that every signed Ratio table is already covered. It does
remove the concrete nonoverlap evidence on which this admission case relied.
Without a separate rigorous replacement for that evidence, retain the useful
global proof internally. The root should not push it as a newly admitted
export under this withdrawn review. The outstanding source-production and
geometry hypotheses listed above remain outstanding.
