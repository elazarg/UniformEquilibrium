# Independent adversarial review of the controlled-window theorem

Verdict: whole-artifact mathematical PASS, with the explicitly scoped
residual-mode/conditional export admission below. No unresolved mathematical
objection. This review covers the final assembled proof, not only an earlier
matrix calculation.

Reviewed proof:
`math/exports/FIXED_CAP_CONTROLLED_WINDOW_MINIMUM_EXCLUSION.md`
SHA256 `97f99ac14e70c8a0d92887aafdd4b0cdab6d14920c7bdec1f8a7a50b8790019e`.
Reviewed and independently rerun checker:
`math/experiments/CODEX_NO_CHILD__CONTROLLED_WINDOW_CHECK.py`
SHA256 `8cde869cb5d4dd87ac3202f8b1cffce269fec9775d552f931c99f29a3cc5f509`.

## Mathematical scope checked

The result applies to actual independent-clock ALL-END observer minima with
positive marginal Never masses. For a fixed full-support window and marked
strict-pivot dates satisfying the stated control rank, it constructs an
exact observer-feasible descent preserving every entrance full cap and all
unmodified earlier behavioral responses. It permits tied unmarked pivot
dates. The general raw certificate has arbitrary n>=2 and includes passive
pair rewards. The explicit alternative covers every real M>=14 on the stated
premium ray, with arbitrary fixed finite higher-coalition rewards. Eventual
full support on that ray forces geometric remaining-mass decay. At the
exact M14 singleton/pair data, eventual full support forces the strict-pivot
date set to have zero upper Banach density.

I checked the proof in the following order.

1. Literal root maps and behavioral splice. The explicit conditional-tail
   inheritance argument is correct: conditioning preserves independence,
   a Never-to-tail improvement is multiplied by opponent survival, and a
   prescribed-head-to-tail improvement by joint survival. Both multipliers
   are strictly positive. Observer contacts and all pivot
   inequalities recover the FULL cap by backwards induction. The unchanged
   continuation is used literally. Fixing entrance Never payoffs therefore
   fixes entrance full caps and observer prescribed values; all earlier
   pure responses retain their values. The global pivot payoff and joint
   Never changes both scale by the head's JOINT survival s, whereas the cap
   is fixed. Thus objective (5) is exactly the correct optimization target.
   No opponent-deleted survival is substituted for s.
2. Rank and nonlinear fiber. The tangent recurrence, endpoint constraints,
   control matrix and dimension |S|-n agree. The fixed nonzero minor gives
   a genuine smooth positive-dimensional local fiber. Positive hazards and
   strict marked inequalities make it locally two-sided; no uniform lower
   margin is needed. The stationarity-multiplier limit at zero is unique by
   full row rank, so the negative Lagrangian Hessian persists at any alleged
   sequence of nearby constrained minima. This proves one epsilon for each
   fixed table, r and pattern, without uniformity over growing patterns.
3. Quadratic identities. I rederived the signed unconditional-atom pair
   expansion, including both orderings and ties. Own-participant pair terms
   give (10); passive pair terms cancel from debt but enter (11) and K.
   Summation by parts gives the two energy identities with their stated
   signs and normalizations. The hazard-to-atom change contributes nothing
   because the relevant ambient first derivatives vanish. Higher participant
   rewards can enter contact Hessians, but their zero-data multipliers are
   zero, so they do not enter the decisive quadratic form.
4. M14 arithmetic. Independently rebuilt both storage constraints, all eight
   positive leading minors, det A, the Krylov determinant, the 19-by-19
   constraint minor and the displayed nonzero tangent. Its exact D and V
   agree with the manuscript.
5. Entire premium ray. Checked the Fourier shift sign, zero extension,
   Parseval identities and the tangent-half-angle substitution. Both exact
   numerator identities and every coefficient after M=14+u were recomputed.
   The first identity excludes pencil zeros away from frequency0; det Gamma
   handles0 and its leading t^16 coefficient handles pi. Nonzero tangent
   means nonzero control polynomial, giving strict integral negativity and
   then coercivity on each fixed finite-dimensional unit sphere. I derived
   det J, det A and the sampled control determinant independently before
   reading the supplied formula; they match. The Fourier argument is a
   legitimate alternative to storage-matrix existence, not an assertion
   that the M14 storage matrices work unchanged for all M.
6. Density refinement. The displayed mod7 Bezout identity proves quartic
   irreducibility. The cubic sign calculation proves one uniquely smallest
   modulus eigenvalue. Galois transitivity then excludes roots-of-unity
   ratios, giving cyclicity for every nonzero integer power of A. Three
   successive cube-span sums increase dimension to four. The density count
   is sound: for M>=8/delta^2 and sufficiently large interval length, each
   shifted set loses at most (M-1)H boundary points, and the stated pair
   lower bound follows. Iterating selects FIXED superincreasing steps with
   a positive-density set of starts. Only after this selection is the
   fixed-window cutoff applied. There is no variable-window loophole and
   no dependence on a long-arithmetic-progression theorem.

7. Geometric-tail refinement. The exact one-finite-opponent expansion has
   uniform O(beta^2) error by independence and the finite reward bound. At
   a full-contact date, Gamma f-Jq=O(beta^2) and Gamma invertibility imply
   sum q>=beta/(2L0), with L0=max(1,||Gamma^-1 J||_1), after a fixed late
   cutoff. The one-clock conditional identity gives
   beta_k-beta_(k+1)=sum_i q_ik(1-f_i(k+1))
   >=(1-beta_k)sum_i q_ik. Thus eta=1/(4L0) is valid. Monotonicity at all
   other dates and one contact in every late five-date block imply both
   displayed estimates (17), including the constant 5/eta in the entire
   future-beta sum. This is an upper geometric rate, not an assumed exact
   geometric clock, and it supplies no growing-window IFT uniformity.

## Independent falsification attempts and source checks

In addition to rerunning the final checker, I compared formulas (10)--(11)
with direct finite-clock expansions on 48 exact rational random tables for
n=2,3,4,5, using nonzero arbitrary passive pair rewards and signed date
arrays of total mass zero. Every comparison passed. This specifically
attacks the easiest missing-term failure in the generalization. I also
checked the empty-control/tied-pivot, insufficient-rank, missing-owner,
passive-pair-perturbation and growing-window boundaries. They are treated
with their actual scopes; no boundary condition is silently discarded.

I directly inspected the named declarations and relevant definitions in
StoppingLawOperationalDistance.lean, TerminalSemanticPair.lean,
TerminalDebtPrefix.lean, PositiveMinimumSemanticDebt.lean,
TerminalSemanticEqualityStratum.lean and SingletonPacketEnergy.lean.
All cited paths are Git-tracked. The exact payoff/cap behavior bridges,
finite-hazard operational-distance bound, and literal root-prefix identity
have the stated scopes. The singleton packet energy accepts a real mass
vector but has none of this theorem's temporal constraints or pair correction.
The positive-minimum declarations concern total debt on a semantic carrier;
they do NOT supply actual realization or J_r minimization on this observer
carrier. The packet accurately states that distinction. No Lean build or
new Lean theorem is claimed in this review.

## Export admission and nonredundancy

I affirm a SCOPED conditional/residual-mode admission: the complete excluded
class is the stated late controlled-window mode of an ACTUAL observer minimum,
including the eventual-full-support/eventually-strict subclass on the whole
M>=14 ray, and the positive-upper-Banach-density strict-date subclass at M14.
The established actual source-arm hypotheses supply observer optimality,
ALL-END, positive Never and the small-tail limit; the full-support/strict
pattern is precisely the residual subclass being excluded. The packet
produces every new comparison witness itself. Its raw LMI, full-cap descent,
unbounded premium ray, geometric-tail bound and density restriction constitute substantive
additional mathematical narrowing, not merely a supplied-strategy verifier.

The unproduced strategic source is an actual representative of an observer
minimum when starting only from failure of UE. This review does not assert
that all counterexamples have that representative, or that the displayed
Lean total-debt theorems produce it. The actual-versus-inherited source
reduction remains ordinary external source mathematics, and the packet
makes no completed counterexample-to-actual or source-to-UE claim. Inherited
endpoints, finite-support sources, sparse I4 schedules, and contact-dominated
full-support tails remain. Approval is for the exact mode theorem above,
not for a new UE existence class or complete I4/Fin4 closure.

Narrow searches in the relevant Root/Paths/Terminal code and the canonical
research notes found no implemented fixed-cap controlled-window concavity
or an equivalent stronger theorem. The older one-packet energy and local
exact ALL-END tail constructions do not provide this descent. The reviewed
packet includes its own proof, exact positive and negative boundary tests,
source correspondence and narrow Lean handoff; it does not depend on an
untracked temporary checker for a mathematical step.

The final proof and checker were copied byte-for-byte to the canonical paths above.
