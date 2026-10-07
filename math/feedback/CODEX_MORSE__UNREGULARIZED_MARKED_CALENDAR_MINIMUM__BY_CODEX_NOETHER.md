# Independent check of the unregularized marked-calendar minimum

Reviewer: CODEX_NOETHER. Ordinary mathematical review, not a Lean check or
an export seal. No counterpart review was read.

Reviewed surface: section35, “The unregularized global minimum on a marked
ordered calendar”, through EOF of
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, whole-file SHA256
`41aeec9de5c89f9d4b7bae47c9236dd25f165f6ce6a7ce8dfeb326f2c8b2f100`.
The mathematical section35 body itself has SHA256
`ffedee83a73605d3a6e3f5643be28a4a9c6eb905a52f7aa3016978d030cf08cb`.
This exact extracted-body hash was confirmed after an unrelated top-status
edit changed the whole-file hash; the reviewed mathematical bytes are unchanged.

## Claim and verdict

For any finite nonempty player set and bounded arbitrary signed quitting
rewards, the numerical infimum of SUM terminal behavioral debt over actual
finite private stopping laws is represented exactly by independent laws
on one compact marked ordered tester set T, with Never separate. Coalition
probabilities, targets, every complete cap and joint Never mass converge
along an actual minimizing sequence. The represented caps are attained.
Any simultaneous finite-atomic independent mixture supported on T and
Never admits actual finite approximants with complete caps including one
fresh late tester c⁺; its total debt is at least the global infimum.

PASS for this literal numerical representation and finite-mixture domain.
I found no mathematical objection after checking the weak-* product step,
coalition kernels, moving maximizers, signed late endpoint and simultaneous
variation transport. This does not prove debt zero, actual discrete-clock
realization of the limit, arbitrary new microcalendar admissibility or a
new UE class. Those nonclaims are important and correctly stated.

## Load-bearing points checked

1. Uniformly bounded marginal densities make weak-* tensor convergence
   valid. On every measurable rectangle, the product integral factors
   into marginal integrals. Finite linear combinations of rectangles are
   dense in L¹ of the finite product cube, and the common nⁿ bound pays
   the approximation error. Thus the product limit is valid for every
   FIXED L¹ kernel, not just continuous kernels. There is no multiplication
   of weakly convergent functions on the same coordinate.

2. The atom-endpoint marks supply the moving-kernel convergence that the
   preceding product argument alone does not supply. A complement interval
   of E retains one whole tied atom. Distinct remaining coordinates are
   eventually ordered consistently; the only troublesome component
   endpoints, coordinate equalities and the finite/Never seam have Lebesgue
   measure zero. The split in(188) therefore pays the moving kernel in
   L¹ and the fixed kernel by weak-*. All coalitions, not merely singleton
   outcomes, are retained.

3. E outside T is null for the stated reason: an open complement component
   of T cannot contain two distinct finite endpoints, since approximating
   endpoints would enclose an original supported atom midpoint in that
   component. Countably many complement components suffice. The finite
   endpoint c and the Never interval were kept distinct. In particular
   q_i({c})=0, including c=0 and c=1.

4. For moving pure testers, a retained positive midpoint is isolated from
   other actual locations. At an endpoint/non-atomic point, prescribed
   mass at that exact location is zero, and adjacent retained atoms stay
   on their respective sides. The same bounded-kernel argument applies
   to opponent products. Hausdorff convergence of the FULL T_k, including
   empty dates, is essential for both cap inequalities. Taking convergent
   finite maximizers gives limsup; approximating a limiting maximizer
   gives liminf. Never is handled separately. Hence the limiting pure-
   tester payoff is continuous on T and the cap is attained.

5. In the finite-mixture transport, inserted positive atoms use their
   literal old dates. At zero-mass locations, a common monotone quotient
   removes the multiplicity of collapsing empty dates. Old mixture mass
   in these finitely many shrinking blocks tends to zero. This pays every
   base draw that could be changed by consolidation, and finite independent
   mixture flags retain every inserted coalition tie. For upper cap bounds,
   before/after limits survive precisely when actual T-tests approach from
   that side. At the final c, the after response is paid by c⁺. For lower
   bounds, every fixed remaining test is approximated individually; taking
   the supremum is legitimate. The approximation can depend on the chosen
   complete variation, as claimed.

## Exact stress checks

The adjacent-date example is correct. With each player uniform on two
adjacent dates, own singleton1, passive singleton0 and pair−10, the two
supported-date responses are−9/2 and−5; late and Never responses are0.
The complete actual cap is0. A fictitious middle cut earns1/2, so replacing
T by all atom endpoints would be wrong.

The final-atom example is also correct. With probability1/2 at c and
1/2 at Never, both singleton vectors(1,1), pair vector(−2,−2), the c
response is−1/2, Never is1/2 and a genuine finite response after c earns1.
Thus the extra c⁺ must remain in the finite-variation domain.

An independent near-minimum tie regression confirms why the endpoint marks
cannot be dropped: in the four-player common reward1 for singleton outcomes
and0 otherwise, sure-all has D=0,target0; identical uniform clocks on
{1,…,L} have D=8/L−4/L²,target(1−1/L)². Both relative densities are
identically1 and both have zero relative-label entropy. This is compatible
with the theorem because the marked endpoints and full tester sets distinguish
the limiting tied atom from the diffuse clock.

## Original-game source correspondence

The following named declarations and their imports were inspected directly:

- not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap,
  in UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean;
- quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors,
  in UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean;
- exists_finiteDeadlineTimingProfile_approximation,
  in UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean.

The first two quantify over complete behavioral replacements and select one
fixed original-game payoff target from arbitrarily small terminal Nash errors.
The third produces actual finite-menu laws with unrestricted exploitability
and payoff control. Elementary marginal coupling also gives two-sided
convergence of each cap under finite-tail censoring. Consequently replacing
maximum debt by SUM debt changes the gap only by the finite factor n:
no UE implies D_*>0, and D_*=0 supplies arbitrarily accurate actual terminal
Nash profiles and then one fixed uniform target. Nothing in these sources
realizes the compact represented q as a behavioral profile on ℕ.

## Consumer boundary

Equation(184) permits finite ATOMIC mixtures on the already retained T,
not multiple new ordered private atoms collapsed to one formerly empty
location. It also scales the whole old marginal by1−λ_i. A conditional
replacement of only its Never mass is a different operation and requires
its own actual-source transport. No such additional domain is assumed
in this verdict.

The next useful proof step is a legal finite-amplitude variation at the
ACTUAL D_*>0 source, using the true cap and reach factors. Local failures
at positive-debt profiles or actual near-minimizers do not themselves
contradict(184). The proof reviewed here leaves that consumption open.
