# Independent whole-artifact review: finite singleton split

Reviewer: MIN_NEVER_SELECTION. Ordinary mathematics; no Lean command.

Final artifact reviewed:
`math/exports/FINITE_SINGLETON_SPLIT_UNIFORM_EQUILIBRIUM.md`, SHA256
`16c3ad54f6d442d0440f8e3a5e29ed06bd81101b2dd054cb3dea6fa4a93519b8`.
The assembled artifact was read in full, including its self-contained core,
exact reward interval, coverage certificate, stationary approximation
boundary argument, and formalization caveat.

**Verdict: mathematical PASS.** No unresolved mathematical objection remains.
The packet produces uniform equilibria on a new raw reward class. It does
not solve arbitrary Fin4 or assert a numerical bound on its large-K threshold.
No strategic witness required by the conclusion is left unproduced.

## Independent derivation and raw selection

I independently found the same finite singleton-0 repair while analyzing
backward Nash prefixes of the concrete table. The proof does not use the
numerical optimizer's small regret. At the limiting
B=(0,-1/9,0,5/9), hazard1/10 gives X=(0,1/10,1/5,2/5). Its quiet Quit vector
is(-1/10,-1,1/10), giving margins(1/5,6/5,3/10). The remaining aggregate
2/7 gives A=(0,9/14,5/7,0). Exact Fraction arithmetic independently checked
every coordinate, every strict margin, and total singleton-0 mass5/14.

For general raw data the finite step has prescribed and Continue values
X=x Gamma[:,0]+(1-x)B. Owner0 is indifferent at zero. The quiet Quit values
are exactly x zeta_j. The interval constraints produce x from raw reward
entries, rather than assuming a strategic return. The sufficient test(4)-(5)
is valid: H=n0-max(zeta1,0) simultaneously controls positive X1 and its
joining comparison, and max(zeta3,0) simultaneously controls X3 positivity
and its joining comparison. Cross multiplication gives the stated L<U test.

The weak boundary zeta2=f is safe for every finite core, not just in a limit:
B_N2=0 exactly, so X_N2=x f=x zeta2. Only rows1 and3 require the printed
strict joining margins. The complete interval, rather than only the
sufficient scalar test, is retained in the theorem.

## Complete core construction and all-large-K coverage

The self-contained core equations reproduce the complete sixty-reward
expectations. Their zero-t maps, row3 backward contraction, weighted entrance
sum, and triangular limiting Jacobian are consistent. Positivity of physical
hazards, including the compactified negative p range, is supplied by(C14),
not assumed in deriving that inequality. Terminal Y and Z have the same
sign; their boundary and wash inequalities persist transversely.

I audited all uses of the previous positive B1 guard. None occurs in the
Banach estimates, analytic entrance equation, nonsingular return equations,
or exact deletion. It had protected the solo2 row1 comparison and the
fully refined solo0 execution. The former instead follows from
-K b_N<B1_N for large K; the latter is replaced by the finite step.
Ell may be arbitrary finite: its core contributions are bounded analytic
terms multiplied by alpha, while its other occurrences are in the explicitly
selected outer quantities. Positivity of ell was a consequence of the
removed guard, not an independent analytic requirement.

The final artifact retains the actual C3_N, which need not be zero. Its
convergence to zero suffices for B3_N, a_N, and the strict finite-step guards.
A_N, B_N, and C_N are defined with their exact finite values. The split does
not silently substitute a limiting continuation for an actual finite one.

Deletion of the last pure3 core root preserves the entrance C_N and thus
B_N and the chosen split. The changed execution leaves every outer affine
return equation and total survival unchanged. Increasing the starting
length preserves the exact adjoining K intervals. Therefore the producer
covers every sufficiently large K/(1+|p|), not merely a chosen subsequence.
Compact uniformity follows from the same strict margins and finite local
choices of the raw split; equality zeta2=f introduces no approximation error.

## Full deviation and fixed-target audit

The refined solo0 prefix joins nonnegative quiet annotations A_N and X_N.
Conditional subdivision preserves its total survival and all prescribed
payoff identities. Each immediate joining surplus is bounded by the mesh
times the positive joining coefficient. The finite0 root and finite2 root
remain adjacent: a zero-payoff empty quitting opportunity is never inserted
at the negative B1_N annotation. Their actual player1 Quit comparisons are
x zeta1 and -K b_N.

The final solo3 refinement has nonnegative row0/row1 annotations and a
strictly positive row2 floor, giving its stated exact comparisons. The core,
finite wash, and finite2 root retain all their exact comparisons. The full
Bellman recursion carries the literal continuation best-response cap after
Continue. It therefore prices all finite deadlines and literal Never, and
hence every independent complete behavioral replacement.

Every deviator faces opponents-only period absorption at least
min(a_N,b_N)>0. Unrolling the cap maximum bounds the full excess by the
largest mesh error; errors are not summed once per root. Policy absorption
also occurs almost surely. Consequently every prescribed and unilateral
terminal payoff shifts by kappa_i when passing from native to original
rewards. No false affine invariance is asserted for arbitrary nonabsorbing
profiles.

For each fixed raw game, K,p, the selected finite core and the initial target
are fixed before accuracy. Only subdivision of the permitted diffuse blocks
changes. The same target kappa+A_N is delivered exactly in the terminal
model, and geometric opponent absorption supplies the uniform finite-horizon
estimate. Thus the result is an original uniform-equilibrium payoff theorem.

I inspected the declarations
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
I also checked `MixedCycleSoloMesh.SourceCertificate` in
`UniformEquilibrium/Quitting/Cycles/MixedCycleSourceCertificate.lean`:
its singleton_floor hypothesis is genuinely stronger than the constructed
negative-return calendar. The packet correctly avoids its padding compiler
and proves the literal variable-length refinement directly.

## Exact interval and coverage checks

The parameter calculations independently give
J=1-ell/4, B1=(6ell-4)/9, and A1=(3/7)(1+ell). The stated raw singleton
range is -1<ell<4, and the finite-step test extends it precisely to
-1/6<ell<4 on the displayed completion. At ell=1/2, interval(3) is
(1/19,5/23). At ell=-1/6 its two decisive endpoints meet at5/23.
The positive test, collapse test, complete table, and physical return chain
all agree. No conclusion at that collapsed boundary or at K=100 is inferred.

The coverage appendix contains all data and exact arithmetic rules needed
for its certificate. I inspected an independent standard-library rational
implementation and reran it: all80 nonzero stationary patterns were excluded
in862 nodes and all65 sure-root patterns in365 nodes. I checked the monotone
K relaxation, the nonnegative inverse-column argument for the origin bound,
and the degree-two Bernstein subdivision rule. These are necessary systems
for every K>=100, not floating-point searches or checks of one selected root.

I separately reran exact matrix algebra. The determinant, full inverse, all
four triple inverses, outside row(-7/10,9/10,-1/5), reciprocal-pair signs,
unique old chamber labeling, and unique attached-pair labeling agree.
The unique chamber labeling has B1=-1/9 and Gamma10=2, excluding both prior
outer returns even after permutation or positive playerwise scaling.

The added stationary compactness argument is necessary and correct. At a
nonzero hazard limit, the Quit/Never comparisons give the F signs whenever
opponents have positive hazard; if all opponents vanish, that owner's F is
identically zero. Thus no nonzero cluster is possible. At zero hazards,
normalization gives a nonzero simplex vector with Gamma x>=0 and active
complementarity; a sole-owner limit violates a negative column, and any
larger support violates principal nonsingularity. There is therefore a
positive stationary regret floor for each fixed table, including the
zero-hazard boundary. No floor uniform in K is claimed.

The weighted-ledger exclusions follow directly from coalition12 and
J_02(w)=w1+w3/2; they test all nonnegative weights. Coalition123 has strictly
positive participant vector(11,2,1), defeating every supportwise balance on
that support. The positive singleton graph forces the full marked set for
the stated ordered-anchor criterion. The intersecting same-sign reciprocal
pairs exclude every signed-cycle labeling and the required disjoint pair
patterns. These are complete tests of the named finite or weighted selector
domains, not one-witness failures.

I inspected the exact source hypotheses of
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`,
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`,
`IsSupportwiseBalancedQuittingPremiumTable`,
`exists_uniformEquilibriumPayoff_of_supportwiseBalance`, and
`SignedFourCycleSingletonData` in the files named by the artifact.
Their raw comparisons match the appendix. Its scope does not purport to
exclude every imaginable nonstationary certificate.

## Retained conclusion

The raw interval produces the missing legal execution, and the packet itself
produces every finite core, wash, return and refinement needed to consume it.
The explicit ray supplies a strict class increment relative to the audited
existing criteria. This qualifies as actual UE-class coverage rather than a
supplied-object verifier. Arbitrary Fin4 and the remaining raw return regions
remain open. No Lean build or new Lean theorem is claimed.
