# Whole-artifact review by CODEX_NOETHER

## Frozen object and verdict

Reviewed the complete standalone
`notes/CODEX_BROUWER__DEBT_RIGID_MULTIPLE_CAP_SOURCE_REDUCTION.md`,
1636 lines, SHA256
`de5e44b5044f7de40020b00ce30b6caee527102e65e078aaca9bf3515760e5cb`.
The hash was checked again after reading and falsification. This is a
whole-artifact mathematical review of Sections 1–15, not certification
inferred from my earlier focused HR review. I did not read another
whole-artifact review or verdict to reach this judgment.

**Ordinary mathematical PASS; tracked-reference HOLD.** I found no
unresolved mathematical objection to the theorem stated in Section 1.
One citation in HR1 labels a declaration in the currently untracked
external implementation `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`
as part of the tracked vocabulary. I inspected its definition and proof;
the mathematical implication is valid and is already proved without that
file in Section 2. This is therefore not a missing mathematical premise,
but the tracked-source claim must be repaired or the implementation must
become an accepted tracked dependency before packet placement. I did not
edit the artifact or perform a Lean build.

The accepted conclusion is significant necessary-source reduction:
existence of any Fin4 counterexample produces ONE fresh bounded signed
table at which EVERY original-carrier SUM-minimizing pair has the same
debt vector, and EVERY marked minimum produced as specified has a cap
with at least two maximizing TEST POINTS. It is not a UE proof, a
positive-gap example, or a claim that those points have different response
kernels. Those limits are stated correctly throughout the artifact.

## Scope and actual strategic input

The finite data are all sixty recipient/coalition entries for four
players, together with the fixed all-Never reward zero. Prescribed laws
are independent; a deviation replaces one complete law; finite deadlines
and Never comprise the entire cap. No public randomization, stationary
response restriction, selected Nash tail, or conditional debt minimum
enters the proof.

I inspected the named declarations under their displayed imports:

- `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`,
  `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`,
  `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff`, and
  `quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`
  in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`;
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- `quittingTerminalSemanticCarrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  and its `all_punishmentNormal` conclusion in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- `quittingPunishmentValue` and `quittingBestReplyValue` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`, and
  `IsQuittingNormalPlayer` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`.

The singleton margin requires actual closed-carrier membership, global
SUM minimality, and positive debt, not Nash of a root or its tail. The
normality producer has only the full reward bound and literal same-table
no-UE assumption relevant here. It yields the unrestricted punishment
value, not the nominal stationary value. Section 2 obtains same-table
no-UE from the final positive actual infimum, so positive recipient
scaling does not silently transport normality from another table.

The live selection date pays zero, and the absorbing reward begins on
subsequent dates. The artifact preserves that chronology and uses terminal
payoffs only through the stated correspondences.

## Actual marked producer and signed transport

I checked Section 3 independently as part of this artifact. Censoring
small finite tail mass to Never controls prescribed payoffs AND all
opponent-response payoffs uniformly, and hence full caps. Finite-support
profiles have the same actual infimum.

The mixture chart is deterministic bookkeeping. Sampling four raw
coordinates independently preserves independent agency. The densities
are bounded by four; the identity Σ f_i=4 survives weak-* convergence.
Hausdorff limits of endpoints and response locations retain every
positive finite mixture atom as an isolated midpoint, with one unchanged
tie interval. Points not arising from those intervals have zero mixture
atom; in particular c has zero atom. Never remains a separate isolated
label even when its law mass is zero.

The product convergence argument is legitimate: marginal weak-* tests
first give rectangle products; their common L∞ bound extends this to
fixed L¹ tests. Coalition kernels converge outside the null sets of
retained endpoints, c and equal raw independent coordinates. The proof
then separates moving-kernel error from fixed-kernel weak-* convergence.
It does not multiply arbitrary uncontrolled weak limits.

For ALL moving response locations, a retained midpoint forces the old
atom and its tie, while a null-cut limit has zero opponent comparison
mass. Both directions of the cap limit are supplied: extract moving old
maximizers for the upper bound, and approximate a limiting test for the
lower bound. This gives the actual original-carrier minimum, not just
the payoff coordinate of a law limit.

The only signed targets used later are existing positive own atoms and
positive-mass old chronological conditionals. Their likelihood factors
have one common legal two-sided neighborhood and bounded old-chart
densities. At a retained atom the left/right raw endpoint, not the
midpoint, implements strict-before/strict-after; the head-through-root
target uses the right endpoint. Null cuts have vanishing raw-boundary
mass and converging whole-date prefix indicators. Strong indicator
convergence plus the old density bound supplies the moving-cut seam.
The old response kernels and ALL original finite tests remain in use.

No arbitrary insertion of a zero-mass clock is inherited from this
transport. Never conditioning, redundant unit-mass coordinates, negative
parameters, and the exact duplicate c⁺ are handled correctly. c⁺ is not
counted as a second point of X, and c is never identified with Never.

## Cap stability, universal earliest argument, and spectra

The two cap-stability mechanisms are correctly distinguished. A unique
isolated maximizer has a compact complement gap. A unique nonisolated
maximizer has no such asserted gap. For the latter the proof expands
changes into positive old-law multiples and signed EARLY submeasures.
Every nonoriginal term absorbs before the response, giving the SAME
positive affine transform for the ENTIRE upper response family. Only
the lower compact set needs a uniform gap.

The fixed-response debt is multiaffine on the actual legal box. An
interior minimum makes its polynomial constant. Distant endpoints are
used only as selected-response algebraic evaluations except where a
separate full-cap argument proves actual endpoint minimality.

The LC, common-cap, tied sole-unsupported, and strictly-earliest
sole-unsupported arguments produce respectively the stated a, C, J,
and F/G values. I checked the omitted-triple sign C_(I∖{i})=−a_i.
The refinement from a general participant floor to own-minus-grand
uses the ORIGINAL pure law after absence of late mass is established;
it does not purify a polynomial endpoint.

Section 7 is genuinely simultaneous-active: the earliest point is over
ALL four compact active sets. With positive FINAL strict-late masses,
each fixed earlier cut gives signed all-upper affine control and a
possibly cut-dependent lower gap. Passing the late conditionals in TV
does not require a uniform shrinking-cut neighborhood. At the final
conditional endpoint the closed upper formula controls EVERY upper
test, and every lower response pays its own singleton. Thus the selected
caps become actual caps; one equals its singleton; singletonMargin then
contradicts actual positive minimality. This is not an endpoint shortcut.

If a final late mass is zero, the proof retains the original sure-early
exception instead. That owner screens every upper response of each other
recipient, producing finite/Never point multiplicity. The supplied
boundary experiment has precisely the density blowup which prohibits
discarding this exception. Under all-unique caps this exception is
already impossible, giving the finite isolated positive-mixture earliest
atom needed subsequently.

## Whole-table contact comparison and debt rigidity

The full-profile reward bound gives |Δ(r)−Δ(r′)|≤8‖r−r′‖∞. Taking the
worst unit-cube SUM value supplies the upper bound for EVERY newly
selected table; no old minimum is retained. SingletonMargin and the
literal all-Never profile prove Ω≤4/5, used to put target contacts
strictly above Ω.

I checked the complete expanded sixty-coordinate target and all 82
labelled functionals. Their cases are disjoint, each old upper contact
targets at least one, the C triple has the opposite withdrawal sign,
and no individual C summand is assumed positive. The coefficient bound
six gives 12α functional motion. The interval [Ω−16α,Ω] is the actual
new infimum interval; 28α<σ separates all noncontacts. Thus every new
minimum avoids every new label. The separate signed-eight argument
retains its narrower preservation claims; none is inherited by the
expanded target.

For recipient scaling the ORIGINAL debt image A is compact and
nonnegative, and positive diagonal scaling maps the full original
carrier onto the new carrier. W(θ)=min_A θ·a is a true concave scalar
function on a fixed set, not a mixing argument for independent laws.
One-dimensional concavity gives two-sided coordinate derivatives almost
everywhere, Fubini produces one regular θ in the desired open box, and
the positive/negative supporting inequalities force EVERY minimizer to
have each coordinate ∂_i W. This proves all-family debt rigidity.

The gap ζ−14ρ remains positive for every one of the 82 labels. The
final table is fixed before fresh minimizing laws are selected. DR5's
existing-atom reset controls all earlier and later full caps; actual
SUM constancy makes every local pair a minimum; only THEN does rigidity
fix individual debts and force an earliest supported owner originally
pure. Its screening contradiction is valid. The all-isolated later
supported consequence is stated with its additional isolation premise,
not used to manufacture a gap at a nonisolated later selector.

## Complete HR consumer and attempted falsifiers

I tried the following failures against the full proof, rather than
assuming the head-box conclusion from its component review:

- A supplier may maximize only at a nonisolated later point or Never.
  HR4 controls the entire upper family by a positive affine map; it
  needs no later-isolation premise. The lower compact set excludes that
  selector and has a strict gap.
- Conditioning several heads might screen a late selected reply without
  screening an original prescribed late clock. Both are strictly after
  τ, and at least one OTHER conditioned owner exits ≤τ. Thus both see
  exactly the same first head coalition, including every ordering among
  conditioned heads. Their raw regret is zero.
- Constant SUM might allow positive debt to transfer between recipients.
  It would without rigidity. Here full-cap stability first makes the
  small box an actual minimum family, so each regret polynomial equals
  the common fixed d_i*. This legitimizes the distant polynomial
  extraction e_h d_h*=d_h* and yields ORIGINAL e_h=1.
- A single head might coexist with all debt concentrated on its owner.
  The singleton margin gives d_h*≥δ, and an earliest unique zero-own-mass
  owner has a strictly positive integral of pointwise regret. No uniform
  regret gap along its law is required. The contradiction is strict.
- An original sure-head limit might still have finite prelimit leakage,
  or opponent mass at the retained root. HR9 retains η_k explicitly for
  all four prescribed payoffs and three nonmover full caps. Opponent
  root masses converge separately to zero before the through-root A_k
  is replaced by the strictly-before A.
- A favorable selected punishment response might conceal a new owner
  cap. HR10 is instead the exact full formula
  max(H_k,A_k+α_k cap_h(w_-h)); every shifted finite deadline and Never
  is covered. All moving head tests give H_k→H, including empty dates.
  The original q_h is sure-head before this graft, so nonmover response
  leakage is bounded uniformly over all dates by 2Mη_k.
- Negative singleton rewards might invalidate the punishment comparison.
  The infimum is finite, ε-punishments are actual independent opponent
  laws, and fresh same-table normality gives cap≤s_h+ε with no sign
  assumption. Since A+αs_h≤H<B_h, choosing ε<B_h−H gives a strict
  FULL-debt decrease. No opponent Nash constraint enters.

None of these produced a counterexample. The zero-table plateau example
does produce distinct but kernel-equivalent maximizing points; the
theorem explicitly allows this and makes no unsupported rank claim.

## Source hold and final disposition

I read `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in the currently untracked external
`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`, including
the preceding infimum/carrier equality proof. It is ordinary valid
mathematics: continuity over the original closure identifies the literal
infimum with every carrier minimum, and positivity is the already stated
terminal no-UE bridge. Section 2 independently proves exactly the
positive-infimum/no-UE implication needed by HR1 using the tracked
`ExploitabilityGap.lean` declaration.

Accordingly, the narrow repair can delete the redundant untracked
equivalence citation or explicitly mark it non-tracked and rely on
Section 2. An accepted tracked implementation would also resolve the
hold. Calling the present external file tracked is not certified by this
review. No other mathematical correction is requested.

Subject to that source-status repair and the required distinct whole
review, this has export-level value as a strict common-source reduction.
It leaves the substantive simultaneous multiple-cap consumer open.

