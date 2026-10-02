# Final export review of generic screened-root exclusion

Reviewer: CODEX_PORTMANTEAU_SCREEN.

Verdict: **ACCEPT**. I read the complete assembled packet and accept its
mathematical claims and export admission with no unresolved objection.
This acceptance applies to the following exact bytes, including an
unchanged copy placed under a stable mathematical filename in `exports/`.

Reviewed file:
[CODEX_SCREEN_GATE__GENERIC_SCREENED_ROOT_EXPORT_PACKET.md](../notes/CODEX_SCREEN_GATE__GENERIC_SCREENED_ROOT_EXPORT_PACKET.md).

Reviewed SHA-256:

    c605fc9a9c34103843ab82a22eac889a89f0d8605cb17fd304edf0395c33037a

This is a complete-packet review. It extends my
[strategic source and compactness review](GENERIC_SCREEN__BY_CODEX_PORTMANTEAU_SCREEN.md)
with an independent check of the polynomial, compatible witnesses, generic
selection, strict separation, and boundary diagnostics. The earlier
[notebook](../notes/CODEX_PORTMANTEAU_SCREEN__MINIMUM_SINGLETON_COLLAR.md)
records the detailed strategic proofs and source inventory. The final
assembled packet, not only the original manuscripts, was read in full.
No new Lean compilation or axiom audit was performed by this reviewer.

## 1. Accepted result and gate classification

For four-player quitting games with independent private behavioral
strategies and unrestricted unilateral behavioral deviations, the packet
constructs a nonzero degree-144 integer reward polynomial on the 56
non-own-singleton coordinates. Nonvanishing excludes every screened product
root with four equal positive complete debts. At a positive singleton-fiber
maximum it gives a strict common screened-root floor.

Existence of any counterexample implies existence of a rational interior
generic fiber with a positive maximizing table, the strict floor, and a
positive total prescribed singleton-mass bound at every sufficiently
accurate actual near-minimizer. That mass bound is uniform on each fixed
positive-gap portion of the fiber and attaches to the same actual
common-calendar profiles and tester weights. Independently, positive MAX
minima satisfy the harmonic inequality, and the maximum global infimum
exploitability over the four-player unit reward cube is strictly below 1/3.

The qualifying category in `math/exports/README.md` is a proved reduction
that strictly narrows an open obligation. The named obligation is the
strict-gap singleton-pressure source in Sections 4–7 of
[MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md).
The packet strengthens its pure sure-coalition floor to all screened mixed
roots and removes zero-singleton minimizing laws from the selectable
counterexample source. Its extra harmonic result sharpens the existing
positive-error bound. This is substantive progress in the stated reduction,
not another verifier for a strategic witness left to be supplied.

Unproduced strategic inputs required by the claimed conclusions: **none**.
The forward theorem starts from the hypothetical existence of a
positive-gap table, which is the premise of the counterexample-preserving
reduction. It need not exhibit a counterexample in order to prove that
reduction. Genericity, rational b, the strict gap, the minimizing joint
carrier, the singleton collar, and the finite source with weights are
produced by the packet or its cited theorems. No conditional-result
exception is needed or invoked.

The remaining post-response full-regret improvement is unproduced, but is
explicitly outside the packet's conclusion. Neither a new low-regret
strategy producer nor a proof of the finite-quitting conjecture is accepted
or asserted here.

## 2. Independent polynomial and selection check

At a root with sure pair {a,b}, after any unilateral deviation another sure
quitter absorbs at zero. The Quit/Continue endpoints therefore compute the
complete response cap, including every later finite date and Never. A
positive tie forces each sure-player Continue-minus-Quit gap to equal the
positive debt, and selects one of the two correct optional debt branches
for each remaining player. All four branch combinations and all probability
boundaries are included. Every used reward entry avoids its recipient's own
singleton coordinate.

For each branch matrix A, its signed maximal-minor vector w satisfies Aw=0.
Nonzero P=w_0w_3−w_1w_2 makes A rank three. A tied branch vector
z=(1,x,y,xy) would be a nonzero scalar multiple of w, contradicting
z_0z_3=z_1z_2. Rank-deficient cases correctly give P=0 rather than an
unjustified exclusion.

I independently checked the bounded witnesses. After multiplying the
equality rows by four, their matrix has first row (1,0,0,1), second row
either (0,−1,0,0) or (−1,1,0,0), and third row either (0,0,−1,0) or
(−1,0,1,0). It has rank three, and the original cofactor vector is

    w=±(1,ξ,υ,−1)/64,

where ξ and υ are zero for Q and one for C. Thus

    P=−(1+ξυ)/4096,

which is −1/2048 for CC and −1/4096 otherwise. The four endpoint pairs for
each sure recipient are disjoint; the optional pairs are disjoint; and
different recipients use different coordinates. These assignments coexist,
leave own singletons free, and have magnitude at most 3/8.

Separate nonzero witnesses for each of the 24 factors suffice because the
polynomial ring is an integral domain. Each nonzero factor is homogeneous
of degree six, so their product has degree 144. The resulting nonvanishing
set is open and dense, with rational points dense in it. No simultaneous
installation of all 24 witness patterns is assumed.

Reward continuity applies uniformly to every prescribed and deviated law
before taking the cap, player maximum, and profile infimum. Hence both
the screened-root minimum and fiber maximum are attained in their stated
compact domains. If θ=Ω_b>0, a screened root would be a positive actual
global MAX minimum; the existing tie theorem would contradict Π≠0.
Positive common scaling and sufficiently small rational perturbations of
b preserve a hypothetical positive gap. Thus the good fiber is produced,
not assumed of an arbitrary incoming table. Its maximizing own-singleton
vector need not be rational.

## 3. Strategic, compactness, and common-calendar check

The source definition `quittingContinuationBestResponseValue` in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean` is the supremum over
all unilateral `BehaviorStrategy` replacements.
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
has exactly the claimed complete pure-clock extremality scope.

`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
and `minimumTerminalSemantic_maximumDebt_allPlayersTie` in
`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`
apply at the same positive MAXimum-debt minimum. The packet does not switch
to a total-debt minimum. Its elementary proofs and unit-bound hypotheses
are correct.

The independent-clock inequality u_i≥p(1−a_i) correctly shows that a
zero-singleton limiting law has Never mass zero or one. Never mass one
would give U=0; the MAX moat then gives s_i≤0 and an actual all-Never
zero-debt profile, contradicting positive minimum. This supplies the
Never-zero hypothesis rather than silently assuming it.

`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin` in
`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`
then applies with precisely its required joint-carrier membership, zero
Never and singleton masses, at least two players, and s_i<B_i. It outputs
one unpadded screened root with the same prescribed payoff, unrestricted
cap vector, and complete outcome law. Its proof's strict cap sandwich
removes the early singleton branch. No ancestry or additional strategic
input is hidden in this theorem.

The joint-carrier minimum set and the varying-table minimum graph are
compact as claimed. Evaluating the same actual laws at nearby rewards
changes each payoff and each full cap uniformly, while leaving their
outcome law unchanged. This validates graph closure and the uniform
near-minimum collar for all s with η(r_b(s))≥a>0. The quantifier is every
actual near-minimizer, which is what the calendar attachment needs.

I read the membership-fiber dependency's Sections 4–6. They consume a
fixed fiber, positive Ω_b, strict pure-root floor, complete finite
approximation, and the MAX moat. They do not consume the preceding
stretch formula or the original full-cube maximizing table. The new
source supplies all these inputs with a stronger root floor. In
`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`,
`escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`
supplies normalized compression internally; the finite-clock upper
attainment theorem therefore introduces no open compression premise.

Every inner minimizer is uniformly near η(r_m), and η(r_m) tends to Ω_b.
The collar applies before tuple/calendar selection. Silent shifting,
weight selection or transport, and final reward-table transport preserve
the prescribed law. All six Section 7.2 fields thus hold for the same
actual profiles and final weights, with fixed b, r_infty, gamma, and
kappa preceding accuracy and calendar-depth requests.

The packet correctly disclaims preservation of an arbitrary incoming
table's inverse-stretch ancestry, individual or sixty-coordinate reward
normals, a fixed-date singleton atom, a response-law singleton mass, cap
attainment, or post-response cap control.

## 4. Harmonic argument and explicit falsification attempts

On the strict Continue-cap branch the exact prefix debt is

    d'_i=β_i d_i+q_i(H_i+β_i U_i−Q_i).

At a positive MAX minimum, q_i=tλ_i has derivative
λ_i(B_i−s_i)−mΣ_jλ_j. Taking reciprocal margins makes all derivatives
equal. A harmonic sum greater than one would decrease every debt for one
sufficiently small legal product prefix, contradicting carrier minimality.
Finiteness and strict cap margins justify the common interval; collisions
and complete responses are already included in the exact identity.

The strict all-Never comparison gives max_i s_i>m. One corresponding margin
is strictly below 1−m, while the other three are at most two. The resulting
m/(1−m)+3m/2<1 yields m<1/3. Compactness and continuity then give an
attained worst unit-cube value strictly below 1/3. These are MAX claims and
do not optimize or import any total-debt constant.

I checked the following attempted falsifiers and their exact interpretation:

- Probability endpoints remain covered by the branch polynomial; missing
  three-sure or four-sure boundary roots cannot evade the argument.
- The zero table has a zero-singleton all-Never minimum, confirming why
  positive gap is required. Without independent private clocks, a public
  mixture of all Never and a sure pair would defeat the Never dichotomy;
  that enlarged randomization model is explicitly absent.
- The anchor table has exact one-sure Nash q=(1/2,1/2,1/2,1). Setting q_3=1
  cannot increase screened regret. Each of the three possible active sure
  players forces e≥(1−e)(1−2e)/2, and the displayed two-sure equality
  profile attains e_*=(5−sqrt(17))/4.
- Scaling by 1/4 and perturbing by 3/4000 preserves a screened floor above
  1/20. The anchor dependency's Section 4 gives exact parent equilibrium
  throughout the rescaled neighborhood, since 3/1000<1/8. Density supplies
  generic rational points there. Thus Π≠0 and θ>0 can coexist with η=0;
  they are not themselves counterexample certificates.

The finite archive regressions are corroborating evidence, not substitutes
for these universal proofs. Their execution was independently reported by
the algebra reviewer. I verified the archive hash and that its proof member
has the same hash as the retained sibling proof; I did not rerun the script.
The corrected reproduction command performs the required JSON normalization
before comparing its tuple-containing Python result to parsed JSON.

## 5. Mandatory export gate coverage

| Gate | Assessment |
| --- | --- |
| Exact self-contained statement | Four players, all 60 reward coordinates, independent clocks, complete deviations, semantic carriers, and the parameter-before-accuracy quantifiers are explicit. |
| Complete definitions and proof | The polynomial, witnesses, selection, zero-Never step, collars, attachment, and harmonic bound are proved. The product-base and calendar constructions are named established dependencies with matching inputs. |
| Probability and agency audit | The packet uses unconditional terminal expectations, private independent laws, full behavioral deviations, and separate Never responses. No public tuple mixture is played. |
| Actual-data adapter or strict reduction | Common scaling and generic rational selection produce the reduced source from any hypothetical counterexample. The named prior source obligation is strictly narrowed. No strategic witness needed for this output remains unproduced. |
| Exact boundary tests | Individual polynomial witnesses, endpoint cases, the zero table, the solved generic anchor neighborhood, and explicit noncoverage checks test the relevant hypotheses. |
| Source and implementation audit | Exact cap, MAX moat/ties, unpadded joint realization, current reward robustness, unconditional normalized finite approximation, and terminal semantic endpoints were inspected. Existing results are credited; no publication-priority or new Lean-status claim is made. |
| Independent substantive review | This is a complete independent acceptance with an explicit falsification attempt. The packet also names the separate complete review by CODEX_CAYLEY_SCREEN; final promotion can verify both review files and their matching hashes. |
| Lean handoff | Section 11 specifies definitions and theorem shapes, keeps proven outputs out of assumed certificate fields, separates elementary algebra from semantics, and leaves implementation/trust checks to formalization. |

The current reward robustness path and source statements were verified:
`abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` and
`quittingTerminalExploitabilityInf_scaleQuittingReward` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
The terminal equivalence declarations in
`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` and
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
have the stated unrestricted and uniform-payoff scopes. This review grants
mathematical acceptance only, without an L, A, or C seal.

No unresolved mathematical, source-hypothesis, or gate-admission objection
remains for the SHA-256 identified above.
