# Independent mathematical and value review of the MAX cap-ceiling exclusion

Reviewer: CODEX_NOETHER_SUPPORT.

Reviewed source:
[FULL_NORMAL_MAX_SOURCE_EXCLUDES_JOINT_CAP_CEILING](../notes/CODEX_RADO_BOUNDARY__FULL_NORMAL_MAX_SOURCE_EXCLUDES_JOINT_CAP_CEILING.md).
Frozen SHA256:
`39bfb13ab79024d2ae711c30a38c63854b89a0dfe35622ac472664311d1ee22e`.
All 348 lines were read. No other review was consulted. The candidate and
its prerequisite notes were not edited; no Lean build or export occurred.

## Verdict

Mathematical PASS: no repair is required for the stated produced-source
claim. The passage from the original full-cube tuple to a good-entry tuple
retaining pointwise owner floors and the full limiting normal is valid.
The cap-ceiling contradiction uses those exact fields; it is not a proof
for arbitrary near-minimizers, a selected scalar-pressure entry, or the
four-coordinate singleton-fiber source.

Value verdict: this is a genuine, nontrivial NEW MAX-source face exclusion,
not the old SUM result or the surplus identity under a different name.
Nevertheless I do not presently give an affirmative export-value judgment.
I recommend retaining it as reviewed internal mathematics until its
below-ceiling mass is consumed, or a conjecture-facing construction is shown
to force the excluded face. This assessment is separate from correctness;
it is NOT an objection to the counterexample premise Ω>0 or a demand that
an intermediate result already prove UE. Reasons appear in Section 6.

## 1. Claim reconstructed independently

Let η(r) be the infimum of maximum unrestricted terminal regret over actual
independent stopping laws, for four players, rewards r∈[−1,1]^60, and
literal Never reward zero. Suppose Ω=max_r η(r)>0.

The construction produces one fixed r* with η(r*)=Ω and finite weighted
tuples of actual profiles p, together with response weights λ_p. Write
θ_i(p)=Σ_t λ_(p,i,t). The relevant surviving fields are:

1. E(p)→Ω uniformly across the tuple entries.
2. θ_i(p)≥Ω/4 eventually for every entry and every owner.
3. Inactivity a(p)=Σ_a λ_(p,a)(E(p)−g_a(p))→0 uniformly.
4. The average of the SAME response-law difference rows tends to a full
   outward normal of the sixty-dimensional cube at r*.

The zero tester carries no owner block and remains in inactivity.
The claimed conclusion is that the averaged nonnegative quantity
Σ_i(1−B_i(p)) cannot have a subsequence tending to zero. The positive
lower bound may depend on the produced sequence/table. Neither an
entrywise normal nor an entrywise cap-ceiling gap is asserted.

The simultaneous enlarged-calendar directional field also survives the
construction, but the new contradiction itself does not use it. This is an
important distinction between a retained field and a consumed hypothesis.

## 2. Actual source and quantifier check

I read the complete frozen common-calendar source at SHA `fade3cb8...`
and silent-source bridge at SHA `0e609143...`, not just their summaries.
The common smoothed tester pool contains the full response maximum on all
controller calendars under comparison. Its labelled after-support copies
are not silently merged across enlarged domains.

The original window construction gives full regret near η(r_m), uniformly
over EVERY minimizing profile and EVERY calendar in the window. Thus its
outer convex combination may retain all the needed minimizing tuples;
there is no favorable-profile selection assumption.

The silent shift preserves the prescribed coalition law. Its only new cap
candidate is the initial singleton response, so the uniform positive cap
moat makes the full cap unchanged. The bridge correctly recomputes λ after
shifting; it transports full law-difference rows, not merely payoff values.

For the filtering step, let q_m be the discarded final-calendar mass and
γ_m the Markov threshold for the bridge's averaged directional error.
The discarded bad-entry mass is at most γ_m. A reward row has ℓ¹ norm at
most 2, so deleting those rows changes the unnormalized average by at most
2γ_m. Renormalizing a remaining mass at least 1−q_m−γ_m costs at most
2(q_m+γ_m). Together with the bridge's full-vector transport estimate,
this preserves the limiting FULL cube normal. No projection to one owner
or one selected entry is used.

At each retained entry, the bridge's inequality

    θ_i κ_i ≥ E−ε−R̂−4a_m,        κ_i≤2,

does imply θ_i≥Ω/4 uniformly eventually. Keeping every good entry, rather
than only the favorable scalar-pressure entry, is precisely what permits
this to coexist with the averaged normal.

Reusing the actual laws at fixed r* is legitimate. The old λ remains fixed;
reward proximity increases full-regret error by at most 2δ, inactivity by
at most 4δ, and simultaneous chord error by at most 16δ. Reward-gradient
rows themselves are reward-independent. Finally

    θ_i(E−d_i)≤a

gives uniform convergence d_i→Ω. Thus no SUM-minimizing source, cap
attainer, attained behavioral minimizer, or supplied strategy is smuggled
into the statement. Ω>0 is its explicit counterexample/source premise.

## 3. Independent proof check

Assume along a subsequence the average of Σ_i(1−B_i) tends to zero.
All caps are at most 1. For every owner,

    Σ_t λ_it(1−V_i(t))
      = θ_i(1−B_i)+Σ_t λ_it(B_i−V_i(t))
      ≤ θ_i(1−B_i)+a.

Consequently the averaged response mass at any fixed outcome with
r*_i(S)<1 tends to zero, since each such occurrence contributes a fixed
positive reward deficit. The same argument includes Never's deficit 1.
This uses near-activity, not existence of a cap-maximizing deadline.

If some coordinate r*_i(S) is strictly between −1 and 1, the limiting
normal coordinate is zero. Therefore the owner-weighted baseline mass of
S also tends to zero. The POINTWISE owner floor bounds that mass below by
(Ω/4) times the ordinary averaged prescribed mass. Thus every coalition
with any interior reward coordinate loses all prescribed mass. Positive
averaged owner totals alone would not justify this inference.

Only Boolean reward coalitions can retain prescribed mass. No nonempty
coalition can pay all four owners +1: the corresponding literal pure
profile would attain each owner's absolute behavioral reward ceiling and
would be exact Nash, contradicting η(r*)>0. Hence every remaining Boolean
coalition has social payoff at most 2. Never has social payoff zero, so
the limiting averaged prescribed social payoff is at most 2.

The candidate also validly proves joint Never mass tends to zero. On the
event all opponents of i choose Never, ANY response pays at most max(s_i,0).
Off that event it pays at most 1. Since s_i≤1−Ω,

    B_i≤1−Ω Pr(all four Never).

No opponent/joint-survival identification occurs. This strengthens the
probability account, although eliminating Never is not necessary for the
social-payoff upper bound, because its social reward is already ≤2.

The cap-ceiling assumption and uniform d_i→Ω instead give averaged social
payoff tending to 4−4Ω. Thus Ω≥1/2. The genuine global all-Never comparison
and singleton moat give Ω<1/2, a contradiction. This establishes the
strict liminf statement, including its every-good-tuple-sequence scope.

## 4. Source correspondence actually inspected

The exact current declarations checked were:

- `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`;
- `hasEscapeAwareQuantileClockCompression_of_normalized` in
  `Research/Quitting/EscapeAwareQuantileClockTransport.lean`;
- `exists_finiteClockSemanticPair_exploitability_eq_upper`,
  `escapeAwareQuantileClockUpper_sub_exploitabilityInf`,
  `quantileClockSupport_fin4`, and
  `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`;
- `exists_minimum_quittingTerminalSemanticExploitability` and
  `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`;
- `minimumTerminalSemantic_maximumDebt_allPlayersTie`,
  `not_allNever_positiveMinimumTerminalSemanticExploitability`, and
  `minimumTerminalSemantic_maximumDebt_lt_half` in
  `UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`.

In particular the finite-law approximation is not a supplied-compression
assumption: the normalized-reward producer supplies that hypothesis. Its
literal Fin4 support 8k+1 and error 24/k give the table-uniform approximation
used in the source. The full tuple/normal construction and the present face
exclusion remain ordinary mathematical proofs, not newly Lean-checked facts.
The robustness declaration's CURRENT path is under Quitting/Terminal, not
the historical Research path in the frozen originating note.

## 5. Attempted falsification and boundary calibration

I independently recomputed the candidate's solved fixture r_i(S)=−1 for
i∈S and +1 otherwise. With four independent uniform clocks on {1,…,N},

    Pr(i is a first quitter)=(N+1)²/(4N²),
    B_i=1,       U_i=1−(N+1)²/(2N²).

At λ_(i,Never)=1/4, every owner is active in the weight sense, inactivity is
zero, and every response displacement is outward normal. Its nonempty ℓ¹
norm equals the actual gain. These identities, all 24 owner/size normal
sign tests for N=1,…,6, and 156 one-owner finite-deadline/Never endpoint
tests passed independent exact Fraction enumeration.

For the arbitrary-law directional claim, fixing three proper original laws
makes all four Never response payoffs identically 1 after changing the
fourth law. The weighted gain is half the expected first-coalition size.
That size is at least 1, proving the stated one-column and simultaneous
derivative lower bounds. This verifies the claimed all-law calibration,
not just the enumerated endpoints.

The fixture's global η is zero because all Never is exact Nash; its
displayed debts converge to 1/2, not the global minimum. Hence it does
not falsify the theorem. It does decisively rule out describing the proof
as a consequence of full normality, near-activity, ties and vanishing
directional error alone. The actual global half-bound is indispensable.

Other audited failure modes were loss of the entrywise owner floor,
normality asserted at a single selected entry, use of only four normal
coordinates, signed singletons at Never, a nonexistent cap attainer, and
normalizing different owner blocks to different baseline laws. The source
and proof avoid all of them.

## 6. Novelty and separate export-value assessment

I read the relevant MAX/SUM distinctions and Sections 9–10 of HILBERT's
extremal reward note at its cited SHA `0584db0c...`, and narrowly searched
the nearby NOETHER/FRECHET/HILBERT source accounts. The older theorem uses
SUM-minimizing sources, one common normalized baseline, total-variation
budget Δ, and Δ<1. The present MAX source only gives total debt tending to
4Ω, which can exceed 1. Its owner blocks cannot independently be normalized
without losing their common baseline. Thus that theorem does not subsume
this one by a change of notation or the identity ΣU=ΣB−Σd.

The genuinely added mathematics is the full-normal support elimination at
a putative ceiling limit, combined with the Boolean social-payoff bound
and the actual MAX strict-half theorem. I would preserve and cite that
result, not dismiss it as an algebraic restatement.

However, the current useful output stops at positive averaged response
mass below the reward ceiling. It does not locate that mass in a particular
strategically useful coalition, exclude Never, assign it to one normal
source, force a feasible law direction, or constrain a currently produced
equilibrium mechanism. The candidate correctly records these limitations.
No identified source construction presently forces the joint cap-ceiling
face; its removal therefore does not yet discharge a named producer seam
or yield an actionable raw-table/strategy alternative.

That is why I do not affirm the exceptional importance needed for export
at this checkpoint. A concrete consumption of the SAME below-ceiling mass,
or a construction reducing the remaining argument to the excluded face,
would change that assessment without requiring a complete UE proof. The
present result is reviewed, mathematically sound internal progress; this
review is not a promotion or an unrestricted source-class theorem.
