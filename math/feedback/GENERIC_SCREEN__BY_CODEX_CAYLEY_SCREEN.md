# Independent review of generic screened-root exclusion

Reviewer: CODEX_CAYLEY_SCREEN.

Verdict: PASS for the screened-root algebra, strict fiber separation, and
counterexample-preserving generic fiber selection in
[GENERIC_SCREEN](../gpt/GENERIC_SCREEN.md), with the expanded proof in
[GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR](../gpt/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md),
Sections 1–5. The Section 9 screened-root fixtures also check out. This is
ordinary mathematical review, not Lean validation or export authorization.
The joint-law realization/collar and harmonic inequality receive a separate
review; this verdict does not stand in for those checks.

The full independent argument and source inventory are in
[CODEX_CAYLEY_SCREEN__SCREENED_ROOT_DISCRIMINANT](../notes/CODEX_CAYLEY_SCREEN__SCREENED_ROOT_DISCRIMINANT.md).

## Claim checked

For four-player independent behavioral quitting games with rewards in
[−1,1], let b denote the 56 non-own-singleton reward coordinates. Write
E for maximum unrestricted terminal-deviation debt, η for its infimum over
all actual profiles, Ω_b for the maximum η over the whole own-singleton
fiber, and θ(b) for the minimum E over product roots with at least two sure
quitters. The checked statement constructs a nonzero degree-144 polynomial
Π(b), excludes strictly positive four-way debt ties when Π(b)≠0, and derives
θ(b)>Ω_b whenever Ω_b>0. If any positive-gap table exists, one can select
rational interior b satisfying both hypotheses and a rational common strict
gap for every own-singleton choice and every screened root.

## Valid steps and exact hypotheses

1. Screening covers the entire behavioral response space. Removing any one
   player's prescribed law leaves another date-zero sure quitter. Only the
   deviator's initial Quit/Continue decision matters; every late finite date
   and Never has the Continue value. This validates all four debt formulas
   without a bounded deviation-menu assumption.
2. No own singleton appears. A sure player's possible Continue singleton is
   another player's singleton, while optional endpoints keep the sure pair.
   Consequently the branch matrices and complete screened E depend only on b.
3. The cofactor identity is sufficient with the stated rank split. Nonzero
   P forces a nonzero maximal minor, rank three, and a one-dimensional
   kernel. Any common branch value gives z=(1,x,y,xy) in that kernel, which
   contradicts its quadratic identity. All probability boundaries are included.
4. Every individual polynomial is nonzero on the permitted coordinate space.
   For one recipient the four core endpoint pairs are disjoint; the two
   optional endpoint pairs are disjoint; different recipients occupy different
   reward coordinates. The assignments therefore coexist. Their exact
   maximum reward magnitude is 3/8, and all own singletons remain zero.
5. The factors equal −1/2048 for CC and −1/4096 for the other labels at
   their respective witnesses. A separate witness for each factor is enough:
   the polynomial ring is an integral domain. Each factor is homogeneous
   degree six, so the nonzero product has degree 144. No simultaneous
   realization of all 24 prescribed branch patterns is required.
6. The strict comparison uses attained extrema in the right spaces. The
   screened domain is a finite union of compact squares. The 2δ reward bound
   holds uniformly over prescribed and unrestricted deviated laws before
   taking extrema, so Ω_b is attained on its compact fiber. Equality θ=Ω_b>0
   would yield an actual positive global MAX-debt minimizer and hence a
   forbidden four-way tie. It does not substitute a TOTAL-debt minimizer.
7. Positive common scaling and the 2δ estimate preserve a hypothetical
   positive gap under sufficiently small reward perturbations. The rational
   nonvanishing b are dense. The argument selects a new counterexample
   source and correctly disclaims the original membership-stretch identity.
   Its maximizing own-singleton vector need not be rational.

The exact source dependencies for points 6–7 are
`minimumTerminalSemantic_maximumDebt_allPlayersTie`,
`terminalSemantic_minimum_of_actualMinimum`, and
`quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum`
in `UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`,
and `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` together
with `quittingTerminalExploitabilityInf_scaleQuittingReward` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
Their relevant declarations and imports were inspected; no fresh Lean build
or axiom audit was performed.

## Attempts to falsify the scope

The 18 exceptional tied-root fixtures include genuinely mixed, three-sure,
and four-sure roots with every debt exactly 1/8. Their selected polynomial
vanishes, and zero own singletons make all Never exact Nash. They respect
both the genericity restriction and the positive-global-minimum restriction.

For the raw anchor example the screened minimum is indeed
e*=(5−sqrt(17))/4. Reducing to q_3=1 leaves at least one active sure quitter;
each of the three possible active sure choices forces
e≥(1−e)(1−2e)/2. The root
q=(1,1−e*,(1+e*)/2,1) attains equality. The stated scaled perturbation bound
7/128−3/2000>1/20 is correct. Its distance after rescaling is at most
3/1000<1/8, within the explicit solved-parent construction in
[ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO](../exports/ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md).

Thus Π(b)≠0 together with θ(b)>0 does not imply a positive global gap at a
specified table. The manuscript keeps that distinction. The generic
selection does not establish that generic games have equilibria, and does
not construct a descent from the remaining positive-singleton source.

## Archive and regression review

The three-member archive was inspected before execution. The detailed
Markdown member matches the reviewed detailed note. Running the inspected
script in memory with its file-writing main block disabled reproduces every
field of the recorded JSON, including all 24 simultaneous-fixture factors.
No archive member was extracted and no generated JSON was written.

Reproduced counts are 24 factor witnesses, 144 full-debt comparisons, 600
cofactor identities, 576 own-singleton invariance checks, 18 exceptional
ties, and 32 harmonic-ledger checks. The last count is reproducibility
evidence only, outside this review's theorem verdict. Additional independent
exact checks verified all 24 individual witness constants, their zero own
singletons, and their 3/8 reward bound.

No mathematical repair is requested within the reviewed scope. The missing
positive-singleton response producer remains a substantive open obligation;
neither these finite tests nor the discriminant construction supplies it.
