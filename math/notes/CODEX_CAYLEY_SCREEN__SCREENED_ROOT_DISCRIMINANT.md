# Screened-root discriminant and counterexample-preserving fiber selection

Author: CODEX_CAYLEY_SCREEN.

Status: ordinary mathematical independent review, PASS for the screened-root
algebra, strict fiber separation, and conditional generic selection in
[GENERIC_SCREEN](../gpt/GENERIC_SCREEN.md), with the detailed argument in
[GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR](../gpt/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md),
Sections 1–5 and the screened-root fixtures in Section 9. No mathematical
objection remains within this scope. No Lean check or export is claimed.
The singleton-law realization/collar and harmonic inequality are outside this
independent review's mathematical verdict. Their companion regression counts
are reported only as reproducibility evidence.

The corresponding author-facing review is
[GENERIC_SCREEN__BY_CODEX_CAYLEY_SCREEN](../feedback/GENERIC_SCREEN__BY_CODEX_CAYLEY_SCREEN.md).

## Self-contained question and strongest valid statement

There are four players I={0,1,2,3}. Every nonempty coalition S has a reward
vector r(S) in [−1,1]^4; Never and live play pay zero. Players use independent
private randomization and unrestricted behavioral strategies. Before the
first Quit, the public history is only elapsed all-Continue play. Thus an
individual strategy induces a clock in the nonnegative integers together
with Never; unrestricted replacement laws remain available to each deviator.

For an actual profile p, let U_i(p) be expected terminal payoff, B_i(p) its
supremum over every unilateral behavioral replacement, d_i=B_i−U_i, and
E_r(p)=max_i d_i. Put η(r)=inf_p E_r(p). All quantities in this review are
terminal expectations; no finite-horizon inequality is silently substituted.

Split the sixty reward coordinates into the four own singleton entries
s_i=r_i({i}) and the other 56 coordinates b. A screened root is an independent
date-zero product with at least two sure quitters and any continuation.
Its complete payoff/cap pair is continuation independent. Let θ(b) be the
minimum E over such roots, and Ω_b=max_s η(r_b(s)), where s ranges over
[−1,1]^4.

The strongest checked conclusion is the following conditional source
selection theorem, together with an unconditional algebraic construction:

1. There is an explicitly specified nonzero homogeneous integer polynomial
   Π in b of degree 144. If Π(b)≠0, no screened root has four equal strictly
   positive complete debts, for any own-singleton vector s.
2. If Π(b)≠0 and Ω_b>0, then θ(b)>Ω_b. Both extrema in this comparison are
   attained in their respective finite-dimensional compact domains.
3. If a four-player positive-gap table exists, there is rational
   b in (−1,1)^56 with Π(b)≠0 and Ω_b>0. For some rational γ>0,
   E_{r_b(s)}(q)≥Ω_b+γ for every s in [−1,1]^4 and every screened root q.

The maximizing s need not be rational. This selects a hypothetical
counterexample source; it neither constructs a counterexample nor produces
arbitrarily accurate equilibria.

## Independent algebra check

Fix a sure pair K={a,b} and order the two optional players c,d. Give them
date-zero Quit probabilities x,y. After any unilateral replacement, at least
one member of K still quits surely at zero. Consequently every late finite
response and Never has exactly the Continue-at-zero value. This proves the
complete response reduction without restricting the deviation class.

For a sure player, prescribed play uses Quit, and its debt is
max(0, Continue−Quit). For an optional player with Quit probability x and
Quit-minus-Continue gap Δ, its debt is max((1−x)Δ,−xΔ). The analogous formula
holds for y. At a strictly positive four-way tie, the sure players' raw gaps
equal the common debt, and one of the four optional branch choices attains
the two optional debts. Taking all four choices covers signs and endpoints.

Each selected branch is bilinear in x,y. Write its row of coefficients as
ℓ_i against z=(1,x,y,xy). The three differences ℓ_b−ℓ_a, ℓ_c−ℓ_a, ℓ_d−ℓ_a
form a 3-by-4 matrix A. Its entries are integer linear forms in b. No own
singleton occurs: a sure player's Continue singleton, when present, belongs
to the other sure player, and an optional player's endpoint retains K.

Define w_j=(−1)^j det(A with column j removed). Laplace expansion gives
Aw=0. If P=w_0w_3−w_1w_2≠0, some maximal minor is nonzero, rank A=3, and
ker A is the line spanned by w. Equal branch values require Az=0 with z_0=1.
Therefore z=t w for nonzero t, contradicting

    0=z_0z_3−z_1z_2=t²P.

This argument works over the complex numbers and includes x or y equal to
zero or one. A rank below three makes every cofactor and P vanish; no
unsupported conclusion is drawn from that exceptional case.

## Nonvanishing and degree

For one fixed pair and branch labels, independently assign reward coordinates
for the four recipients so that

    F_a=1/4,       F_b=1/2+xy/4,
    F_c=L_c(x)/4,  F_d=L_d(y)/4,
    L_Q(t)=1−t,    L_C(t)=t.

A core recipient's four Continue/Quit pairs are disjoint: a Continue
coalition excludes that recipient and its matching Quit coalition includes
it, while changing the optional set changes both coalitions. None is its
own singleton. A gap g is realized by Continue reward g/2 and Quit reward
−g/2. An optional recipient has two disjoint endpoint pairs, realized using
constant gap +1/4 for Q and −1/4 for C. Different recipients use different
reward coordinates even when the coalition agrees. Hence the assignments
do not conflict. The largest absolute reward is 3/8; own singletons are zero.

Multiplying A by four gives first row (1,0,0,1). Its other rows encode
x=ξ and y=υ, with ξ=0 for Q, ξ=1 for C, and likewise for υ. Its kernel is
spanned by (1,ξ,υ,−1), and its signed cofactor vector is that vector up to
sign. Thus the original P is

    (−1−ξυ)/4^6,

which is −1/2048 for CC and −1/4096 for CQ, QC, QQ. This proves each of
the 24 factors is a nonzero polynomial. The witnesses may differ between
factors; the integral-domain property is sufficient to make their product
nonzero. A single simultaneous witness is additional evidence, not a missing
quantifier in the proof.

Each cofactor is homogeneous cubic in b, so every nonzero P is homogeneous
of degree six. The product over six sure pairs and four optional labels is
nonzero and homogeneous of degree 144. A nonzero real polynomial cannot
vanish on a nonempty open box. Its nonvanishing set is open and dense, and
every nonempty open subset of that set contains a rational point.

## Why the fiber inequality is strict

For fixed b, screened roots form the union of six compact squares and their
full E is continuous. This gives a minimizing screened root. For any fixed
actual profile and complete replacement, changing rewards by at most δ
changes the expected terminal payoff by at most δ. Taking response suprema,
player maxima, and the profile infimum gives

    |E_r(p)−E_{r'}(p)|≤2δ,    |η(r)−η(r')|≤2δ.

The same laws are used at both tables. Response cap attainment is not needed.
This gives continuity and attainment of Ω_b over the singleton cube.

Every screened root is an actual profile, so η(r_b(s))≤θ(b) for every s,
hence Ω_b≤θ(b). If equality held at Ω_b>0, take an s attaining Ω_b and a
screened root attaining θ. That actual root would minimize maximum complete
debt among all actual profiles. By continuity it also minimizes on the
semantic carrier. The inspected all-player-tie theorem then makes all four
debts equal Ω_b, contradicting Π(b)≠0. The theorem used here is explicitly
about MAXIMUM debt; no total-debt minimizer is substituted.

Scale any hypothetical positive-gap table strictly inside the unit cube by
one positive common factor. The gap scales positively. A sufficiently small
perturbation of only b preserves η>0 by the 2δ estimate, while rational
nonvanishing b are dense. Its full fiber has Ω_b>0 and the established strict
comparison supplies rational γ in (0,θ(b)−Ω_b]. This is an existential
perturbation argument, with no retained membership-stretch ancestry.

## Boundary fixtures and the surviving no-go

The archive's equal-positive-debt fixtures use x,y=(1/2,2/3), (1,1/2), and
(1,1), with appropriate optional labels. Every debt is exactly 1/8 and the
selected factor is zero. Every own singleton is zero, so all Never is exact
Nash. The fixtures therefore do not falsify the global-minimum theorem;
they confirm that a positive tie alone is insufficient.

For the raw anchor table in
[ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO](../exports/ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md),
setting q_3=1 cannot increase screened debt. At least one active q_i must be
one. If E≤e<1/2, the three cases give respectively:

- q_0=1: q_1≥1−e, q_2≤(1+e)/2;
- q_1=1: q_2≥1−e, q_0≥(1−e)/2;
- q_2=1: q_0≤e, q_1≥(1−e)/2.

In each case a remaining debt is at least (1−e)(1−2e)/2. Thus
e≥(1−e)(1−2e)/2. Equality is achieved at

    e*=(5−sqrt(17))/4,
    q=(1,1−e*,(1+e*)/2,1).

Hence the stated screened minimum is exact. After scaling by 1/4 and
perturbing by at most 3/4000, screened regret is strictly above
7/128−3/2000>1/20. Rescaling gives distance at most 3/1000<1/8 from the
raw anchor, so the cited explicit parent-equilibrium construction applies.
The archived perturbation has all 24 factors nonzero.

This is a concrete no-go for the implication

    Π(b)≠0 and θ(b)>0  ⇒  η(r)>0.

The strongest surviving conclusion is the conditional comparison θ(b)>Ω_b
when Ω_b>0. The reduction does not solve the remaining singleton-bearing
minimum source.

## Source inventory and reproducible evidence

The bounded route was `docs/TOOLKIT.md`, “Boundary analysis and diagnostics,”
which names the maximum-debt minimum and reward-robustness modules. The
following declarations were read in their source files, including their
imports and the relevant proof bodies:

- `minimumTerminalSemantic_maximumDebt_allPlayersTie`,
  `terminalSemantic_minimum_of_actualMinimum`, and
  `quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum`
  in `UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`.
- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
- `abs_quittingContinuationBestResponseValue_sub_le_of_reward_close`,
  `abs_quittingTerminalExploitability_sub_le_of_reward_close`,
  `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close`, and
  `quittingTerminalExploitabilityInf_scaleQuittingReward` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.
- `quittingTerminalSemanticDebt_nonneg_of_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticDebt.lean`.

The target context in `UniformEquilibrium/Quitting/Conjecture/Basic.lean`
and narrow import/symbol entries in
`UniformEquilibrium/Quitting/Root/TerminalSemanticSoloCapThreshold.lean`,
`UniformEquilibrium/Quitting/Root/FiniteWordSemanticSplice.lean`, and
`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`
were also inspected. The latter theorem's full-pair realization is delegated
to the separate collar review. A narrow cofactor/resultant/screened-root
search in the chosen diagnostic files found no duplicate discriminant
declaration; this is not a global novelty claim. No original-paper result is
being promoted or translated by this review.

The archive was listed and its complete script inspected before execution.
It has exactly the detailed Markdown, the companion Python script, and the
recorded JSON. The Markdown archive member has SHA-256
`07df0dcef1bb37d9c1721a1147981fcbe2069719eff263f608a7534f907752cc`.
The companion was compiled and executed in memory with
`__name__='reviewed_in_memory'`, then `run_checks()` was called. Its file-writing
main block was not invoked and no archive member was extracted. The returned
JSON, after ordinary JSON serialization, agrees with every archived field.

Counts reproduced: 24 factor witnesses, 144 full-debt comparisons, 600
cofactor identities, 576 own-singleton invariance checks, 18 exceptional
ties, and 32 harmonic-ledger interpolation checks. Independent additional
exact checks verified each individual witness's 3/8 reward bound, zero own
singletons, and the four displayed factor constants. These bounded checks
support the universal arguments above; they do not replace them.

No Lean source was changed or built. No export, shared index, or author's
source note was changed.

## Next question

Can the separately reviewed positive prescribed-singleton mass collar supply
an actual unilateral change with strictly smaller maximum complete debt,
while controlling every other player's changed cap? The algebraic exclusion
provides no such response producer.
