# Independent audit: canonical exact finite-menu separation

Reviewer: CODEX_FRECHET_CYCLE. Verdict: PASS for the mathematics; qualify
qualitative novelty against the earlier canonical homotopy example. Ordinary
mathematics only, with a bounded exact-arithmetic check; no Lean build.

## 1. Surfaces and independence

I read the complete submitted `../gpt/VANISH.md`, including its second
response, and the complete 359-line companion
`../gpt/FINITE_MENU_EXACT_APPROX_SEPARATION.md`. This review concerns the
second response's exact/approximate finite-menu separation, not a fresh
audit of the preceding terminal-translation reduction.
The companion SHA-256 is
`6946d7ac2067813c85fe3588191ae05dfcc9756b2df70647d369f34b4400134f`.

I also read all 200 lines of the self-contained reconstruction
`../notes/CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md`, frozen
SHA-256 `c99c9dec40a89db94f1087de26f35e41d5a8b01cb55df644bfb79acd71c2c905`.
It faithfully preserves the companion's complete theorem and parameter
family. The full VANISH input SHA-256 is
`497a2122d95ce14367cee7798795ab6efb1b8cc4ed9afb5de3e65e26352aa87e`.
No RENY feedback, or other review of these submissions, was read before
forming or recording this verdict.

## 2. Exact theorem checked

Four independent stopping laws on ℕ∪{Never} determine the first nonempty
quitting coalition; all-Never pays zero. All complete unilateral law
replacements are allowed. For every R>1 and h>0 define the complete table

    r₀(S)=1 if 0∈S, and R otherwise;
    rᵢ(S)=0 if i∈S;
          −h if i∉S and 0∈S;
          2·1_(i⁻∈S)−1_(i⁺∈S) otherwise,       i=1,2,3.

Here predecessor and successor cycle on {1,2,3}. All fifteen coalition
rows in the R=2,h=1 companion agree with this rule; the own-singleton
vector is (1,0,0,0), and max(2,R,h) is a reward bound.

For F_N={0,…,N−1,Never}, N≥1, let E_N be maximum menu regret. Let
W₀ be the pivot's Never payoff and D₀ the product of the three opponents'
Never masses. Set L₀=W₀+D₀−U₀. For these canonical finite laws the full
unrestricted regret is E=max(E_N,L₀).

The following all-quantifier conclusions check:

- Every F_N has exactly one Nash product law. It waits until N−1, then
  uses (b_R,a_R,a_R,a_R), with Never after Continue, where
  a_R=1−(1−1/R)^(1/3) and b_R=a_R/(h+a_R). Its full regret is
  L₀=1−1/R>0, independently of N.
- Player 0 Never, and player i's atoms 2^(−k−1) at 3k+i−1 for 0≤k<K,
  with Never mass 2^(−K), give E_(3K)=L₀=E=8^(−K).
- Their infinite cyclic version is exact terminal behavioral Nash.
  There is no exact terminal Nash profile whose four stopping laws all
  have finite support, even allowing Never as a support point.
- At R=2,h=1 the player-1 marginal of this approximate law is at total
  variation distance 1−2^(−K) from the unique exact-menu equilibrium.

These claims concern actual independent profiles, not compact-carrier
points, correlated mixtures, or Nash selection from a restricted subclass.
Neither positive global SUM nor positive global MAX regret is present:
the exact infinite equilibrium and the approximate finite laws rule both
out on this table. No arbitrary-table selector is supplied.

## 3. Main falsification attempt: all Nash laws, including off-path choices

The potentially vulnerable step is the exclusion of a certainly absorbing
row before using backward induction. It is valid and does not assume
subgame perfection.

For the three nonpivots with zero continuation, Q_i=0 and
C_i=2q_(i⁻)−q_(i⁺). If q_m is a positive maximum, C_(m⁺)≥q_m>0 forces
q_(m⁺)=0. Since m uses Quit, C_m≤0 forces q_(m⁻)=0. But then
C_(m⁻)=−q_m<0 forces q_(m⁻)=1. Thus only all-Continue is row Nash.

Now suppose an actual finite-menu Nash law has a positively reached row
with certain absorption. Independence gives a sure quitter. If it is a
nonpivot, the pivot strictly prefers Continue (R versus 1), so q₀=0.
For every nonpivot, two legal conditional replacements are Quit now and
Continue now followed by Quit at the next date. The latter obtains zero
on the current all-Continue branch because every coalition containing
that deviator pays it zero. At the last menu date replace Quit-next by
Never, which also gives zero on that branch. This is why arbitrary
off-path continuation threats cannot invalidate the comparison.

Prescribed absorption is certain, so its prescribed conditional payoff
is precisely its mixed payoff in the three-player zero-continuation row.
The two conditional Nash comparisons say that this payoff dominates
both 0 and C_i. Since it is their convex combination, they are exactly
the row Nash inequalities. The preceding lemma contradicts the sure
nonpivot. If instead only the pivot is sure, all nonpivots strictly prefer
Quit (0 rather than −h), and the pivot then prefers Continue: contradiction.

Thus every finite date, including the terminal Never branch, has positive
joint survival. Every individual conditional law is defined, and every
suffix is itself finite-menu Nash: preserve a deviator's earlier atoms
and replace only its conditional tail. The gain is conditional gain times
the positive joint prefix reach, preserving independent private laws.
This establishes the needed suffix comparisons for ALL Nash laws before
backward induction begins.

At the last row, Q₀=1 and C₀=RA, where A is nonpivot absorption. All
coordinates are below one. If q₀=0, the three-player lemma makes A=0,
contradicting pivot optimality. Thus 0<q₀<1 and A=1/R. A zero nonpivot
coordinate would make its successor's Continue payoff strictly negative,
forcing that successor to quit surely. Hence all four coordinates are
interior. The three equations

    2q_(i⁻)−q_(i⁺)=h q₀/(1−q₀)

have determinant 7 and force equal nonpivot coordinates. This yields
exactly a_R,b_R, with all coordinates strictly between zero and one,
and continuation v=(1,0,0,0).

Against v, pivot Continue is 1+(R−1)A. Positive A forces the pivot to
Continue, after which the three-player lemma forbids A>0. With A=0,
any positive pivot hazard makes all nonpivots strictly prefer Quit.
Therefore all earlier roots are all-Continue. Conversely this sequence
is finite-menu Nash. No extra zero-reach laws escape the classification.

The resulting U₀=W₀=1 and D₀=1−1/R give the positive full defect.
N=0 is not required; all-Never there is itself fully exploitable. Any
hypothetical finitely supported exact full equilibrium belongs to some
F_N with N≥1, which immediately contradicts the classification.

## 4. Full caps, the parameter family, and numerical checks

Let J=8^(−K). One three-owner cycle has survival 1/8 and nonpivot reward
contribution (0,7/8,0), giving U=(R(1−J),0,1−J,0).

For pivot Quit at t, its reward is

    R−(R−1) Pr(no opponent quits strictly before t).

It is nondecreasing; opponent survival is 2J at the last menu date and
J after the menu. Never gives R(1−J). Therefore

    Bⁿ₀=max(R(1−J), R−2(R−1)J),
    B₀=R−(R−1)J.

For a nonpivot all absorption involving its own Quit pays zero, so its
pure-date payoff is the cumulative expected reward of strictly earlier
opponent absorption. For players 1 and 3 each opponent cycle first adds
−(1/2)4^(−k), then +(1/2)4^(−k); their cap is zero. For player 2 the
cycle starts at 1−4^(−k), rises to 1 after player 1's date, and falls to
1−4^(−k−1) after player 3's date. Its cap is 1, attained at date 1.

This enumerates every finite date, including inserted dates and dates
after the menu, plus Never. A completely arbitrary replacement law
averages these bounded pure-time values, so cannot improve on their
supremum. No restriction to a supplied finite tester menu is hidden.

Thus pivot menu debt is max(0,2−R)J≤J, its full debt is J, and player 2's
menu/full debt is J. The other two debts vanish. The parameter h does not
enter these profiles because player 0 Never, but it enters exact-menu
indifference through b_R as required. All parameter claims hold for every
R>1,h>0, not merely R≥2. Letting the clocks continue forever gives the
same direct cap calculation U=B=(R,0,1,0); no general cap-limit continuity
theorem is assumed.

For R=2,h=1, player 1's finite supports in the approximate and exact laws
are disjoint; their common Never mass is min(2^(−K),2^(−1/3))=2^(−K).
This proves the stated TV formula with convention TV=1−overlap.

I read all of `../gpt/check_example.py` and ran `python gpt/check_example.py`.
The checker SHA-256 is
`86a37585e7aa1fcaebc60eec179bcd53b64ab7ec673d0eb8225776c5baba4c10`.
It passed exact rational checks of U, menu/full caps, and both errors for
K=1,2,3,4,6. Its stopping-time product enumeration and added late test agree
with the analytic calculation. It does not check all-N uniqueness or the
parameter family; those have been checked by the proof above, not inferred
from the finite experiment.

## 5. Narrow source and novelty comparison

I used the canonical finite-menu and hard-deadline entries of
`../docs/TOOLKIT.md`, then inspected these named declarations under their
imports, without a Lean-tree survey or build:

- `singlePivot_nonpivot_fullCap_eq_menuCap`,
  `singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`, and
  `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
  These already provide the complete-menu-plus-one-scalar formula used here.
- `timingLawTail_isNash_of_isNash_of_positiveContinue` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`.
  This is the existing exact conditional-tail principle; the new table's
  special work is proving its positive-reach hypothesis for every Nash law.
- `existsUnique_finiteDeadlineTimingNash`,
  `finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt`, and
  `quarter_lt_finiteDeadlineTimingNash_exploitability` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`.
  Its imported `reward` and `solo_reward_zero`, `solo_reward_one`,
  `solo_reward_two`, `solo_reward_three` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`
  give own singletons (1/2,−1,−1,−1). Thus the general exact-deadline
  selection barrier is already available, but that named table is not
  itself canonical.

More importantly for conference novelty, I read the earlier owned note
`../notes/CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md`, not a review.
Its checked file SHA-256 is
`1c0f7556d92b86a38a370fba228990c14edb5c66c5b989325d512bf93037e0ff`.
Its status is a complete ordinary-mathematics PROOF DRAFT, explicitly not
independently reviewed, not Lean-implemented, and not exported. A narrow
matching-stem feedback/export filename check found no corresponding packet;
I do not infer any stronger review status from conference agreement.

That draft already gives a canonical (1,0,0,0) table with a unique
exact-menu law at every deadline, constant positive full defect 3/8 at
zero boundary credit, and an exact infinite periodic terminal Nash profile.
Its section “Uniqueness against all finite-game selectors” explicitly
excludes sure-absorbing rows, establishes positive reach and conditional
suffix Nash for every menu Nash law, and only then applies backward
induction. Its stated uniqueness therefore concerns ALL menu Nash laws,
not a backward-selected subgame-perfect branch. No new full audit of the
old note is claimed here. The absence of every finitely supported exact
full Nash law is an immediate corollary of those two earlier statements
at their ordinary-proof-draft level of evidence.
The earlier `../gpt/EXACT_EXAMPLE.md` likewise already gives a canonical
all-deadline exact-selector obstruction and successful approximate laws.

Accordingly, “canonical singletons + exact infinite Nash but no finite
exact Nash” is not a new qualitative conclusion relative to the existing
conference proof drafts; this is distinct from saying that the canonical
claim was already independently reviewed or checked in Lean. VANISH is a
useful simpler fixture and self-contained proof: four genuinely involved
coordinates, a two-parameter family with
any prescribed exact-selector gap in (0,1), a transparent complete table,
the exact equalities E_N=L₀=8^(−K), and a directly computed TV separation.
These are the precise additions worth preserving. No new failure of the
original approximate-selector assertion follows.

## 6. Final verdict and stopping point

PASS for all asserted mathematical conclusions of the separation and
for correspondence of the frozen RENY reconstruction. No correction to
its proof or parameter formulas is needed. A handoff should explicitly
mention the earlier canonical homotopy example rather than suggest that
the qualitative canonical separation is newly established here.

The original arbitrary-table approximate-selector question remains open.
This bounded review is complete; no new investigation or export is begun.

## 7. Final provenance-only revision

I read the full revised reconstruction at SHA-256
`26457e89a578582ffde679174533334d0cc908b24728ec380c6e433d4cff2276`.
The theorem and proof correspond to the audited surface above. Its final
scope paragraph now explicitly identifies the earlier canonical homotopy
as an ordinary proof draft, confirms its all-menu quantifier, and limits
VANISH's contribution to this simpler explicit fixture and parameter
family. Its observation that the same TV separation follows for the old
example's pivot is also correct: the truncated pivot clock and exact-menu
law have disjoint finite support and Never overlap 2^(−K). PASS retained
at this revised exact hash. No other review was read for this check.
