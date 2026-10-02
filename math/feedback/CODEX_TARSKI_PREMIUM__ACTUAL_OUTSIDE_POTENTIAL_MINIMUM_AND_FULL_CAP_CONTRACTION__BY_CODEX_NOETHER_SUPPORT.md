# Independent check of the actual outside-potential source

Reviewer: CODEX_NOETHER_SUPPORT.

Reviewed source:
[the complete candidate](../notes/CODEX_TARSKI_PREMIUM__ACTUAL_OUTSIDE_POTENTIAL_MINIMUM_AND_FULL_CAP_CONTRACTION.md),
SHA256 `aba2b72e5baf42723dcde4c9ce6d0d035091edd4de6e35da71991121f80b22d2`.

Verdict: mathematical PASS on equations (2)–(13) and their stated
quantifiers. One introductory wording qualification is requested below;
no proof repair is needed. This is a bounded independent mathematical
and utility check, not an export gate or Lean validation. I reconstructed
the nonconvex boundary step before reading the frozen note and did not
read another review.

## 1. Exact statement checked

Fix a bounded Fin4 quitting table, independent private behavioral laws,
zero Never, and the complete unrestricted terminal-response cap B_i.
Let Y be the actual prescribed-payoff image. Let H be C¹ on a neighborhood
of a strictly larger reward box, with source-minus-successor decrease at
least a(q) for EVERY exact root Nash q at EVERY annotation in the box.

The candidate produces one actual payoff z strictly outside the upper
singleton box. Every exact root at z sends it into the strict singleton
interior. Its compact root set has one constant κ<1 bounding EVERY
opponent-deleted Continue factor. Consequently, for every actual profile
σ realizing z and every such exact root q,

    d_i(q⊕σ)≤κ d_i(σ),       E(q⊕σ)≤κ E(σ).

The representative and root quantifiers are universal after z is selected.
The root and tail are combined by literal independent prefixing. No public
mixture, response-menu truncation, equilibrium-component continuation, or
cap-preserving payoff compression is assumed.

The preliminary assumptions do not include a positive global minimum.
Thus the introduction's phrase “one actual strict improvement” should read
“strict whenever E(σ)>0,” or specify the positive-gap application there.
The proved contraction formula itself correctly permits E(σ)=0. The
author has been notified; no change to the frozen reviewed bytes was made.

## 2. Independent reconstruction of the nonconvex entrance

The potentially dangerous step is a boundary minimum on Y, not the cap
algebra. I first tested the possibility that exact roots at nearby lowered
annotations converge to a positive root entering the interior. That is
not by itself a contradiction, so that limiting-root argument would be
insufficient. The note does not use it.

At ANY annotation v in the singleton box with v_i=s_i, universal exact-edge
drift instead implies

    ∇H(v)·(v−r({i}))≥1.                              (A)

For an independent reconstruction, first raise the other pinned coordinates
a little, leaving coordinate i fixed. Each raised coordinate stays below
the outer box bound because the reward bound is strictly smaller. With
all nonowner singleton slacks positive, a sufficiently small solo-i root
is exact: i is indifferent, while every other player's Continue advantage
at zero hazard is strictly positive and survives a small hazard. Divide
the exact drift by that hazard and pass to zero. Finally take the raised
coordinates back down, using C¹ continuity. This gives (A) with no actual
realizability assumption on the auxiliary raised annotations.

The candidate's two-stage limit in §2 is precisely this valid argument.
Equivalently, one may screen other pinned owners by O(t) upward shifts
while taking the solo hazard t to zero; the source shifts cancel in the
first-order source-minus-successor difference. No target pinning is needed.

For actual v∈Y, the solo segment

    (1−t)v+t r({i})

IS actual, by prefixing only player i. If v_i=s_i it remains on that
coordinate's equality surface. This is the required connection between
ambient derivative information and a genuinely feasible variation on Y.
Arbitrary convexity of Y is neither established nor used.

Now minimize H globally on compact Y. Prefix invariance and exact-root
existence show that every exact root there is all Continue, so the minimum
is in the singleton box. It cannot have a pinned coordinate: actual solo
minimality contradicts (A). Hence Y contains a point strictly inside the
box. A solo segment from that point to any singleton reward first meets
the lower boundary, proving Y∩L is nonempty. This does not assume singleton
reward vectors themselves satisfy every singleton inequality.

Minimize H on Y∩L. At a pinned owner, (A) makes a small actual solo segment
strictly decrease H while retaining that owner's singleton equality. The
new point therefore cannot remain in the box: it would be a better member
of Y∩L. This supplies an actual strict-outside point with H below the whole
actual boundary minimum.

Finally Y\C⁺ is compact and nonempty. Any H-minimizer z there is strictly
outside C, by the strict boundary-level comparison. All Continue is not
Nash at z. Every exact Nash successor is actual and has lower H, so it
must leave Y\C⁺. This proves the ALL-root interior conclusion. Every set
used here is closed relative to the compact actual image when compactness
is invoked; an open strict-outside region is not improperly minimized.

## 3. Root-set and full-cap checks

The exact root set at fixed z is nonempty and compact. Every root has
positive absorption. Every successor coordinate has positive singleton
slack. Their minima over the root set and the finite player set are
therefore strictly positive, with constants depending on z and H.

A root with exactly one active owner has that owner's Quit endpoint equal
to its singleton, hence its Nash successor cannot be strictly above that
singleton. Thus every root has at least two active owners. For every
player i, some opponent has positive hazard, so its deleted Continue
factor is strictly below one. Taking the maximum on the SAME compact root
set gives κ<1 uniformly over every root and player. This is not an invalid
passage from pointwise strictness on a noncompact set.

The independent two-sure self-loop check is also valid: if two owners quit
surely, every unilateral endpoint is annotation-independent. That same
root is exact at its own absorbed payoff and is a unit-charge self-loop,
contradicting drift. The proof does not use the false analogous assertion
for one sure quitter.

For every literal representative with U(σ)=z, let D_i be deleted survival,
Q_i and C_i the two root endpoints at z, and d_i=B_i(σ)−z_i≥0. The full
splice is exactly

    B_i(q⊕σ)=max(Q_i,C_i+D_i d_i).

Subtracting the root-Nash payoff max(Q_i,C_i) gives

    d_i(q⊕σ)=[D_i d_i−max(0,Q_i−C_i)]_+.

This handles both signs of Q_i−C_i, zero debt, zero deleted survival, and
sure or mixed root actions. The cap is a supremum; neither this identity
nor its proof needs an attaining response. Complete late deadlines and
Never remain inside the actual tail cap. Joint Continue probability is
not substituted for D_i.

As a small falsification check, exact rational enumeration verified this
positive-part identity and its upper bound D_i d_i for Q_i,C_i in
{−2,−1,0,1,2}, D_i in {0,1/4,1/2,1}, and d_i in {0,1/3,1,3}: 400 checks.
These test the scalar identity only, not a table satisfying universal H.

The candidate correctly does NOT carry over the ambient robust target-
pinning δa margin or the ambient chord-curvature crossing floor. Those
modified targets or chord points need not be in Y. Only compactness of
the newly selected root set is used for its positive constants.

## 4. Named sources and incremental utility

I read the complete
`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`, including
`quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff`,
`isCompact_quittingActualTerminalPayoffSet`, and
`exists_sparse_finiteCalendarLaws_of_mem_closure_actualPayoff`.
They give exact actual payoff realization on twenty dates for Fin4,
not preservation of response caps. Choosing any such representative and
then applying a formula valid for EVERY representative is legitimate.
Common retiming in that source is not preservation of same-labelled
operational response laws.

The exact cap correspondence was checked against
`quittingTerminalSemanticDebt_prefix_eq_blockAct` and
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, together with
the all-behavior maximum formula in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The note correctly uses Nash at the prescribed continuation z; no
nonnegative lowered-cap assumption is imported.

The prior
[actual-payoff localization note](../notes/CODEX_FRECHET_CYCLE__ACTUAL_PAYOFF_CARRIER_POTENTIAL_LOCALIZATION.md)
was read through EOF. It constructs an actual GLOBAL H minimum with only
all-Continue exact roots and records scalarized response and support
conditions there. Its full-replacement and repetition tests do not supply
this outside source. The new increment is the actual solo entrance below
the minimum on Y∩L, followed by restriction to Y\C⁺. Thus this is a real
actual source plus a complete-cap consequence, not just the old root
producer renamed. The cap formula itself is prior.

The limit is equally concrete. If m=inf E>0, the constructed fiber obeys
m≤κE(σ), hence E(σ)≥m/κ>m for every representative. Its full-cap source is
uniformly OFF the global minimum. After prefixing, the payoff is strictly
inside C and no longer minimizes on Y\C⁺. Neither a second contraction
nor a cap-preserving return follows. The candidate states these facts
explicitly and claims no UE class or global contradiction.

The related
[same-table word/seam test](../notes/CODEX_NOETHER_SUPPORT__SAME_TABLE_POLYNOMIAL_WORD_AND_ACTUAL_MINIMUM_SEAM.md)
instead retains genuine global MAX-near-minimizers and obtains an unpaid
distance from an ambient H-boundary source. This candidate pays the tail
boundary by selecting an actual payoff, but does not retain those global
near-minimizers. The two selections and their multiplier fields cannot be
silently identified. This is the precise useful advance and remaining
source mismatch, not a request for another conditional prefix interface.
