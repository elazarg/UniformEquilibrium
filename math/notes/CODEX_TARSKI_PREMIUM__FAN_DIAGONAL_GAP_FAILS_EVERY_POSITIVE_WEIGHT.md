# The native Fan diagonal-gap test fails every positive weight

Author: CODEX_TARSKI_PREMIUM.

Status: completed bounded test, STOPPED. Ordinary mathematics, not
Lean-checked or independently reviewed. The compact mixed-clock space has
the right convexity and diagonal-cover property for the Fan–KKM argument,
but its ORIGINAL weighted Nash-gap sublevels need not be closed. The same
fixed tester defeats EVERY positive player-weight vector on both requested
canonical calibrations. Under hypothetical canonical no UE, the existing
actual-payoff-exclusion contrapositive already forces this failure. Hence
this is a theorem-application stop, not a new counterexample restriction,
UE class, or conditional selector interface.

## 1. The one theorem and the literal strategy domain

Primary source: Ky Fan, *A Generalization of Tychonoff's Fixed Point
Theorem*, Mathematische Annalen 142 (1961), 305–310, **Lemma 1**, with
its complete proof at pp. 305–306. The original English scans were read
through the [Göttingen volume](https://gdz.sub.uni-goettingen.de/id/PPN235181684_0142),
images 309–310, not through a later minimax theorem's attribution.
The [DOI](https://doi.org/10.1007/BF01353421) identifies the original paper.
Only this lemma is used; no claim is made to have read Fan's 1972 paper.

In the needed form, Fan's lemma says: for a subset X of a Hausdorff
topological vector space, closed sets K(q) indexed by q∈X have nonempty
intersection if one K(q) is compact and every finite convex hull of
indices lies in the union of the corresponding K(q). No convexity of
the sets K(q) is required. The lemma follows by pulling the finite
family back to a Euclidean simplex, applying finite KKM, and then using
compactness for the finite-intersection property.

Here players are I={0,1,2,3}. Fix a bounded real terminal table r(S),
∅≠S⊆I. Live and Never reward are zero. Set

    D=ℕ∪{∞},       X_i=Prob(D),       X=∏_i X_i.

D has its one-point compactification topology; X_i has the weak topology.
X is compact, convex, and Hausdorff in the product of the weak-star
spaces of signed measures. A point p is a tuple of INDEPENDENT marginal
clocks. Convex combination in X is coordinatewise mixing of marginals,
not a correlated mixture of complete product profiles. The terminal
coalition consists of every player at the first finite clock minimum;
all infinite clocks give payoff zero.

Every marginal law is realized by its conditional stopping hazards.
Conversely, before absorption the only public history is unanimous
Continue, so every complete behavioral replacement has such a law.
Thus the response quantifiers below include all finite deadlines,
unbounded random clocks, and exact Never, not just finite-menu replies.

## 2. What the diagonal argument would actually require

Fix w_i>0, without normalization. For actual p,q∈X define

    F_w(p,q)=Σ_i w_i [U_i(q_i,p_−i)−U_i(p)],
    K_w(q)={p∈X:F_w(p,q)≤0}.

For fixed p, F_w(p,·) is affine in the joint tuple q. Also F_w(p,p)=0.
Consequently the KKM cover condition is automatic: if
p=Σ_a α_a q^a and every F_w(p,q^a)>0, affinity would give
0=F_w(p,p)=Σ_a α_a F_w(p,q^a)>0. The same argument applies after
discarding indices of weight zero.

If every K_w(q) were closed in X, it would be closed in the ambient
Hausdorff vector space as well, because X is compact and hence closed.
Each would then be compact. Fan's lemma would supply p in their common
intersection. That conclusion is EXACT original terminal Nash: to test
player i, take q_j=p_j for j≠i and vary q_i alone. Conversely, at Nash
each summand is nonpositive. This is stronger than merely an approximate
finite-law output, but the falsification below concerns a concrete
hypothesis, not an assumption that exact Nash must exist.

Writing B_i(p)=sup_τ U_i(τ_i,p_−i) and d_i=B_i−U_i≥0 gives

    sup_q F_w(p,q)=Σ_i w_i d_i(p).

The suprema separate because the four q_i may be chosen independently;
arbitrarily accurate cap responses suffice, with no attainment assumed.
Only the ZERO levels of this weighted sum and max_i d_i agree. Their
positive minima are not identified. No global regret minimizer is used.

The usual lower-semicontinuity condition on F_w(·,q) would imply the
needed closedness. We show failure of CLOSEDNESS ITSELF.

## 3. Exact boundary computation with a fixed full tester

Assume the canonical own-singleton vector s=(1,0,0,0). Let p∞ be all
Never and fix q⁰_i=Quit0 for all i. This q⁰ is a tuple of four separate
unilateral tests, not the payoff of a simultaneous four-player deviation.

For any actual profile p, shift every finite clock forward by n≥1,
retaining every Never atom. Call the resulting independent profile p[n].
Then p[n]→p∞ weakly, while the prescribed terminal coalition law and
Never probability are unchanged. A deviation Quit0 now occurs strictly
before every finite opponent clock. Therefore, EXACTLY for every n≥1,

    F_w(p[n],q⁰)=w₀−w·U(p),       F_w(p∞,q⁰)=w₀>0.       (1)

In particular, w·U(p)≥w₀ implies that p[n] belongs to K_w(q⁰), but
its limit does not. If w·U(p)>w₀, even strict negative values converge
to the positive value w₀. This proves the claimed failures of closedness
and lower semicontinuity. No cap continuity or payoff-fiber compression
is invoked; (1) uses actual laws and the same prescribed payoff.

## 4. Easy canonical calibration: VANISH

Use the known cyclic canonical table. For nonempty S, let

    r₀(S)=1 if 0∈S, and 2 otherwise.

On the cyclic order 1→2→3→1, for each nonpivot i put

    r_i(S)=0                                      if i∈S;
           −1                                     if i∉S and 0∈S;
           2·1_{pred(i)∈S}−1_{succ(i)∈S}           otherwise.

Never remains zero. Its three nonpivot singleton vectors are

    r({1})=(2,0,2,−1),
    r({2})=(2,−1,0,2),
    r({3})=(2,2,−1,0).

Their sum is (6,1,1,1). For EVERY w_i>0 there is a nonpivot j with

    w·r({j}) ≥ 2w₀+(w₁+w₂+w₃)/3 > w₀.              (2)

Choose p as sure singleton j at date zero and shift it in (1).
This is already enough to defeat Fan closedness for every positive
weight. The game itself is solved, including the actual asymmetric
finite-law construction in the [private-date checkpoint](../notes/CODEX_TARSKI_PREMIUM__PRIVATE_FINAL_DATE_EXACT_NASH_AND_ORIGINAL_ERROR.md).
Its existence is also covered by the valid normalization of the existing
capped-member consumer, as recorded in the [scope correction](../notes/CODEX_TARSKI_PREMIUM__ROTATING_PRIVATE_MENU_SCOPE_AND_NORMALIZED_CAPPED_EXIT.md).
No selected finite-Nash target is required here.

## 5. Paired degree-one calibration, with ACTUAL normalization

Take c=2 in the [paired collision-reward family](../exports/PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md).
Normalize at pivot 0 by subtracting one from EVERY absorbing reward
coordinate of players 1,2,3, leaving player 0 unchanged and Never zero.
This is the literal `quittingSinglePivotNormalizedReward`, not merely a
relabeling of its singleton matrix. For completeness the resulting table is:

| S | r(S) |
| --- | --- |
| 0 | (1,3,−1,−1) |
| 1 | (4,0,−1,−1) |
| 2 | (0,−1,0,3) |
| 3 | (0,−1,3,0) |
| 01 | (2,1,0,0) |
| 02 | (2,0,1,−1) |
| 03 | (2,−1,0,1) |
| 12 | (0,1,1,0) |
| 13 | (1,1,−1,1) |
| 23 | (1,0,1,1) |
| 012 | (1,−1,−1,−1) |
| 013 | (0,0,−1,−1) |
| 023 | (0,−1,−1,0) |
| 123 | (0,−1,0,−1) |
| 0123 | (−1,−2,−2,−2) |

Its FOUR singleton vectors sum to (5,1,1,1). Thus for every positive w,
some singleton j satisfies

    w·r({j}) ≥ (5w₀+w₁+w₂+w₃)/4 > w₀.              (3)

The same fixed tester and literal singleton shift give nonclosedness.
Only summing the three nonpivot rows would not prove (3); the pivot
singleton is legitimately available in this test.

This is not another successful test confined to capped/Q-bar/exclusion
data. The singleton matrix has a two-player principal with both off-diagonal
entries −1, so fails projective Q-bar; pair members receive 2 above their
original singleton 1, so the direct capped hypothesis fails. The actual
periodic profile in the cited family has all original payoffs strictly
above 1, so its normalized payoffs strictly dominate (1,0,0,0), defeating
every nonempty weak-subset payoff exclusion. Nevertheless the table has
UE by that explicit periodic–stationary disjunction and the checked
forward normalization consumer. No unknown nonexistence or new class is
inferred from this solved regression.

## 6. The genuine no-UE source gives failure, not the missing hypothesis

On a hypothetical canonical Fin4 table with no uniform-equilibrium
payoff, apply the contrapositive of
`exists_uniformEquilibriumPayoff_of_finFour_signFreeWeakSubsetExclusion`
with designated set all four players. It supplies one ACTUAL profile p
with U_i(p)>s_i for every i. For every w_i>0, this same p has
w·U(p)>w·s=w₀. Equation (1) then violates Fan closedness for every w.

This uses a current named theorem, not an additional strategic witness
assumed by the candidate operation. It proves that the no-UE restrictions
do not repair this exact Fan hypothesis. It does NOT contradict no UE,
because failure of a sufficient equilibrium theorem is consistent with
that hypothesis. It adds no counterexample restriction beyond the
already available payoff-exclusion contrapositive.

## 7. Known/new split and stop

Read narrowly: `arch/SUFFICIENT_STATE.md`,
`arch/CONTROLLER_VS_TESTER.md`, and
`arch/STATE_TOPOLOGIES_AND_APPROXIMATION.md`, plus the existing
[Reny infinity-fiber test](../notes/CODEX_TARSKI_PREMIUM__RENY_SECURITY_AT_THE_INFINITY_PAYOFF_FIBER.md).
These already explain delayed payoff graphs and the compact-weak versus
operational-total-variation distinction. No exact weighted Fan gap or
all-positive-weight zero-sublevel test was found in the narrow search.
The incremental calculation is (1)–(3), not a new topology obstruction.

Source files inspected for this test:

- `Quitting/Paths/CounterfactualStoppingLaw.lean` and its imported
  `BehaviorStoppingPayoff.lean`: independent first-stopping outcome laws
  and the original behavioral/stopping-law semantics.
- `Quitting/Root/SinglePivotNormalization.lean`:
  `quittingSinglePivotNormalizedReward` and
  `quittingSoloReward_singlePivotNormalized`.
- `Diagnostics/Quitting/FinFourSignFreeWeakSubsetUniformPayoff.lean`:
  `exists_uniformEquilibriumPayoff_of_finFour_signFreeWeakSubsetExclusion`,
  whose literal hypothesis quantifies over actual behavioral profiles.

All three paths above are below `UniformEquilibrium/` in the repository.
The checked controller/tester compact carrier is not X with this topology:
its prefix-operational barrier does not establish the closed sets needed
here. Switching X to total variation restores static payoff stability but
loses compactness already on the sequence of pure clocks δ_n. No new
topology, correlation, sharing rule at infinity, or abstract closedness
assumption is introduced to rescue this test.

The chosen Fan–KKM operation is stopped at its failed hypothesis. No
further theorem application or conditional compiler is proposed here.
