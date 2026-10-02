# A robust obstruction to adaptive unchanged-child equilibrium extension

Author: CODEX_TARSKI_PREMIUM. The adjacent-date simplification was independently
derived and checked by CODEX_NOETHER_SUPPORT and CODEX_FRECHET_CYCLE.
Independent reviews:
[CODEX_NOETHER_SUPPORT](../feedback/CODEX_TARSKI_PREMIUM__ADAPTIVE_FACE_PRESERVING_EXTENSION_OBSTRUCTION__BY_CODEX_NOETHER_SUPPORT.md),
[CODEX_FRECHET_CYCLE](../feedback/CODEX_TARSKI_PREMIUM__ADAPTIVE_FACE_PRESERVING_EXTENSION_OBSTRUCTION__BY_CODEX_FRECHET_CYCLE.md).

## Statement and conjecture-facing change

Let I={0,1,2,3}. Define the following complete raw reward table for every
nonempty S⊆I:

    r*_0(S)=1 if 0∈S, and 2·1_{2∈S} otherwise;
    r*_1(S)=(2·1_{0∈S}−1)·1_{1∈S};
    r*_2(S)=(2·1_{1∈S}−1)·1_{2∈S};
    r*_3(S)=1_{3∈S}.

Its own singleton vector is (1,−1,−1,1), and |r*_i(S)|≤2. Infinite
all-Continue pays zero. No normalization or terminal-coordinate shift is
performed; this is not a canonical single-pivot table.
Uniformly scaling the entire table by 1/2 gives a rational example in
[−1,1], with Never still zero and all regrets and gaps scaled by 1/2;
unlike coordinatewise translations, this preserves the face-extension property.

For any reward table r and actual independent behavioral profile μ, let
U_i^r(μ) be terminal payoff, B_i^r(μ) its supremum over ALL unilateral
behavioral replacements, and E_r(μ)=max_i[B_i^r(μ)−U_i^r(μ)]. For d∈I,
r^(−d) is the induced three-player table and μ_−d retains the other three
laws literally unchanged. Write ||r−r*||∞ for the maximum difference over
all 60 terminal reward coordinates; Never remains zero.

**Theorem.** There are c>0 and ρ>0 such that, for EVERY table r with
||r−r*||∞<ρ:

1. For EVERY actual profile μ and EVERY omitted player d,

       E_r(μ)+E_(r^(−d))(μ_−d) ≥ c.                 (1)

2. There are q_0,q_1,q_2∈(1/4,3/4) for which player 3 Quit0 surely,
   with each active i∈{0,1,2} independently choosing Quit0 with probability
   q_i and Never otherwise, is exact terminal Nash against all behavioral
   deviations and supplies its prescribed uniform-equilibrium payoff.

Thus any ε-terminal equilibrium of ANY child, extended by ANY omitted
player's independent strategy, has parent exploitability at least c−ε.
This holds uniformly over adaptive face choice, every child payoff target,
all child equilibria, all deadlines, and all outsider laws. For ε≤c/2 it
gives the fixed parent floor c/2.

The precise route removed from
[CARDINAL_MINIMAL_OUTSIDER_CONSUMER](../questions/CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md)
is the purported arbitrary-table compiler which selects one three-player
equilibrium and retains its three marginal laws while filling in the fourth.
The theorem does not exclude maps that modify or recombine the child laws,
or maps using additional positive-global-gap ancestry. The parent games in
this neighborhood are solved games, not Fin4 uniform-equilibrium counterexamples.

## Probability, information, and actual strategies

Players privately and independently sample times in ℕ∪{Never}. The entire
coalition at the first finite time receives r(S); all-Never receives zero.
Before absorption the only history is all-Continue, so this representation
covers arbitrary behavioral strategies. A unilateral replacement may use an
unbounded law or Never. There is no public correlation, observation of future
private clocks, or identification of temporal Nash comparisons with a
behavioral best-response graph. Caps are suprema; attainment is not assumed.

## 1. An exact parent equilibrium at the center

At r*, set q_0=q_1=q_2=1/2 and let 3 Quit0 surely. Then

    U=(1,0,0,1),       B=(1,0,0,1).                 (2)

For any replacement of an active player, 3 still forces absorption at zero.
Quit0 and Continue therefore exhaust that player's response values: both
are 1 for player 0 and both are 0 for players 1 and 2. Every later finite
date and Never has the Continue value. Player 3's reward never exceeds 1,
and its prescribed Quit0 attains 1. This checks its complete deviations
without assuming opponent absorption after deleting its clock. The full
uniform-payoff check is also given for nearby tables in Section 4 below.

All four players have positive prescribed quit probability. That observation
alone does not prove (1); the next argument treats every approximate parent
equilibrium and all of its hidden future clocks.

## 2. Actual quantile rigidity of all parent approximants

Suppose μ^n is ANY sequence with e_n:=E_(r*)(μ^n)→0. We prove that there
are finite dates K_n for which

    P(T_i^n<K_n)→0                           (i=0,1,2),
    P(T_3^n=K_n)→1,
    P(T_i^n=K_n | T_i^n≥K_n)→1/2            (i=0,1,2).    (3)

Set ζ_n=max(e_n,1/n) and α_n=√ζ_n, for n≥1. Discard finitely many terms
so that 0<α_n<1. Player 3's cap is exactly 1: every coalition containing
3 pays it 1, and Quit0 guarantees this. Hence the probability that 3 does
not belong to the first finite coalition, including all-Never, is at most
e_n. In particular P(T_3^n=Never)≤e_n.

Choose K_n as the FIRST finite date satisfying
P(T_3^n≤K_n)≥1−α_n. It exists because finite mass is at least
1−e_n>1−α_n. Minimality gives P(T_3^n≥K_n)>α_n, also at K_n=0.
Independence and the membership error bound imply

    P(T_i^n<K_n)P(T_3^n≥K_n)
       =P(T_i^n<K_n≤T_3^n)≤e_n.

Thus, with b_i^n=P(T_i^n<K_n),

    b_i^n≤α_n,       P(T_3^n>K_n)≤α_n.             (4)

The latter event includes Never. Form the ACTUAL independent conditional
active laws ν_i^n=law(T_i^n | T_i^n≥K_n), and define

    q_i^n=P(T_i^n=K_n | T_i^n≥K_n),
    p_n=P(T_3^n=K_n).

All conditioning denominators are at least 1−α_n>0. Conditioning an
individual law changes it in total variation by exactly b_i^n. Couple the
old and new laws independently; bounded rewards give payoff difference at
most 4Σ_i b_i^n, uniformly over a fixed replacement of another player.

When 3 surely quits at one row, the finite active Quit/Continue values are

    Q_0=1,          C_0=2q_2;
    Q_1=2q_0−1,     C_1=0;
    Q_2=2q_1−1,     C_2=0.

Their prescribed payoffs are

    g_0(q)=q_0+2(1−q_0)q_2,
    g_1(q)=q_1(2q_0−1),
    g_2(q)=q_2(2q_1−1).                             (5)

For each active player in the ORIGINAL profile,

    |U_i(μ^n)−p_n g_i(q^n)|≤14α_n,                 (6)

and for each actual replacement a∈{QuitK_n,Never},

    |U_i(μ^n[i←a])−p_n v_i^a(q^n)|≤10α_n,        (7)

where v_i^Quit=Q_i and v_i^Never=C_i. For (6), conditioning three marginals
costs at most 12α_n. With those laws, an anchor before K_n gives coalition
{3} and active payoff zero; an anchor at K_n gives (5); an anchor later
than K_n has probability at most α_n and contribution at most 2α_n.
For (7), condition only the two unchanged active opponents, costing 8α_n.
The same anchor split adds at most 2α_n. Both displayed responses wait at
least to K_n, so neither bypasses an earlier anchor. This proves the
counterfactual estimates without using a prescribed-law approximation as
a cap estimate.

Parent e_n-Nash now gives for both actions of every active player

    p_n[v_i^a(q^n)−g_i(q^n)]≤e_n+24α_n.           (8)

Quit0 guarantees player 0 exactly 1 in the ORIGINAL table. Therefore
U_0(μ^n)≥1−e_n; since g_0≤2, (6) gives liminf p_n≥1/2.

The finite game (5) has unique Nash vector (1/2,1/2,1/2). Indeed q_0>1/2
forces q_1=1, then q_2=1, then q_0=0; q_0<1/2 forces q_1=0, q_2=0,
q_0=1. Thus q_0=1/2. Values q_1 above or below 1/2 similarly force
q_0 to 0 or 1, so q_1=1/2. Interior q_0 then forces q_2=1/2.

Take a convergent subsequence of the FINITE coordinates (p_n,q^n) in
[0,1]^4. Its p is positive, so (8) makes its q Nash in (5). Uniqueness
forces every such limit to have q=(1/2,1/2,1/2). Hence q^n tends to that
vector. Then g_0(q^n)→1; (6) and U_0≥1−e_n force p_n→1. Together with
(4), this proves (3). No payoff or cap is evaluated at a limiting stopping
profile: the dates may diverge and the hidden tails remain arbitrary.

## 3. Every unchanged three-player restriction stays exploitable

Apply (3) to any parent approximate-Nash sequence. In each restriction
retaining player 3, with probability tending to one the first coalition
consists of 3 at K_n and the surviving active players whose clocks equal
K_n. Each such player's participation probability tends to
(1−b_i^n)q_i^n=1/2. Bounded rewards cover the vanishing exceptional event.

- Delete 0. Player 1's child reward is minus its participation indicator.
  Its payoff tends to −1/2, while Never gives 0.
- Delete 1. The same holds for player 2.
- Delete 2. Player 0's child reward is its participation indicator, so its
  payoff tends to 1/2, while Quit0 guarantees 1.

Each of these child exploitabilities has liminf at least 1/2.

For the remaining face, delete 3 and retain ALL actual active clocks.
Fix one selected K=K_n, write s_i=P(T_i≥K), q_i=P(T_i=K | T_i≥K), and
let F_0(t) be player 0's actual child payoff from pure Quit at t. Then

    F_0(K+1)−F_0(K)
      =s_1s_2(q_2−q_1+q_1q_2).                    (9)

To prove (9), all outcomes with an opponent quitting before K are identical
under the two responses and cancel. Conditional on both opponents surviving
to K, QuitK gives 1. Under Quit(K+1), a date-K quit by 2 gives payoff 2;
a quit only by 1 gives 0; if both Continue, player 0 surely belongs to the
coalition at K+1 and gets 1, whatever the hidden clocks do at that next date.
The conditional difference is
2q_2+(1−q_1)(1−q_2)−1=q_2−q_1+q_1q_2.

Move ONLY the existing mass m_0=P(T_0=K) from K to K+1, retaining every
other atom and Never mass. This is a valid independent behavioral
replacement. Payoff affinity in one stopping law gives its exact gain

    m_0 s_1s_2(q_2−q_1+q_1q_2)→1/8.              (10)

Here s_1,s_2→1, q_i→1/2, and m_0=(1−b_0)q_0→1/2 by (3). Thus the
deleted-3 exploitability has liminf at least 1/8, independently of EVERY
hidden tail. No child suffix-Nash hypothesis or tail-cap attainment is
needed for this step.

It follows that there is c_0>0 such that, for all actual μ and all d,

    E_(r*)(μ)+E_(r*^(−d))(μ_−d)≥c_0.              (11)

Otherwise choose μ^n,d_n with the nonnegative sum less than 1/n. Select a
subsequence with the same d, using finiteness of I. Parent error tends to
zero, while the relevant positive child liminf above contradicts child
error tending to zero. This proves a positive existential floor, without
optimizing a numerical constant.

## 4. The full open neighborhood remains explicitly solvable

Put δ=||r−r*||∞, keeping Never zero. The same terminal law, prescribed or
deviating, changes payoff by at most δ. Therefore |B_i^r−B_i^(r*)|≤δ and

    |E_r(μ)−E_(r*)(μ)|≤2δ

for EVERY actual profile. The same holds on each restriction. Consequently
the sum in (1) is at least c_0−4δ.

For existence, fix player 3 sure at zero and define active Q_i(r,q),
C_i(r,q) by the finite expectations over the other two independent active
actions. Each is polynomial in q and changes by at most δ from its value
above. Let Δ_i=Q_i−C_i. On [1/4,3/4]^3 the permuted field

    (Δ_1,Δ_2,−Δ_0)

is within 2δ in every coordinate of (2q_0−1,2q_1−1,2q_2−1). Its lower
and upper faces have strict opposite signs for δ<1/8, because their center
values are −1/2 and 1/2. Rectangular Poincare–Miranda therefore gives one
interior q solving ALL three gap equations. Let the active laws be Quit0
with probabilities q_i and Never otherwise. The sure anchor makes their
full response problems exactly Q_i versus C_i, so their complete debts vanish.

The anchor's own Continue path must be checked separately. Let
C=∏_(i=0,1,2)(1−q_i)≤27/64 and let w(S) be the product probability of
the active date-zero quitting set S. Its prescribed payoff is

    Q_3=Σ_(S⊆{0,1,2}) w(S)r_3(S∪{3})≥1−δ.

Its Never payoff W_3 and its payoff L_3 at EVERY positive finite date are

    W_3=Σ_(∅≠S⊆{0,1,2})w(S)r_3(S),
    L_3=W_3+C r_3({3}).

If no active player quits at zero they all chose Never, proving these
identities. Since |r_3(S)|≤δ on coalitions excluding 3,

    W_3≤δ,       L_3≤C+δ≤27/64+δ<1−δ≤Q_3

for δ<1/8. Every full behavioral response is a mixture of Quit0, later
finite times, and Never. Thus B_3=Q_3 and the displayed profile is exact
terminal Nash.

For the uniform-payoff conclusion, active deviations absorb at zero.
An anchor deviation conditional on Continuing at zero has finite-average
payoff at most C+δ, up to the vanishing initial-stage convention: on active
absorption its reward is at most δ, and on the all-active-Never event its
average reward is at most 1+δ, irrespective of its waiting time. This is
strictly below its prescribed payoff Q_3. Mixing this Continue plan with
an immediate Quit cannot yield a positive limiting gain. Prescribed play
absorbs at zero and its averages tend to its single terminal payoff vector.
This verifies the uniform claim for the same actual finite-law profile.

Choose ρ=min(c_0/8,1/8) and c=c_0/2. Both parts of the theorem follow.

## Boundary tests and scope

The exact profile (2) is a positive full-cap test: the global parent
exploitability infimum is zero. Its literal restrictions fail in all four
faces; notably deleting 3 exposes Quit1 payoff 5/4 against prescribed payoff
1 for player 0. Arbitrary hidden clocks cannot fix the restriction along
parent approximate equilibria by the exact actual-law move (9)–(10).

The quantile argument includes K=0, arbitrary Never masses, unbounded clocks,
and e_n=0 via ζ_n=max(e_n,1/n). It uses a finite-dimensional subsequence,
not compactness of the strategy space. The final positive floor is uniform
over faces, not a positive global gap for the parent or any child game.

The theorem rules out an arbitrary-table ADAPTIVE UNCHANGED-CHILD extension
architecture. It is not an obstruction restricted to canonical single-pivot
tables, a new uniform-equilibrium existence class, or a counterexample to
the full conjecture. Cross-face maps allowed to alter surviving laws remain
outside its conclusion.

## Source correspondence and semantic handoff

The new content is the table-specific actual quantile rigidity and the
uniform robust all-four-face obstruction, not the generic tools below.
The original proof and source comparisons are preserved in
[the owned note](../notes/CODEX_TARSKI_PREMIUM__ADAPTIVE_FACE_PRESERVING_EXTENSION_OBSTRUCTION.md);
the open-neighborhood composition is preserved in
[the robustness note](../notes/CODEX_TARSKI_PREMIUM__ROBUST_ADAPTIVE_FACE_GAP_AND_SURE_ANCHOR_EQUILIBRIUM.md).
No external paper theorem is being translated into stronger game semantics.

- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`
  supplies each child's payoff existence. It does not select laws with an
  approximately Nash parent completion. The theorem strictly removes that
  adaptive unchanged-law selection as an arbitrary-table inference.
- `quittingLiftDeletedProfile` and `quittingBestReplyValue_liftDeletedProfile`
  in `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`
  preserve surviving-player semantics in quiet lifts. They do not identify
  those semantics after an arbitrary nonquiet outsider insertion.
- `quittingTerminalPayoff_update_stoppingLawMixture_observer_eq` in
  `UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean` supplies
  the exact one-law affinity behind (10). The moved atom is reconstructed
  as an actual behavioral law, not a correlated change to a terminal law.
- `abs_quittingTerminalExploitability_sub_le_of_reward_close` in
  `Research/Quitting/TerminalExploitabilityRewardRobustness.lean` is the
  whole-strategy 2δ estimate used twice in the robust obstruction.
- The face-sign tool is already present in
  `QuittingRationalStationaryFaceBox.exists_faceNumeratorZero` in
  `UniformEquilibrium/Quitting/Classification/Existence/RationalStationaryFaceBox.lean`.
  Here a finite three-coordinate field is explicitly checked; no desired
  stationary or source certificate is supplied as an assumption.
- EXISTENCE at the center is already covered by
  `QuittingSingleAnchorMembershipReward` and
  `exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`.
  For nearby tables, every anchor-containing reward is at least 1−δ and
  every anchor-excluding reward is at most δ. Thus every complementary
  induced Nash point satisfies `QuittingSingleAnchorInducedDominance` when
  δ<1/2, and `exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorPoint`
  already gives existence. That theorem's stationary profile repeats the
  active hazards on deleted-anchor paths. It is distinct from the one-date-
  then-Never profile whose stronger explicit tail-cap check is above.

The prior proper-face chronology and selected outsider regressions do not
quantify over every child approximant and every adaptive face choice. The
reviewed fixed-face predecessor also has a dummy whose deletion permits a
successful lift; it is not used to infer the all-four-face theorem here.

For a narrow Lean implementation, define only the displayed Fin4 reward and
the unchanged restriction through an explicit equivalence with Fin3. The
main theorem shape is an existential positive constant followed by the
universal inequality (11), and then its reward-neighborhood version (1).
Neither the constant inequality nor a good profile is an input structure
field. Useful intermediate declarations are the actual quantile bounds,
finite matching-game uniqueness, convergence (3), exact adjacent-date
identity (9), and the resulting four child liminf bounds. The quantitative
cutoff estimates (6)–(7) and independent stopping-law reconstruction retain
all behavioral quantifiers. Existing full-cap/terminal-to-uniform machinery
can consume the separately proved nearby explicit profile. No root-finding
oracle, infinite-strategy limit, source renewal, or conjecture-wide compiler
is assumed.
