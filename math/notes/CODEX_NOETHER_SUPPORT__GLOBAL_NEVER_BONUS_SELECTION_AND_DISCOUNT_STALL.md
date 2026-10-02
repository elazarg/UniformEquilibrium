# Global Never-bonus selection and an exact discount stall

Author: CODEX_NOETHER_SUPPORT.

Status: ordinary mathematical proofs, not Lean-checked and not an export
proposal. The discount rule in Section 2 fails. Section 3 proves a global
auxiliary-equilibrium selector on the familiar solo-pivot face. Section 5
extends the selection language to a non-solo paired raw class by optimizing
over a vanishing bonus box. Both existence classes were already covered;
the new content is the selection/calibration statement, not UE coverage.

## 1. Exact question and source correspondence

There are four players, independent private stopping laws, finite rewards
r(S) at nonempty quitting coalitions, and payoff zero at infinite all-Continue.
The own singleton vector is (1,0,0,0). Write F_N={0,...,N−1,Never}.
For a product of laws on F_N let U_i be its original prescribed payoff,
E_N its maximum menu best-response gain, W_0 the original payoff to pivot 0
from Never, and D_0 the product of the three nonpivots' Never probabilities.
The complete exploitability is

    E = max(E_N,L_0),                 L_0=W_0+D_0−U_0.       (1)

Indeed every response beyond the menu equals Never for nonpivots, while
it equals W_0+D_0 for the pivot. Arbitrary behavioral deviations correspond
to mixtures of these pure stopping responses. The question is whether one
can select actual finite laws with both terms in (1) arbitrarily small;
N may grow with the requested accuracy.

Inspected declarations are `singlePivot_nonpivot_fullCap_eq_menuCap`,
`singlePivot_pivot_fullDebt_eq_max_menuDebt_scalar`, and
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`;
the exact conditional consumer is
`exists_uniformEquilibriumPayoff_of_singlePivot_finiteMenu_scalar_source`
in `SinglePivotFiniteMenuCompletion.lean` in the same directory. The research
question is [the current finite-menu question](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md).

Credit for the STALL table and its exact-menu obstruction below belongs to
[STALL](../gpt/STALL.md). Credit for investigating private planned-Never
bonuses and global equilibrium selection belongs to CODEX_HILBERT's
[first bonus note](CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md)
and [adaptive portfolio note](CODEX_HILBERT__ADAPTIVE_NEVER_BONUS_PORTFOLIO_ON_H.md).
The all-nonpivot saturation rule below is a different objective and has an
elementary raw-table comparison profile. It does not claim novelty for the
private-bonus concept or the underlying solo equilibrium.

## 2. A vanishing realized-time discount does not select away STALL

Use core players 0,1,2 and the following complete core table:

| Core coalition | Core rewards |
| --- | --- |
| {0} | (1,3,3) |
| {1} | (3,0,3) |
| {2} | (3,3,0) |
| {0,1} | (4,1,3) |
| {0,2} | (1,3,4) |
| {1,2} | (3,4,1) |
| {0,1,2} | (2,2,2) |

Without player 3 append reward 1; with player 3 and a nonempty core append
reward 0 and leave the core rewards unchanged. Coalition {3} pays zero.
Thus all fifteen coalitions are specified, all rewards are in [0,4], and
own singletons are canonical.

Perturb the F_N game by paying λ_N^t r(S) at absorption date t, with
λ_N=1−1/N² for N≥16, and still pay zero at Never. Select any exact Nash
equilibrium of this perturbed finite game.

Claim: its unique product of stopping laws is the original STALL law: all
Continue before date N−1, and at that date independent hazards

    q*=(2θ,θ,4θ,0),       θ=3/2−√2.                        (2)

Consequently the ORIGINAL menu regret is zero and the ORIGINAL late gain is

    L_0=β=21/2−7√2>1/2                                   (3)

at every such N. Yet the supremum norm of the entire auxiliary payoff
perturbation is at most 4/N and tends to zero.

Proof. At a root with normalized continuation v, the core Quit-minus-
Continue gaps, using cyclic indices modulo three, are

    (s_i−v_i)(1−q_{i+1})(1−q_{i−1})+q_{i+1}−2q_{i−1}.    (4)

No core coordinate can equal one in an exact root equilibrium, for any v:
q_i=1 forces q_{i+1}=0, then q_{i−1}=1, then gives player i a negative gap.
The dummy player has Quit value zero and Continue value
H+(1−H)v_3, where H is core absorption probability. Her sure quitting in a
reached row would therefore force H=0, but the pivot could join her and
gain one. These statements remain true with discount: divide by the
positive current-date weight and replace continuation by its positive
discounted value. All continuation rewards of player 3 are nonnegative.
Thus every date is reached with positive probability in every auxiliary
Nash law, and every conditional tail is itself auxiliary Nash.

At zero continuation the unique root is (2). To check this directly from
(4), all core coordinates must be positive: q_0=0 contradicts the other
two best responses and then the pivot's gain; q_1=0 with q_0>0 forces
q_2=1; and q_1>0 forces q_2>0. They are therefore interior. Zero gaps imply
q_0=2q_1, q_2=4q_1 and 4q_1²−12q_1+1=0, giving θ. The dummy Continues.
Its unweighted payoff vector u has every u_i>s_i, and

    u_0=3(1−β)=21√2−57/2>9/8.                              (5)

Whenever all four continuation coordinates exceed their own singletons,
all Continue is the unique root Nash point. The dummy must Continue;
any positive core coordinate, by (4), forces q_{i+1}>2q_{i−1} and hence all
three coordinates positive. Summing these inequalities is impossible.

Since λ_N^(N−1)≥1−1/N≥15/16, (5) implies
λ_N^(N−1)u_0>1. Every earlier backward continuation is a scalar multiple
λ_N^k u with all its coordinates strictly above the singleton vector.
Backward induction therefore forces all Continue until the last date and
proves uniqueness. Existence follows by the same backward inequalities.
The original law has U_0=W_0=u_0 and deleted Never mass β, proving (3).
Finally 4(1−λ_N^(N−1))≤4/N bounds the payoff perturbation. This rules out
this specified vanishing discount rule, not perturbation methods generally.

## 3. A global selection rule with an exact scalar entrance

Define three pairs of raw reward coordinates

    v_j=r_j({0}),       k_j=r_j({0,j}),       j=1,2,3,

and the closed interval, possibly empty,

    Q={q∈[0,1] : q k_j≤v_j for all j=1,2,3}.                (6)

No other reward coordinates are restricted except the canonical own
singletons. Assume Q is nonempty and choose any q∈Q. Let

    K=max(0,k_1−v_1,k_2−v_2,k_3−v_3).

Use a common private planned-Never bonus ξ_N for the nonpivots only. Thus
the auxiliary pure payoff to player j>0 is its original terminal payoff
plus ξ_N times the indicator that its CHOSEN menu action is Never; the
pivot's payoff is unaltered. The bonus is paid even when another player
quits earlier. It is an auxiliary normal-form payoff, not a modification
of the original game's terminal reward or Never convention.

The selector is: among all exact Nash equilibria of this finite auxiliary
game, maximize

    H(σ)=p_1(Never)+p_2(Never)+p_3(Never).                   (7)

The Nash set is nonempty and compact and H is continuous, so maximizers
exist. Choose the bonus as follows:

| Chosen q | Bonus and comparison pivot law |
| --- | --- |
| q=0 | ξ_N=K/N; pivot uniform on 0,...,N−1 |
| 0<q<1 | ξ_N=K(1−q)^(N−1); pivot hazard q before N−1, sure Quit at N−1 |
| q=1 | ξ_1=0; pivot surely quits at date zero |

Theorem: EVERY maximizing output has

    E_N≤ξ_N,                 L_0=0,                       (8)

and the three nonpivots choose Never surely. Hence this is an actual
finite-law approximate selector at arbitrary accuracy when (6) holds.
It does not use full exploitability as its selection objective.

Proof. We first construct an auxiliary comparison equilibrium with H=3.
Let the nonpivots all choose Never. Any proper finite pivot law is then an
exact pivot best response: every finite date pays one and Never pays zero.
Write S_t=P(T_0≥t) and p_t=P(T_0=t). A nonpivot j's original Never payoff
is v_j, and its original pure response at t is

    F_j(t)=v_j(1−S_t)+k_j p_t.                              (9)

This accounts separately for earlier pivot absorption, a collision at t,
and solitary nonpivot quitting before the pivot, which pays zero.

For q=0, (6) says v_j≥0. Under the uniform comparison law, (9) is
(t v_j+k_j)/N, maximized at t=N−1, and exceeds v_j by at most K/N.
For 0<q<1, at every nonfinal date (9)−v_j equals
(1−q)^t(q k_j−v_j)≤0. At the final date it equals
(1−q)^(N−1)(k_j−v_j)≤ξ_N. For q=1 the same check reduces to k_j≤v_j.
The private bonus therefore makes each nonpivot's prescribed Never action
an exact auxiliary best response in every case. This proves the comparison
equilibrium and H=3. Every maximizer has H=3, hence all three nonpivots
choose Never surely. Its exact pivot optimality forces p_0(Never)=0.
Thus U_0=1, W_0=0, D_0=1 and L_0=0. Removing a private bonus of size ξ_N
from an auxiliary Nash law increases each nonpivot menu regret by at most
ξ_N. Canonical zero nonpivot singletons make menu and complete caps agree.
This proves (8), including unrestricted behavioral replacements via (1).

The comparison construction is rational when the table, q and bonus are
rational. The arbitrary globally maximizing equilibrium need not have
rational coordinates; no rational-selection assertion is made about it.

## 4. Exact scope, examples, and what is not new

Condition (6) exactly characterizes the possibility of original finite
approximate equilibria with all nonpivots always Never, even if arbitrary
pivot laws and growing supports are allowed. Sufficiency is Section 3.
For necessity, take such laws with complete error tending to zero. The
pivot's prescribed value is 1−p_0(Never), while a late finite response pays
one, so p_0(Never) tends to zero. A nonpivot's prescribed payoff tends to
v_j, and its response at date zero pays k_j p_0(0). Take a subsequence
along which p_0(0) tends to q∈[0,1]. The regret inequalities give q k_j≤v_j
for every j, establishing (6).

For interior q, the infinite constant-hazard solo-pivot law is already an
exact terminal Nash law: (9) at every date is at most v_j, and its pivot
quits almost surely. For q=0, the singleton column is weakly unblocked
and small constant pivot hazards give the familiar stationary approximate
family. For q=1 there is already a one-date exact law. Thus Section 3 is
not a new UE existence theorem. Its useful content is the global selection
statement, including control of ALL its maximizers.

For STALL, v=(3,3,1) and k=(1,4,0). Choose q=1/4 and K=1. The comparison
law therefore uses bonus (3/4)^(N−1), the objective's maximum is three,
and every selected auxiliary equilibrium has complete error at most that
bonus and zero late gain. This succeeds on the exact same table where
Section 2's unique discount equilibrium retains late gain β. STALL has an
actual payoff strictly above all own singletons, so universal weak payoff
exclusion does not hold there. This is a selection comparison, not a new
existence result for STALL.

The normal-core/Q comparison also cannot be inferred from failure of payoff
exclusion. The definitions inspected are `normalizedSoloMatrix` in
`Quitting/Classification/LCP/Normalization.lean`, `normalLayer` and
`normalCore` in `NormalCore.lean`, `StandardLCPSolution` and
`IsStandardQMatrix` in `MatrixClasses.lean`, and `StandardQMatrixSide`
in `Gate.lean`. The actual existing theorem is
`exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide` in
`StationaryExistence.lean` in the same directory; the alternative is not
a disjoint classification of strategic solvability. The q=0 branch is
already the weakly unblocked solo branch; the explicit all-behavior source
`isεAsymptoticNash_soloStationary_le_pairPremium` in
`Quitting/Classification/Existence/AcyclicSoloPreemption.lean` was checked.

Unlike q=0 alone, the scalar test (6) can coexist with a full-normal,
nonhomogeneous standard-Q singleton matrix. For example choose the
normalized singleton matrix

    M = [ 0 −1  1  1 ]
        [−1  0  1  1 ]
        [ 1  1  0 −1 ]
        [ 1  1 −1  0 ],

and define raw singleton rewards by r_i({j})=s_i+M_ij with
s=(1,0,0,0). Set k=(−4,2,0); all other nonsingleton coordinates may be
zero. Then v=(−1,1,1), and Q=[1/4,1/2]. The full-core,
nonhomogeneous standard-Q calculation for precisely this matrix is proved
in the independently inspected
[paired-class review](../feedback/CODEX_TARSKI_PREMIUM__ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_SELECTOR__BY_CODEX_FRECHET_CYCLE.md),
“Narrow comparison with the normal-core/non-Q stationary consumer.”
Every row has its partner as a negative witness. Singleton
homogeneous supports fail at that partner; all larger principal matrices
are invertible. That review additionally supplies a complete arbitrary-
right-hand-side LCP case analysis, not a finite-grid inference. This only
shows that (6) does not imply the non-Q sufficient hypothesis: the very
same example has the elementary exact solo stationary law just proved.

## 5. Bonus-box minimization on a genuinely non-solo paired face

This extension uses the already proved raw paired producer in
[Asymmetric paired-cycle equilibria with exact finite response caps](../exports/ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_FINITE_SELECTOR.md),
Sections 1–5, read in full. Credit for testing this connection belongs to
the coordinator. No new paired-existence proof or coverage claim is made.

Here is a direct canonical raw subrectangle of that packet. Pair players
as {0,2},{1,3}, write p(i) for the partner, and keep canonical own singleton
vector s=(1,0,0,0). For every player i and the other pair B={k,l}, require

    s_i−11/10 ≤ r_i({p(i)}), r_i(B) ≤ s_i−9/10,
    s_i+9/10 ≤ r_i({i,p(i)}), r_i({k}), r_i({l}) ≤ s_i+11/10,
    r_i({i}∪T) ≤ s_i+1/50                for ∅≠T⊆B.        (10)

Other entries are arbitrary finite reals. These are precisely a subrectangle
obtained by taking original own singletons equal to one and making the
packet's justified canonical transformation. The packet does NOT assume
terminal-only translation preserves finite zero-Never payoffs; it transports
the infinite law and every unilateral deviation using certain absorption,
then computes the finite canonical law afresh.

This rectangle is outside the solo test (6): the pivot's partner 2 has
v_2≤−9/10 and k_2≥9/10. Its symmetric center has the full-normal,
nonhomogeneous standard-Q matrix displayed above, with the pairing labels
permuted. The packet also produces a prescribed payoff strictly above every
own singleton, so weak payoff exclusion fails. These are concrete comparison
facts, not exclusion from all already solved existence classes.

For K≥1 put

    N=2K,       b_K=(99/100)^(3K),       δ_K=(5/3)b_K.

For EACH bonus vector ξ∈[0,δ_K]^4 define the finite auxiliary game by giving
player i its original terminal payoff plus ξ_i for its privately chosen
Never action. This time the pivot also may receive a bonus. Jointly choose
(ξ,σ), where σ is an exact Nash equilibrium of the corresponding auxiliary
game, to minimize the deleted pivot Never probability

    D_0(σ)=p_1(Never)p_2(Never)p_3(Never).                  (11)

This is a definite global selection rule. The feasible set is nonempty and
compact: finite Nash existence supplies points for every ξ, and the Nash
inequalities are closed and continuous in bonuses and the finite mixed laws.
The selector's INPUTS are the raw reward table, N and the displayed bonus
box. Neither a periodic hazard vector nor an already good finite law is an
input. A finite polynomial optimization describes it; efficiency and rational
exact maximizers are not asserted.

Theorem: every globally minimizing output satisfies

    E_N≤δ_K,             L_0≤b_K,             E≤δ_K.        (12)

Thus the rule selects literal finite approximate laws beyond the solo face,
on this already covered paired raw class.

First observe a general fact independent of (10). Auxiliary Nash gives

    F_i(a)+ξ_i 1_{a=Never} ≤ U_i+ξ_i p_i(Never).

Thus original menu regret is at most ξ_i≤δ_K. In particular

    W_0−U_0 ≤ −ξ_0(1−p_0(Never))≤0,

so the original late gain is at most D_0, with NO additional perturbation
error. To prove (12) it remains to produce one feasible comparison point
with D_0≤b_K; the following calibration supplies exactly that.

By the cited raw paired theorem, (10) produces hazards 1/100<q_i<1/2,
an infinite exact terminal Nash law with certain opponent absorption under
every deviation, and its K-cycle censored laws σ^K. Set

    a_i=1−q_i,       C=∏_i a_i,       d_i=∏_{j≠i}a_j.

For one fixed canonical payoff vector v the packet gives

    0<v_i≤5/3,       U_i(σ^K)=(1−C^K)v_i,
    B_i(σ^K)=v_i,    p_i(Never)=a_i^K.                     (13)

Every supported finite stopping date has original response value EXACTLY
v_i. To see this, the corresponding infinite law is a mixture of its own
active dates, each with strictly positive mass. Its prescribed value and
complete cap both equal v_i. Consequently no such supported pure response
can have value strictly below v_i. Censoring after the calendar does not
alter a pure response inside it, because that response forces absorption
by its chosen date if opponents have not already absorbed.

Expanding (13) in the censored player's own stopping law therefore gives

    (1−C^K)v_i=(1−a_i^K)v_i+a_i^K W_i,
    W_i=(1−d_i^K)v_i.                                     (14)

Choose the comparison bonuses

    ξ_i*=d_i^K v_i.                                       (15)

Every supported finite response and the bonus-corrected Never response then
pay exactly v_i; all other finite responses pay at most v_i by (13).
Therefore σ^K is EXACT Nash in the auxiliary game with bonuses (15).
Since d_i≤(99/100)^3, these bonuses lie in the prescribed box. Moreover
D_0(σ^K)=d_0^K≤b_K. The minimum in (11) is no larger than this comparison
value. Apply the general auxiliary inequalities to every minimizing output
to obtain (12), and apply (1) to include all behavioral deviations.

The comparison uses the existing raw paired producer essentially. The
selector does not need to compute that comparison law or its calibrated
bonus vector: it searches the entire explicitly bounded bonus box. This
distinguishes the selection theorem from a supplied-profile verification,
but it does not turn the calibration into an independent universal producer.

An exact rational test uses original pair data s_i=1, partner payoff 0,
own-pair payoff 2, other singleton payoff 127/63, other-pair payoff 0,
and all applicable joining rewards 1. Constant pair hazards q_i=1/7 solve
the field because the active value X=8/7 and post-active value Y=4/3 obey

    Y=2q(1−q)(127/63)+(1−q)²X,       q=1/7.

After canonical transformation and starting with pair {0,2}, the initial
vector is v=(8/7,1/3,1/7,1/3). Equations (13)–(15) are checked by direct
rational enumeration in
[the owned calibration checker](../experiments/CODEX_NOETHER_SUPPORT__CHECK_PAIRED_NEVER_BONUS.py).

Subsequent completeness test: requiring its minimum deleted Never mass to
vanish is NOT necessary for canonical UE existence. The exact
[all-horizon counterexample](CODEX_NOETHER_SUPPORT__BONUS_BOX_DELETED_NEVER_COMPLETENESS_FAILURE.md)
has minimum D_0 equal to one at every small bonus ceiling, while EVERY
auxiliary equilibrium is an exact original terminal equilibrium. Positive
slack of the unused pivot Never response cancels D_0 there. Thus a universal
proof cannot insist on the low-D_0 comparison used for the paired class.

Current next question: can the same permitted bonus boxes select small
ACTUAL late gain universally, retaining that unused-action slack? No
approximation-to-exact auxiliary Nash theorem is supplied by the present
periodic comparison or by the finite-menu compactness argument alone.
