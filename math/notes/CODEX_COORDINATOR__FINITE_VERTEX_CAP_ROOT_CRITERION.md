# A finite vertex criterion for uniform equilibrium in finite quitting games

Owner: CODEX_COORDINATOR. Ordinary mathematics. The theorem supplies complete
uniform equilibria from a finite raw reward test, for any number of players.
It is retained internally: coverage beyond the existing existence criteria
remains unresolved. The displayed controls have stationary equilibria in
numerical searches, so they are not certified frontier separators. No new
counterexample-class exclusion is counted on the strength of this note.

## Raw finite criterion

Let I have n>=2 players. Let Z_i(S) be arbitrary finite native rewards with
Z_i({i})=0. Live and Never rewards are0. For nonempty D not containing i,
put Delta_i(D)=Z_i(D union{i})-Z_i(D). Define the zero-diagonal matrix
L by L_ij=Delta_i({j}), and the squarefree polynomial vector

 R_i(x)=-sum_{D subset I minus{i}, |D|>=2} Delta_i(D) product_{j in D}x_j,
 C(x)=Lx-R(x),
 H_i=max(0,max_{S nonempty}Z_i(S)).

Choose an explicitly specified invertible matrix T with entrywise
nonnegative entries and a vector xbar>0. At every one of the 2^n vertices
z_i in{0,xbar_i}, check the componentwise inequalities

    0 <= G(z):=z-T C(z) <= xbar-T H.                   (V)

This is finite raw arithmetic; there is no root, strategy, continuation,
return family, or equilibrium witness in the criterion. For fixed xbar,
the inequalities are linear in T; its invertibility is checked separately.
Neither L invertibility nor a higher-joining sign condition is assumed.
The useful specialization T=L^{-1}>=0 gives G=A R with A=L^{-1}.

**Theorem.** For every positive epsilon there is an actual profile of
independent complete quitting laws such that EVERY player's law is finite
almost surely and the SUM of all native full behavioral response debts is
at most epsilon. Consequently, for every independently chosen real offsets
kappa_i and positive scales sigma_i, the table

    r_i(S)=kappa_i+sigma_i Z_i(S), live/Never0,

has a uniform-equilibrium payoff. One target is fixed before accuracy.
The profile may depend on accuracy; all unilateral behavioral deviations
are allowed. There is no bounded-period or bounded-calendar restriction.

## A root for every nonzero nonnegative cap

Set X=product_i[0,xbar_i]. The polynomial G is multiaffine, so each value
in X is a convex combination of its vertex values: the weight of the corner
specified by a subset S is product_(i in S)t_i product_(i notin S)(1-t_i),
where t_i=x_i/xbar_i. Thus(V) holds throughout X.
For any continuation v with0<=v<=H, define

    F_v(x)=T v+G(x)=x-T[C(x)-v].

Nonnegativity of T and(V) imply0<=F_v(x)<=xbar. It is a continuous self-map
of the nonempty compact convex box X, so Brouwer gives a fixed point x.
Invertibility of T then gives C(x)=v. If v is nonzero, x cannot be0,
because C(0)=0 and F_v(0)=T v is nonzero. Coordinates of x may vanish.

Set q_i=x_i/(1+x_i), so q is proper, and c=product_i(1-q_i)<1.
Let Q_i be the immediate-Quit payoff, P_i the passive expected absorption
payoff when i Continues, and h_i the opponent joint-Continue probability.
The exact offer identity is

    (Q_i-P_i)/h_i=C_i(x)=v_i.

Thus every player is indifferent between Quit and Continue at v, including
inactive players. This is a full mixed Nash root, not only an observer root.
It is produced for every nonzero cap in the entire nonnegative reward box.

## The compact carrier and elementary global-minimum lemma

For an actual independent complete quitting-law profile whose EVERY law is
finite almost surely, let U be its prescribed native terminal payoff and B
its supremum over all unilateral complete behavioral replacements. Such
replacements may choose Never. Full debts d_i=B_i-U_i are nonnegative.
Take the closure K of all these finite-dimensional pairs(U,B). It is compact
because every payoff and cap is bounded by the finite raw rewards. All debts
remain nonnegative, and B_i<=H_i. Finite root prefixing preserves K: prefix
the same independent root to each actual approximant. Every player's new
law is still finite almost surely. The prefix map is continuous because

 U'_i=q_i Q_i+(1-q_i)P_i+c U_i,
 B'_i=max(Q_i,P_i+h_i B_i),
 d'_i=c d_i+R_i^root,
 R_i^root=max(Q_i,P_i+h_i B_i)
            -q_i Q_i-(1-q_i)(P_i+h_i B_i)>=0.           (1)

The formula for B prices the entire response menu. After fixing private
randomness, a behavioral deviation is a quitting deadline or Never, and
any choice after Continue is bounded by the continuation full cap.

Suppose for contradiction that min_K sum_i d_i=g>0. Fix any pivot p and
let C_p be the closed subset with d_i=0 for i!=p. It is nonempty: force p
to quit at date0; at that date let its n-1 opponents use a finite-game mixed
Nash equilibrium. Give each opponent who Continues the prescribed sure-quit
date1. All marginal laws are finite. Against a fixed observer, p still quits
at date0, so that observer's whole deviation menu has just the two finite-
game endpoint payoffs; its debt is0. The pivot's debt is unconstrained.

Choose a global minimum of d_p on C_p, with value m>=g>0 and pair(U,B).
For any root q that is observer-Nash at B, formula(1) and minimality imply

    m(1-c)<=R_p^root.                                 (2)

For0<=a<m, take any full Nash root at the arbitrary finite annotation
B-a e_p; finite mixed Nash existence supplies it. Its observer regrets at B
are0, while its pivot regret at B is at most a q_p h_p. To check this bound:
if q_p=0 the shifted Continue preference implies zero regret at B; if
0<q_p<1 its shifted indifference makes the regret exactly a q_p h_p; if
q_p=1 its shifted Quit preference bounds the regret by a h_p.
Since c=(1-q_p)h_p, (2) yields

    m(1-h_p)<=(a-m)q_p h_p.                           (3)

The left side is nonnegative and the right side nonpositive. Necessarily
h_p=1 and q_p=0, so this Nash root is AllContinue. Its own-singleton rewards
are0, hence B_i>=0 for every observer and B_p>=a. Letting a increase to m
proves

    B>=0 and B_p>=m>0.                               (4)

This elementary lemma needs no genericity, singleton inverse condition,
positive payoff margin, degree calculation, or actual realization of the
minimizing closure point.

## Strict descent and actual profiles

The cap B from(4) is nonzero and lies in0<=B<=H. The raw root producer gives
a full Nash root at B with c<1. Its root regrets in(1) are all0. Prefixing
therefore retains all zero observer debts and changes the pivot debt to
c m<m, contradicting the chosen global minimum.

Thus min_K sum d_i=0. Since K is the closure of the actual all-marginal-
finite pairs, for every positive epsilon an actual such profile has total
native debt at most epsilon. No strategy or successful recurrence was
assumed. Compactness, finite Nash, and the Brouwer root construction supply
all witnesses in this contradiction proof.

## Signed offsets and the fixed uniform target

Fix n>=2 and one all-marginal-finite profile. Under ANY unilateral replacement
by player i, at least one opponent has an almost surely finite quitting date;
in fact T_-i=min_{j!=i}T_j is finite almost surely. Thus absorption still
occurs almost surely. Every terminal payoff shifts by exactly kappa_i and
scales by sigma_i, for the prescribed play and for every response. Hence

    d_i^r=sigma_i d_i^Z.

This signed-offset identity would not follow merely from joint absorption;
the stronger marginal condition proved above is essential.

Choose actual profiles with native total debt tending to0. Their original
terminal payoffs lie in a fixed bounded cube, so take one convergent
subsequence with limit u_* before choosing accuracy. Its terminal regrets
also tend to0. For one selected profile and reward bound R, uniformly over
all unilateral deviations of i, the finite-horizon Cesaro payoff differs
from its terminal payoff by at most

    2R E[min(T_-i+1,Horizon)/Horizon].

This tends to0 by dominated convergence, because T_-i is finite almost
surely and its law is fixed by the prescribed opponents, independent of
the deviator. The same holds for the prescribed payoff. Select the profile
with small terminal debt and terminal payoff close to u_*, then one horizon
threshold for all players. For every larger horizon the same profile
approximates u_* and prices every complete behavioral deviation. This is
the asserted fixed-target uniform-equilibrium contract.

## Monotone and explicit cyclic adapters

If L is invertible with A=L^{-1}>=0, take T=A. Condition(V) is exactly
0<=A R(z)<=xbar-A H at all box vertices. If additionally all higher joining
increments are nonpositive, R has nonnegative coefficients, and it is enough
to check a raw supersolution

    C(xbar)>=H.

Indeed A R(xbar)<=xbar-AH and0<=AR(z)<=AR(xbar) at every vertex. One fully
explicit option is xbar=2 A H whenever it is strictly positive and
R(2 A H)<=H. A supplied strategic root is unnecessary.

For an open polyhedral Fin4 adapter, suppose L has one positive entry per
row, at a predecessor permutation consisting of one4cycle, all other
linear entries are negative, and all higher joining increments are negative.
Fix xbar=2*1 and require C(xbar)>H. These are strict linear raw inequalities,
where the comparison with H is expanded against0 and every raw reward.
They also produce A>=0: write L=(D-N)P, with D positive diagonal and N>=0.
Since L xbar=C(xbar)+R(xbar)>0, y=P xbar>0 gives D^{-1}N y<y. In the
weighted max norm, D^{-1}N has norm<1, so the Neumann inverse proves
L^{-1}=P^{-1}(I-D^{-1}N)^{-1}D^{-1}>=0. This argument remains valid for
any n>=3 full positive cycle and any checked positive xbar.

The canonical premium family has, at xbar=2*1,
C(xbar)=(2M-122,2M-124,2M-126,2M-124) and H=(M-1)*1.
Thus M>125 passes strictly. This verifies that the class is nonempty and
contains an open raw neighborhood, but this canonical family is already
covered. A separating example from all relevant prior criteria remains
necessary before an export claim.

## Source correspondence and outstanding overlap audit

The exact finite-game input is exists_isZeroQuittingRootNash in
UniformEquilibrium/Quitting/Root/NashExistence.lean. Prefix continuity and
diagonal semantics are quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash
and continuous_quittingTerminalSemanticPrefix in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean. Full behavioral
response recursion is quittingContinuationBestResponseValue_rootThenContinuation_eq_max
in UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. Brouwer's box
fixed-point theorem is the standard theorem also used through
FixedPointTheorems.brouwer by MathUE/Topology/PoincareMirandaCube.lean.
The fixed-target endpoint also agrees with
quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors in
UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean.
No Lean change or build is claimed.

The pending coverage issue is substantial: does the finite vertex criterion
already force a stationary equilibrium, or is it covered by existing raw
consumers? No answer is claimed. The theorem cannot be counted as a newly
excluded Fin4 class without resolving that question. It does supply a complete
consumer for the raw root-box test; it does not require an assumed return,
entry, or actual realization of the minimizing semantic point.
