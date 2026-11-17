# Uniform equilibrium with two unrestricted recipient rows

Let four players have independent private stopping laws on the positive
integer dates and Never. First exit by the nonempty coalition T pays
r(T), and live play and joint Never pay zero. Write s_i=r_i({i}),
Z_i(T)=r_i(T)-s_i on nonempty coalitions, and Gamma_ij=Z_i({j})
for j distinct from i, with zero diagonal. All rewards are finite real
numbers. Partition the owners into h,k,a,b. The entire thirty original
payoff entries of h and k are arbitrary.

There are two alternating phases. Both h and k may quit in both. Player a
is scheduled only in the first phase and b only in the second. For each
e in {a,b} write o for its scheduled phase and p for the other one.
Given opponent hazards, define P as the expected native reward
contribution if e waits at that date, Q as its forced native Quit
offer, and H as the probability no opponent quits. Thus P is the sum
of probabilities times Z_e(T) over nonempty opponent subsets, Q uses
Z_e(T union {e}), and both contributions at the empty subset are zero.
At o the two hazards x are those of h,k. At p the three hazards y are
those of h,k and the other scheduled owner.

**Theorem.** Suppose the following comparisons hold on the specified two
rows. Then the original game has a uniform-equilibrium payoff.

1. For e=a,b and all x in [0,1)^2, y in [0,1)^3, put

       A_e=H_o(P_p+H_p Q_o)-(Q_o-P_o),
       B_e=P_p+H_p P_o-(1-H_o H_p)Q_p.

   Require A_e>=0 to imply B_e>=0.
2. In the row of a, for each of the three nonempty subsets T of {h,k},
   require Z_a(T union {a})>=Z_a(T).

The tests refer only to the rewards. The implication in (1) is polynomial
in five real variables, so it is a finite semialgebraic test. It requires
no solution of the quitting game. There is no separate sign or premium
condition on b. The theorem includes signed own levels and every
unilateral behavioral replacement. One target is fixed before the
accuracy and finite-horizon threshold are chosen.

Here is a simple finite sufficient test for (1). For each e pick u_e>=0.
On subsets of {h,k} require native P(T)<=0 and Q(T)-P(T)>=0, and on
all nonempty subsets of the three opponents require Q(T)<=-u_e P(T).
Here P(T)=Z_e(T) and Q(T)=Z_e(T union {e}). In particular, it suffices
that for e=a,b the passive rewards are sums of their singleton
comparisons, joining multiplies that sum by -u_e with u_e>0, and each
sees h and k nonpositively as singleton quitters. The two factors may
differ. Neither free row needs to have this form.

To check the finite test, set U=Q_o, W=(Q_o-P_o)/H_o. Its scheduled
guards give W>=max(0,U), and A_e>=0 gives P_p>=W-H_p U>=0.
Hence Q_p<=0. With D=1-H_oH_p,

    P_p+H_p P_o = (P_p+H_p U-W)+D W >=0,

which proves B_e>=0. All comparisons use the independent hazards,
including each possible simultaneous exit.

## Six phase choices and one shifted comparison

Work by contradiction on this same original game. The proved
counterexample necessities give R0 and nonzero minimum-map degree
(in fact degree one) of Gamma, and each original upper punishment value
mu_i is at most s_i. Here mu_i is the infimum over opponent policies of
the supremum of i's original terminal payoff. The necessary declarations
and their signed hypotheses are recorded in the
[global singleton reduction](FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md)
and the [punishment-normal adapter, section 10](NATIVE_COLLISION_FLOOR_AND_GLOBAL_MASS_DICHOTOMY.md).

Give each available action a nonnegative odds variable z, with hazard
z/(1+z). For each e=a,b use the U_e,W_e above and set
F_e=P_p+H_p U_e-W_e. For each free i=h,k and each phase v, let w
be its other phase and p_iw its own hazard there. Define

    F_iv=p_iw Q_iw+(1-p_iw)(P_iw+H_iw Q_iv)
         -(Q_iv-P_iv)/H_iv.

The expectations are taken over all available opponents at the relevant
phase and exclude the owner's own hazard. All H here are positive at
finite odds. For lambda>=0 consider

    z>=0,   F(z)-lambda e_a>=0,   z_j(F(z)-lambda e_a)_j=0.

Only a's one scheduled comparison is shifted. For every such root
lambda is bounded by a constant depending on the fixed table. Indeed
condition (2) gives W_a>=0, so F_a<=P_ap+H_ap U_a is bounded above.
This argument leaves the other five comparisons unshifted.

At zero, F(z)=Lz+O(||z||^2) where L duplicates the rows and columns
of h,k in Gamma, one coordinate per available phase. To first order
the two passive contributions add and the forced Quit terms cancel,
independently of the higher rewards. A nonnegative homogeneous
complementary solution for L collapses, by adding the two copies of
each free owner, to one for Gamma. Hence L is R0. Its degree is the
degree of Gamma. To see this, choose a generic target y in the four
equations Gamma v>=y. For any fixed support, a singular active block
has target in a proper subspace; for a regular block, zero active
weights or a zero inactive slack also cut out proper hyperplanes.
Thus every root is regular with local sign the sign of its active
principal determinant (empty determinant one). In the duplicate
coordinates give each extra copy target y_i-1 and the first copy y_i.
The extra copies are strictly slack and must vanish. All roots and
local index signs agree with the four-dimensional ones. Offsets can
be homotoped to zero on a fixed large ball: any unbounded root
sequence for bounded offsets would give an R0 violation by scaling.

For the minimum-map argument extend F to all of Euclidean space by
F(z^+)+L(z-z^+). If the homotopy roots are bounded in z, the total
degree on a ball containing all of them is zero, since lambda is
bounded on the solution set. At lambda=0 the local degree at zero
is nonzero by the expansion and the positive minimum of ||min(z,Lz)||
on the unit sphere. Excision gives a nonzero finite root at lambda=0.
The other possibility is a sequence of homotopy roots with unbounded
odds. We show how each possibility supplies an original equilibrium.

## Actual choices at proper odds

At a finite root with at least two distinct owners using positive
hazards, each owner's opponents absorb geometrically in two-phase
periods for every unilateral policy. Finite native values thus restore
the signed original offsets. For a free owner let V_v be its prescribed
value, with C_v=P_v+H_v V_w the Continue offer. From
V_v=p_iv Q_v+(1-p_iv)C_v and the corresponding equation at w one gets

    [1-(1-p_iv)(1-p_iw)H_vH_w](C_v-Q_v)=H_v F_iv.

Thus both phase choices of each free owner are optimal, also on the
shifted homotopy. For an unshifted scheduled owner e the Never values
at the passive and scheduled phases are respectively

    (P_p+H_p P_o)/(1-H_oH_p),   (P_o+H_o P_p)/(1-H_oH_p).

Their surpluses over the corresponding Quit offers have numerators
B_e and A_e. The latter equals H_o F_e and vanishes when e actually
mixes. Condition (1) prices the passive action. These Never values
are the actual values: substituting them into the policy equations
works at a positive hazard by this indifference and at zero by the
Continue recursion. The same conclusions hold for a if lambda=0,
and also if a has zero hazard. In particular all unshifted owners
are best responding at both phases for every finite homotopy root.
Iteration of the Bellman inequalities bounds entire unilateral laws,
including literal Never. At a nonzero unshifted root this gives exact
terminal Nash and, by the geometric survival bound, a fixed original
uniform payoff.

If just one owner g has a positive hazard, all the other owners are
quiet and have a geometric opponent. Their comparisons still hold: a
quiet shifted owner uses only Continue and F_a>=0 suffices. If g=a
then F_a=0 because its opponents never play, so lambda=0. In native
coordinates the sole owner's payoff against all Never is zero under
every law. The profile absorbs and gives a native terminal Nash.
For the signed original game, play these policies for N periods and
after survival switch the opponents to an original punishment for g
within epsilon of mu_g<=s_g. Until then a deviating g can collect only
s_g by stopping; postponing cannot earn more than s_g+epsilon. For the
prescribed profile and for any other deviator the tail modification
costs at most twice the reward bound times the probability that g
survives N periods, which tends to zero. This gives terminal Nash at
every accuracy, implying a fixed original uniform payoff by the
[terminal characterization](GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md).
Thus under the contrary assumption every nonzero root under
consideration has at least two distinct effective owners.

## A phase with a sure quitter at the limit

If odds are unbounded, choose a subsequence on which all six hazards
converge. At least one owner tends to sure in some phase v. Use its
limiting hazards as an original opening date. To get a uniform payoff
it suffices to verify the one-stage Nash comparisons with continuation
mu_i for each owner. This is the checked
[sure-quitter punishment-vector criterion](../../UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean).
Only a sole sure owner can reach that continuation by deviating.
The criterion allows punishments approximating the infimum.

Every unshifted owner is best responding at every finite root along
the sequence. Its actual original continuation value at the other
phase is at least its own mu_i, by the definition of punishment value;
it is also bounded by the fixed reward bound. If this owner faces a
sure opponent in the limit, its one-step comparisons therefore pass
to the opening head with the continuation term disappearing. If it
is the sole sure owner, its positive hazard implies equality of its
two offers at the finite roots. Passing to the limit and using the
lower bound mu_i prices withdrawing. This argument also applies to
the scheduled owner b in its permitted and omitted phases.

If a is passive and faces a sure opponent, along the sequence
A_a=H_o F_a>=0 implies B_a>=0. At the head H_p=0 and the limiting
inequality is Q_p<=P_p. If a is scheduled and faces a sure opponent,
F_a>=0 gives Q_o-P_o<=H_o(P_p+H_p U_a) tending to an upper bound
of zero. When a has positive limiting hazard, F_a=lambda is bounded,
so Q_o-P_o tends to zero. These price its two actions as required.
Finally, if a itself is the sole sure owner, its phase is scheduled.
Its two possible opponents there are exactly h,k. Condition (2)
implies Q_o>=P_o, and mu_a<=s_a implies that waiting and receiving
the original continuation is worth at most s_a+P_o. Thus a also
obeys the punishment-vector comparison. The sure-quitter criterion
contradicts the original no-UE assumption. This exhausts the odds
homotopy, including escape with just one active owner in the limit.

## An exact comparison with the earlier producers

Take s_i=1 for all i, a=1, b=2, h=0, k=3, and

    Gamma=[0,-1,-1,5; -5,0,2,-1; -2,4,0,-5; 3,-4,2,0].

Use the common proportional additive completion with factor one,
except for these four finite native entries of recipient 0:

    Z0(01)=41,    Z0(013)=36,    Z0(23)=164,    Z0(123)=163.

The other free recipient could be changed arbitrarily as well in the
theorem. At this particular instance the native passive and forced
offers of 0, writing (x,y,z) for hazards of players (1,2,3), are

    b0=-x-y+5z,     P0=b0+160yz,    Q0=-b0+40x(1-y).

Thus P0+Q0>=0. Every player guarantees native zero against any
opponent schedule by using constant hazard 1/2: each reached date's
expected native absorbing contribution is nonnegative. The original
punishment values equal the own levels since all-Never opponents
give the converse bound. The three unchanged rows have the usual box
signs on their singleton sums (nonnegative at quiet players, zero
at proper players, nonpositive at sure players) both in stationary
Nash and in any punishment-vector Nash head with a sure quitter.
For the latter assertion every owner facing a sure opponent compares
the two immediate offers, and a sole sure owner compares to its
native zero punishment continuation.

Here is an exact census with t the hazard of player 0. To reproduce it,
partition 1,2,3 into sure S, proper A and quiet. For the 27 partitions
solve Gamma_AA q_A=-Gamma_A0 t-Gamma_AS 1, then impose the two weak
box signs and 0<=q_A<=1. For a one-element A, the equation fixes t
with one remaining free variable; the larger active blocks are
invertible. Endpoints with identical statuses can be included twice.

| t | (x,y,z) |
| --- | --- |
| 0 | (0,y,0), 0<=y<=1 |
| [0,2/5] | (0,1,0) |
| [0,2/5] | (t/2,5t/2,0) |
| 2/5 | (x,1,0), 0<=x<=1/5 |
| [0,4/13] | (19t/8,13t/4,3t/2) |
| [1/5,4/13] | (3t/4+1/2,1,2-5t) |
| [2/3,1] | (1,2-3t/2,4/5-2t/5) |
| [1/5,2/3] | (1,1,1) |
| 1/5 | (x,1,1), 13/20<=x<=1 |
| 2/3 | (1,1,z), 8/15<=z<=1 |

When z=0 and the vector is nonzero, t<1 and P0=b0<0<Q0.
Player 0 strictly prefers quitting against a stationary calendar,
and against a sure opponent if one is present. When z>0 and any of
1,2,3 is sure, the table gives t>0, b0>0, and either y=1 or
y>=1/2, z>=2/5. Then Q0<P0, inconsistent with positive t since a
sure opponent ends the game. On the remaining all-proper ray t<1
and b0=15t/8>0. Write H=(1-x)(1-y)(1-z). As
1-H<=57t/8 and (1-H)x<4yz, one has
P0-(1-H)Q0>0, contradicting stationary mixing. AllNever fails since
the own levels are positive. These comparisons rule out all stationary
exact equilibria and every sure-quitter punishment head. A stationary
vanishing-regret sequence is also impossible. A nonzero limiting
hazard gives absorbing native Nash by continuity of every finite
deadline. At the zero-hazard limit normalize the four hazards by
their sum. The first-order singleton equations give a homogeneous
complementary vector for Gamma, contrary to R0. Details of these two
compactness steps are in the
[stationary-limit calculation](NONMATCHING_PAIR_LIMIT_RETURN_UNIFORM_EQUILIBRIUM.md#every-fixed-upper-bound-on-the-period-fails);
the new bounded nonsingleton rewards change only the quadratic error.

The earlier [two-disjoint-pair odds](TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md)
and their [generalized opposite-phase comparison](ALL_PROPORTIONAL_ADDITIVE_FOUR_PLAYER_UNIFORM_EQUILIBRIUM.md#a-matching-of-two-pairs)
also fail on this example. On 01|23 and 03|12 the mate premium
already fails (respectively in row 3 and row 1). On 02|13 the odds
equations use only the singleton entries, mate premiums and passive
opposite pair rewards; all remain unchanged. Its vertex cap in row 0
would need lambda>=41 from singleton 1 and lambda<=1 from singleton 3.
Indeed every nonzero complementary odds root itself fails an actual
incentive, as the following calculation shows.

Write X_i for the disjoint-pair odds and K_i for the native passive
opposite-pair reward. With mate m and opposite j,k, each old root obeys

    Gamma_ij X_j+Gamma_ik X_k+K_i X_j X_k >= (-Gamma_im) X_m.

This follows from the old root equation because the additive matched
premium Pi_i=-Gamma_im>0 and c_i=-2 Gamma_im. Row 3 gives X1<=1:
if X1>1 every group in the required inequality

    (8X1-3)X0+(8X1-2)X2+(8X1-5)X0X2+X1[8-4/(1+X1)]<=0

is nonnegative and the last is positive. Rows 0,2,1 then give
X1+X2<=9X3, 5X3+2X0<=4X1, X3<=2X2. Consequently X1,X2,X3>0
at every nonzero root. If X0=0, the equalities in active rows 1,3
give X3>=X2/(1+X2) and X1<=X2/[2(1+2X2)], contradicting
5X3<=4X1. Thus all four are active. In phase 13 the prescribed
payoff of 0 is W0=2X2<=62X1/5<=124q1/5, since X1<=2q1.
Its passive singleton sum 5q3-q1 is at most 7q1 by 5X3<=4X1.
Its actual forced offer in that phase is -(5q3-q1)+40q1, exceeding
W0 by at least (41/5)q1>0. This excludes the complete old root menu.
All four proper triple inverse comparisons depend only on Gamma and
are excluded by the exact calculation in the
[proportional calibration](ALL_PROPORTIONAL_ADDITIVE_FOUR_PLAYER_UNIFORM_EQUILIBRIUM.md#an-exact-test-against-the-previous-producers).
The theorem above supplies a uniform payoff on this nonproportional
table, as well as on the full two-free-row class.

In fact every ordinary period-two equilibrium that assigns a pair and its
complement to separate dates fails on this table. A sure hazard would give
a sure-quitter punishment head, already excluded. Proper mixers have
nonnegative native values at each reached phase by the constant-hazard
security policy above. On 03|12 the forced offer of either partner against
the other is strictly negative whenever its mate plays. Thus each phase
has at most one mover. If distinct owners i,j alternate alone, indifference
sets i's value at its own phase to zero and requires the other phase to
deliver zero. That phase delivers q_j Gamma_ij, which is nonzero. With
only one recurring mover, an outsider who dislikes that singleton can
quit alone at the blank date and improve.

On 01|23 the forced offer of 3 against a positive 2 is negative. If
0 and 1 both mix on the first date, 0 earns U0=41q1 there and requires
W0=42q1/(1-q1)>U0 on the second. A blank date or 2 alone delivers at
most U0. If 3 alone moves, player 1 requires W1=10q0/(1-q0)>U1=5q0
and receives at most U1. The remaining configurations reduce to the two
solo dates just treated. On 02|13 any proper periodic Nash with at least
two effective owners satisfies the odds comparisons above. Indeed the
two-phase value equations give the sign of C_o-Q_o as the sign of
P_p+H_p Q_o-(Q_o-P_o)/H_o, with equality at each positive hazard. This
is exactly the scheduled comparison defining the disjoint-pair odds
system. The failed passive offer thus excludes this last partition as
well. The comparison covers the three partitions into two pairs.

There are also direct obstructions to the earlier support and weight tests.
On support {1,2,3} at odds (1,1/2,3), the three forced-Quit numerators
are (1/2,14,4), and the signed determinant of the joining-gap Jacobian is
1200. This violates both the low and negative-orientation tests. The
singleton charge at {3} is 1+5=6, so this same support cannot be assigned
a charge. On coalition {1,2} the four native rewards are (-2,-2,-4,-2),
excluding every nonzero nonnegative weight with nonnegative reward on all
proper coalitions. The joining-gap vectors for the outside players on
{1,2} and {0,3} are respectively (4,0,0,4) and (0,12,14,0).
A nonnegative weight whose joining-gap sum is nonpositive on every
coalition must therefore vanish. This rules out the support-filtered
weight test even if either pair is exempt from its reward comparison.
[Support comparisons](SUPPORTWISE_NEGATIVE_ORIENTATION_UNIFORM_EQUILIBRIUM.md)
and [weighted tests](SUPPORT_FILTERED_WEIGHTED_LEDGERS_UNIFORM_EQUILIBRIUM.md).
