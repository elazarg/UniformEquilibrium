# Graph-free H/J and proper-flat uniform equilibrium for four players

Author: CODEX_TURING_BOX. Status: ordinary UNREVIEWED complete proof
candidate, frozen for independent mathematical review. This is not an
export, a Lean implementation, or a claim about arbitrary Fin4 tables.
The named checked declarations below supply the semantic infrastructure;
the raw-class argument, finite escape and paid prefix are ordinary math.

## 1. Exact raw-data theorem

Let I have exactly four players. For every nonempty coalition S subset I
let r(S) be an arbitrary finite real reward vector. At the first date
when someone quits, the nonempty set S of simultaneous quitters fixes
the absorbing payoff r(S). Live play and perpetual nontermination pay0.
Players observe the quitting-game history, use independent private
randomization, and have unrestricted behavioral strategies. A deviation
replaces ONE player's complete behavioral law, without restrictions on
its calendar, memory, stopping date or literal Never choice. No public
randomization or correlation device is introduced.

Put s_i=r_i({i}). Suppose s_i>=0 and there are weights a_i>=0, not all0,
such that EVERY nonempty proper coalition S satisfies

    H(S):=sum_i a_i[r_i(S)-s_i]>=0,
    J(S):=sum_(i notin S) a_i[r_i(S union{i})-r_i(S)]<=0.      (1)

Suppose also that EVERY nonempty proper A contains a participant i in A
such that

    r_i(S)<=s_i for EVERY nonempty S subset A containing i.  (2)

THEOREM CANDIDATE. The original game has a uniform-equilibrium payoff
against all unrestricted behavioral deviations. In particular ONE
target v is selected before accuracy: every delta>0 has an actual
independent private profile and a horizon threshold after which payoff
delivery approximates v and the full unilateral-deviation inequalities
hold with accuracy delta, at ALL later finite horizons.

There is NO strictness assumption on H, NO insertion-graph assumption,
and NO strategic input. The rewards and weights are the only inputs;
(1),(2) are finite raw-table comparisons. Own singletons can be0, weights
can vanish, and no fixed universal reward bound or normalization is used.
The H/J and proper-flat conditions remain genuine restrictions: this
does NOT decide arbitrary Fin4 UE.

## 2. Actual full-cap carrier and exact arbitrary-root calculus

Before absorption the only public active history is repeated all
Continue. Thus an independent behavioral profile induces independent
private deadline laws on natural dates plus literal Never. Conversely
these laws are executable by behavioral strategies. Any one-player
replacement is another such law, and its terminal payoff is affine in
that law. The supremum over unrestricted replacements therefore equals
the supremum over ALL finite pure deadlines and Never. This equivalence
does not truncate the deviator's calendar or require an attained optimum.

For an actual profile write U_i for its terminal payoff and B_i for that
FULL unrestricted response supremum. Let K be the closure of ALL actual
pairs (U,B), not of a chosen family or root spine. Every coordinate lies
in[-M,M] for any finite M bounding all rewards and0. Thus K is compact,
nonempty, and retains B_i>=U_i. A closure point is not declared actual.
Put

    d_i=B_i-U_i,       E=max_i d_i,
    L(B)=sum_i a_i(B_i-s_i).

Fix any product root q in[0,1]^I. For player i let A be its independent
opponent quitter set, and define

    c=product_i(1-q_i),       alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(A union{i})],
    b_i=E[r_i(A) 1_(A nonempty)],
    C_i=b_i+alpha_i B_i,      g_i=Q_i-C_i,
    Delta_i=q_i(-g_i)_+ +(1-q_i)(g_i)_+.

The endpoint Q_i forces Quit at the new root; C_i forces Continue and
then permits the ENTIRE old best response if all opponents Continue.
Allowing a supremum rather than a maximum causes no error in this split.
The exact semantic prefix map is

    U_i'=q_i Q_i+(1-q_i)(b_i+alpha_i U_i),
    B_i'=max(Q_i,C_i).                                      (3)

It is continuous in(U,B) for fixed q and preserves K: actual prefixing
preserves the actual set, and continuity then preserves its closure.
Choosing q after a carrier point is fixed is legitimate; no continuous
selector of q over K is needed.

Subtracting the two coordinates and using (1-q_i)alpha_i=c gives

    B_i'=q_i Q_i+(1-q_i)C_i+Delta_i,
    d_i'=c d_i+Delta_i,
    E'<=c E+Delta_max,       Delta_max=max_i Delta_i.         (4)

If q has proper support, every nonempty root coalition is proper.
The expected payoff at continuation B is
cB+sum_(S nonempty)p_q(S)r(S). Weighted summation of (4) therefore gives
the EXACT arbitrary-root ledger

    L(B')=c L(B)+sum_(S nonempty)p_q(S)H(S)
                         +sum_i a_i Delta_i.                (5)

Equations(3)--(5) include every early, simultaneous, intervening, late
and Never response. They do not assume root Nash. A FULL cap-Nash root
means a mixed Nash equilibrium of the finite Boolean game whose
all-Continue vector is B and whose absorbing rewards are r(S). Nash
optimality is equivalent to Delta_i=0 for EVERY player, including
players with q_i=0. At such a root, (4) gives d'=c d and E'=cE exactly.

## 3. Strict-seed intermediate chamber and Nash preservation

For now assume H({j})>0 for at least one j. Prescribe sure Quit at date0
to j and Never to everyone else. This ACTUAL profile has

    U_i=r_i({j}),       B_j=s_j,
    B_i=max(r_i({j}),r_i({i,j})) for i!=j.                   (6)

The owner can get s_j by any finite deadline and0 by Never, so s_j>=0
gives its exact cap. Another player can Quit0 for the pair reward or
wait for the passive singleton reward; no later response is omitted.
Since B>=U and a>=0, L(B)>=H({j})>0, and B_j=s_j. If E=0, K already
contains a diagonal. Otherwise fix lambda=L(B)/E>0 and the nonempty
compact chamber

    C={(U,B) in K: min_i(B_i-s_i)<=0, L(B)>=lambda E}.       (7)

This lambda is fixed from the raw-data seed. The objective is maximum
debt E on C, not total debt, nor E on the unconstrained carrier.

At any positive-E point in C, EVERY full cap-Nash root either gives a
diagonal or preserves C with E'=cE. First, if some q_i=1 then c=0 and
(4) gives a diagonal immediately. Otherwise suppose all q_i>0. All
rates are interior, hence g_i=0. With z_i=q_i/(1-q_i)>0 and
z_A=product_(j in A)z_j, divide endpoint indifference by alpha_i to get

    B_i-s_i=sum_(empty!=A subset I\{i}) z_A
                       [r_i(A union{i})-r_i(A)].

Summing with weights and regrouping by A yields

    L(B)=sum_(empty!=S proper) z_S J(S)<=0,                 (8)

contrary to L(B)>=lambda E>0. Thus any remaining full root has proper
support D. If D is nonempty, (2) supplies i in D with Q_i<=s_i:
every forced-Quit coalition is a subset of D containing i. Supported
Nash optimality gives B_i'=Q_i, preserving the low face. Equations
(4),(5) and H>=0 give E'=cE and L(B')>=cL(B)>=lambda E'.
All Continue fixes the input. This proves the preservation assertion.
No preservation property of arbitrary non-Nash roots has been assumed.

## 4. Full finite-root escape from sinks and universal recipients

Define h_ij=r_i({i,j})-r_i({j}) for distinct i,j, and draw j->i exactly
when h_ij>0. Suppose B>=s and its tied set T={i:B_i=s_i} is nonempty.

LEMMA. If the induced graph on T has a sink or a universal recipient,
there is a nonzero FULL original cap-Nash root. A sink has no outgoing
arrow within T; a universal recipient receives a STRICT positive arrow
from every other vertex of T, without any outgoing-arrow requirement.

For a sink i, let only i quit with probability p>0. Player i is
indifferent. For every j!=i,

    Continue_j-Quit_j
      =(1-p)(B_j-s_j)+p[r_j({i})-r_j({i,j})].               (9)

This is nonnegative on T by the sink property, and outside T for all
sufficiently small p>0 by the strict margin B_j>s_j. Finiteness keeps
all outside inequalities simultaneously. This is a FULL root.

For a universal recipient i, suppose all Continue is the only original
full Nash root. Add epsilon>0 to i's payoff when IT chooses Quit in the
finite Boolean game, and choose any perturbed Nash root q^epsilon.
Finite mixed Nash existence applies. Compactness and the closed Nash
inequalities imply q^epsilon->0 as epsilon->0: otherwise a subsequence
would have a nonzero original Nash limit. Every player outside T has
g_j(0)=s_j-B_j<0; continuity and Nash therefore force q_j^epsilon=0
for all small epsilon.

On the remaining tied coordinates, finite expansion gives

    g_i(q)=sum_(j in T\{i}) h_ij q_j+O(t^2),
    t=sum_(j in T\{i})q_j.

All listed h_ij are positive. If T\{i} is nonempty, the linear term is
at least h*t for h=min_j h_ij>0 and dominates the bounded quadratic
remainder near0. If T={i}, g_i=0 exactly. In either case the perturbed
gap g_i+epsilon is positive near0. Nash forces q_i^epsilon=1, a
contradiction. The ORIGINAL game has a nonzero full root. No nonzero
limit of perturbed roots or continuous Nash selector is asserted.

Sets of size at most2 always have a sink or universal recipient. For
three vertices, absence of a sink means every outdegree is at least1;
absence of a universal recipient means every indegree is at most1.
There are exactly three arrows and every degree is1, hence the graph
is EXACTLY a bare directed triangle. Conversely a bare triangle has
neither special vertex. Zero and negative differences are absent arrows.

## 5. Bare triangles: positive forward product gives a distant root

Suppose the tied set T is a bare proper triple. Cyclically label its
unique cycle0->1->2->0 and write

    h=[[0,-n_0,p_0],[p_1,0,-n_1],[-n_2,p_2,0]],
    p_0=h_02>0, p_1=h_10>0, p_2=h_21>0,
    n_0=-h_01>=0, n_1=-h_12>=0, n_2=-h_20>=0,
    P=p_0 p_1 p_2>0,       N=n_0 n_1 n_2>=0.

The products do not depend on the starting vertex of the cyclic label.
LEMMA. If P>N, the FULL original game has a nonzero cap-Nash root.
This finite lemma needs neither H/J nor flatness.

There is a positive vector w with w-transpose*h positive in EVERY
column. Explicitly choose eta>0 so product_i(n_i+eta)<P, then sigma>1
so sigma^2 product_i(n_i+eta)<P, and take

    w_0=1,       w_2=sigma(n_0+eta)/p_2,
    w_1=sigma(n_2+eta)w_2/p_1.

These satisfy w_1 p_1>w_2 n_2, w_2 p_2>w_0 n_0 and
w_0 p_0>w_1 n_1. Zero reverse coefficients cause no problem.

Suppose again all Continue is the only full original root. Add epsilon
to the Quit action payoff of EVERY tied player and select any perturbed
finite Nash root. The same compact closed-graph argument gives
q^epsilon->0; the strict outside cap margin forces the fourth rate0
for small epsilon. Set t=sum_(i in T)q_i. At B_i=s_i on T, expansion
g=hq+O(t^2) and strict column positivity give finite mu>0,K with

    sum_(i in T) w_i g_i >= mu*t-K*t^2 >=0

near0. Adding epsilon sum_i w_i makes the perturbed weighted gap
strictly positive. Some tied player strictly prefers Quit and hence
has rate1, contradicting q^epsilon->0. Thus a nonzero ORIGINAL full
root exists. As in Section4, the argument finds a distant root by
contradiction, not a favorable perturbation limit.

## 6. Bare triangles: reverse product gives a paid non-Nash prefix

LEMMA. Suppose (U,B) is a positive-E point of C, B>=s, its tied set T
is a bare proper triple, N>=P, and H({j})>0 for some j in T. Then a
FIXED independent prefix supported on T gives another point of C
with strictly smaller E. The fourth player's full cap is retained.

Choose a flat participant of T by (2), and cyclically relabel it0.
Since N>=P>0, ALL n_i>0. Set

    z_1=1,       z_2=n_0/p_0,
    p_2/n_2 <= z_0 <= n_1 n_0/(p_1 p_0).                  (10)

The interval is nonempty exactly when N>=P; its endpoints are positive.
Thus z>0, h z<=0, and (h z)_0=0. Equality N=P is included and makes
all three linear gaps0. Let k be the fourth player. With q_k=0, the
flat player's EXACT tied gap is

    g_0=-n_0 q_1+p_0 q_2+kappa q_1 q_2,
    kappa=r_0(T)-r_0({1,2})+n_0-p_0.

For sufficiently small tau>0 choose

    q_0=tau z_0,       q_1=tau z_1,
    q_2=n_0 q_1/(p_0+kappa q_1),       q_k=0.             (11)

The denominator stays positive since p_0>0. All three rates lie in
(0,1), q_i=tau z_i+O(tau^2), and substitution gives g_0=0 EXACTLY.
Every coalition in Q_0 is a subset of T containing0, so flatness gives

    B_0'=Q_0=C_0<=s_0.                                   (12)

This preserves the low face without strict participant inequalities,
strict pair deficits or any second-order sign assumption.

For each tied player i, g_i=tau(hz)_i+O(tau^2). Since hz<=0,
(g_i)_+=O(tau^2), (-g_i)_+=O(tau), and q_i=O(tau). Hence (4) gives
Delta_i=O(tau^2). For the outsider, g_k(0)=s_k-B_k<0, so continuity
gives g_k<0 near0. With q_k=0, Delta_k=0 EXACTLY. In particular the
outsider's ENTIRE debt contracts as d_k'=c d_k, not just one candidate
deviation or one deadline. Its unrestricted future cap is in C_k.

Write Z=sum_(i in T)z_i>0. Finite Taylor expansions and (11) give
K<infinity and tau_0>0 such that, for 0<tau<tau_0,

    Delta_max<=K tau^2,       1-c>=(Z/2)tau,
    p_q({j})>=(z_j/2)tau.

Choose tau still smaller if needed. Equation(4) gives

    E'<=E-(EZ/2)tau+K tau^2<E.

Using (5), H>=0, a>=0 and the SAME fixed lambda from (7),

    L(B')-lambda E'
      >=c[L(B)-lambda E]+p_q({j})H({j})-lambda Delta_max
      >=(z_j H({j})/2)tau-lambda K tau^2>=0.              (13)

The strict singleton H surplus pays the ENTIRE quadratic root defect.
Together(12),(13) preserve C. If E'=0 this already gives a diagonal.
The chosen root is fixed after choosing the point and tau, so (3)
preserves K even if the point is only in its closure. No exact root
Nash, safe child, changed lambda or new continuation source is assumed.

## 7. Complete intermediate producer by compact constrained minimization

Assume the raw guards (1),(2), at least one strict singleton H, and
the following finite graph condition: EVERY bare proper triple either
has P>N or contains a singleton with H({j})>0. In particular this
condition is automatic if TWO different singleton H values are strict,
because every triple meets that two-element set.

Construct the actual seed and chamber (6),(7). If the seed is diagonal
there is nothing more to prove. Otherwise E attains a minimum on C.
Suppose this minimum is positive at(U*,B*).

If some B_i*<s_i, all Continue is not Nash. Finite Nash existence gives
a nonzero full root. Section3 either gives a diagonal or preserves C
with E'=cE*<E*, since a nonzero root has c<1. Either contradicts the
positive minimum. Thus B*>=s.

The tied set T is nonempty by the low face and proper because
L(B*)>=lambda E*>0. It therefore has at most three vertices. A sink
or universal recipient supplies a nonzero full root by Section4 and
the same contraction contradiction. The only remaining graph is a
bare triple. If P>N, Section5 supplies the full root. If N>=P, the
assumed strict singleton in T lets Section6 give a smaller-E point
of the SAME C directly. These cases exhaust all tied sets, including
zero reverse coefficients and product equality. The minimum is0.

The minimizing pair is a diagonal (v,v) in K. By definition of K there
are actual profiles with prescribed payoffs and FULL caps tending
to the SAME v; maximum terminal regret tends to0. The checked diagonal
consumer named in Section10 gives a uniform-equilibrium payoff target v,
selected before accuracy, against unrestricted behavioral deviations.
This does not assert existence of an exact terminal Nash equilibrium.

Zero weights do not alter this proof: no weight is divided by, and a
strict H seed makes lambda>0 regardless of vanishing coordinates.
Own singleton0 is allowed in (6). The only divisions are by p_i>0,
n_i>0 where N>=P>0, and the positive denominator in (11). Constants
and small rates can depend on the table and the minimizing pair; no
game-uniform convergence rate is claimed. The grand-coalition rewards
enter only through the original J guards on triples and full root
inequalities; no new grand-row assumption has been added.

## 8. Passive-singleton perturbation removes strictness and graph guards

Return to ONLY the final raw assumptions (1),(2). Put A_*=sum_i a_i>0.
For every epsilon>0 define

    r_i^epsilon(S)=r_i(S)+epsilon if S={j} with j!=i,
    r_i^epsilon(S)=r_i(S) otherwise.                       (14)

Own singletons are unchanged. Direct sums give

    H^epsilon({j})=H({j})+epsilon(A_*-a_j),
    J^epsilon({j})=J({j})-epsilon(A_*-a_j).

For |S|>=2 both H and J are unchanged. Thus (1) survives. EVERY
participant-flat comparison is unchanged literally: when i in S,
the changed-entry condition S={j},j!=i is impossible. The SAME flat
participant works for each proper A, including every triple.

There is at most one j with A_*-a_j=0. Such equality means all other
weights vanish, so two such equalities would contradict A_*>0. Hence
at least THREE singleton H^epsilon values are strictly positive. The
two-strict corollary in Section7 applies to EVERY r^epsilon, regardless
of its insertion graph. No requirement to preserve that graph or to
bound epsilon by its positive insertion gains is needed.

Every nearby table has a uniform-equilibrium payoff and
|r_i^epsilon(S)-r_i(S)|<=epsilon. Checked reward-closedness named below
therefore yields a uniform-equilibrium payoff for r. The nearby targets
and profiles may vary; no synchronization or convergence of chosen
nearby targets is assumed. This proves the final theorem.

Equivalently, fix ANY profile and reuse the SAME strategy laws at the
two reward tables. The absorption law is reward-independent. Prescribed
terminal payoff changes by at most epsilon, as does EVERY deviating
payoff; taking the full response supremum gives cap distance at most
epsilon. Thus maximum terminal regret changes by at most2epsilon.
Given original accuracy delta>0, take epsilon=delta/4 and an actual
nearby profile with terminal regret at most delta/2 from Section7's
diagonal carrier. At r its terminal regret is at most delta. Terminal
Nash existence at EVERY accuracy then selects ONE original uniform
target via the checked all-errors compiler named below. This alternative
also avoids any matching of targets across nearby reward tables.

In particular ALL singleton H values can originally be0. Their local
non-Nash prefixes need not have a linear payment at that original table;
strictness is introduced only in nearby games and removed by existence
closure. The proof does not assert an unfunded prefix or automatic
quiet-child lift at the original table.

## 9. Exact boundary tests and conjecture-facing scope

The following four-player table, with a_i=s_i=1, satisfies the raw
guards and has a bare triangle0->1->2->0 plus arrow3->0. It tests the
paid-prefix branch at P=N=1. A row label lists the simultaneous quitters;
each reward vector is in player order0,1,2,3.

| S | r(S) |
| --- | --- |
| 0 | (1,-1,1,4) |
| 1 | (1,1,-1,13/4) |
| 2 | (-1,1,1,3) |
| 3 | (2,2,2,1) |
| 01 | (0,0,1,3) |
| 02 | (0,1,0,3) |
| 12 | (1,0,0,3) |
| 03 | (3,2,2,1) |
| 13 | (2,0,2,1) |
| 23 | (2,2,0,1) |
| 012 | (0,0,0,4) |
| 013 | (0,0,3,1) |
| 023 | (0,3,0,1) |
| 123 | (3,0,0,1) |
| 0123 | (0,0,0,0) |

Its singleton H values are(1,1/4,0,3) and singleton J values
(-3,-9/4,-2,-3). Child pairs01,02,12 have H=0,J=-3. Pair03 has
H=4,J=-4; pairs13,23 have H=1,J=-4. Triple012 has H=0,J=-4;
the other triples have H=0,J=-3. For flat participants, take either
member of any child pair, player3 for each pair containing3, player0
for012, and player3 for the other triples. Singletons are tautological.
Every indicated participant has all its participant subrows at most1.

The actual profile with player0 sure Quit1 and others Never gives
U=(1,-1,1,4), B=(1,1,1,4), E=2,L=3. The sure-owner1 seed has E=1,
L=5/4, so this point lies in the same lambda=5/4 chamber, but is NOT
its minimizing point. At its cap, outside player3 always strictly
Continues: its forced-Quit payoff is at most1 and forced-Continue
payoff at least3 for EVERY child root. The child gaps are exactly

    g_0=q_2-q_1-q_1q_2,
    g_1=q_0-q_2-q_0q_2,
    g_2=q_1-q_0-q_0q_1.

All Continue is the only full cap-Nash root: one positive rate gives
an inactive successor a positive gap; two rates give one supported
player a negative gap; with three positive rates the gap sum is minus
the positive sum of pair products, whereas supported Nash requires
every gap nonnegative. Thus flatness alone cannot guarantee nonzero
finite Nash escape in the equality orientation. Section6 instead
uses q_0=tau,q_1=tau,q_2=tau/(1-tau), giving g_0=0 and only quadratic
full-cap defects, with a strict singleton H payment. This is a positive
calibration, not an unrestricted equilibrium exclusion.

For the zero-H boundary, the table r_i(S)=1 for every nonempty S and
every i, with a_i=1, has H=J=0 and all participant-flat comparisons
equalities. It satisfies the FINAL theorem but has no strict original
seed. Perturbation (14) gives H^epsilon({j})=3epsilon and
J^epsilon({j})=-3epsilon, leaving all other guards unchanged. The
unperturbed game already has obvious absorbing equilibria; the example
tests the exact hypothesis removal, not novelty of existence there.

The mathematical increment over the prior independently reviewed
sink-or-receiver chamber is removal of its proper insertion-graph
restriction and its strict-singleton-seed requirement for Fin4. The
table above is outside its graph guard, but is NOT claimed here to
be outside every other implemented existence class. No exhaustive
implementation-coverage or publication-novelty assertion is made.
Any export still requires independent soundness and coverage reviews.

## 10. Named sources inspected and strategic-input audit

The infrastructure below was opened under its actual imports. Its
checked status is not being attributed to the new raw-class theorem.

In `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`:

- `quittingTerminalSemanticCarrier` is the closure of actual payoff/cap
  pairs, not an arbitrary envelope or prescribed root family.
- `exists_terminalProfile_sequence_tendsto_semanticPair` supplies actual
  profiles approximating ANY carrier point.
- `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix` and
  `quittingTerminalSemanticPrefix_mem_carrier` supply compactness,
  continuity and fixed-prefix closure used in Sections2,3,7.

In `UniformEquilibrium/Quitting/Root/NashExistence.lean`,
`exists_isZeroQuittingRootNash` supplies FULL finite root Nash existence
at arbitrary continuation vectors, not only a tied-player subgame.

In `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`,
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect`
is the EXACT arbitrary-root identity (4), without a Nash assumption.
In `UniformEquilibrium/Quitting/Root/NashDefect.lean`,
`quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`
gives the displayed Delta decomposition. No prescribed-payoff Nash
block-action identity is substituted for this cap-defect identity.

In `UniformEquilibrium/Quitting/Root/FirstOrderProductFlow.lean`,
`abs_quittingRootEndpointDifference_sub_solo_sub_tail_sub_collisionFlow_le`
bounds the quadratic endpoint remainder at tied coordinates by4M
times squared total rate. Sections4--6 also derive their needed finite
expansions directly. The exact cap-Nash specializations are
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`.

In `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`,
`isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`
turns Section7's diagonal into the SAME fixed-target uniform payoff
against the full behavioral deviation space. It has no sign, graph,
stationarity or public-correlation premise beyond carrier membership.

In `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`,
`abs_quittingContinuationBestResponseValue_sub_le_of_reward_close`
and `abs_quittingTerminalExploitability_sub_le_of_reward_close` give
the one-epsilon cap and two-epsilon regret bounds. The declaration
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
delegates reward-closedness to
`quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards`
in `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean`.
That declaration uses fixed-skeleton stage-payoff closure and permits
varying nearby targets. The alternative terminal compiler is
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

Bounded symbol/phrase searches in the Root subtree, the named weighted-
trap module and nearby conference notes did not locate a prior theorem
asserting w-transpose*h>0 implies a nonzero full root. This is a bounded
overlap check, not an exhaustive novelty claim. The paid NON-Nash
prefix and its chamber consumer remain the new mechanism even if the
finite weighted escape is available elsewhere.

All strategic witnesses are produced: (6) produces the actual seed;
compactness produces its chamber minimizer; finite Nash existence and
Sections4,5 produce required escaping full roots; (10),(11) produce
the alternative paid prefix; carrier closure and its diagonal consumer
produce actual profiles and a fixed uniform target; (14) and checked
reward closure remove extra strictness. No child equilibrium, supplied
safe lift, response-attaining optimizer, chronology, rate selection or
additional convergence hypothesis remains assumed.

Requested independent adversarial checks: exact identities(4),(5);
the perturbed-full-root contradictions, especially inactive outsiders;
the rational correction and low-face equality(11),(12); the quadratic
defect estimate and payment(13), including P=N; constrained versus
unconstrained minimization; zero weights and own singletons; and every
guard plus fixed-target quantifier in the reward-limit step. This file
is held under notes/ pending those checks and a separate coverage review.
