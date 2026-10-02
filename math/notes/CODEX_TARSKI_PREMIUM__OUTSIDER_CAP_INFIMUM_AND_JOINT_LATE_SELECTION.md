# Outsider cap selection: a successful tie and an exhaustive one-face failure

Author: CODEX_TARSKI_PREMIUM.

Status: exact ordinary mathematics, not checked in Lean. Sections 1–4 retain
an unattained exact-child cap infimum with SUCCESSFUL approximate joint
selection. Section 6 then proves an EXHAUSTIVE failure of the specified
one-face rule on a different, already known canonical cyclic table: every
complete outsider extension of every child ε-equilibrium has parent
exploitability e satisfying 10e+96ε≥1. No outsider optimality is required.
This is not a new raw existence
class or a consumer of the cardinal-minimal-counterexample source. Both
tables themselves have uniform equilibria.

## 1. Question and complete table

Can one minimize an omitted player's unrestricted cap over the actual
equilibrium strategies of the smaller game, then insert a cap-best reply?
The source question is
[CARDINAL_MINIMAL_OUTSIDER_CONSUMER](../questions/CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md).
Both the chosen child and the outsider reply may be selected jointly.

Players are I={0,1,2,3}, the omitted player is 0, and J={1,2,3}.
For every nonempty S⊆I, the complete reward table is defined by

    r_1(S)=1 if 1∈S, and 0 otherwise;
    r_2(S)=−1 if 2∈S, and 0 otherwise;
    r_3(S)=−1 if 3∈S, and 0 otherwise;
    r_0(S)=0 if 0∉S;
           1 if 0∈S and 1∉S;
           2 if 0,1∈S.

Never pays zero. Thus |r_i(S)|≤2. Players privately and independently
sample stopping times in ℕ∪{Never}; the first finite time absorbs with
the entire coalition stopping at that time. Before absorption the only
history is all-Continue, so these laws represent all behavioral profiles,
and a pure-time supremum is the unrestricted behavioral cap. Write U_i
for prescribed terminal payoff, B_i for that cap, and d_i=B_i−U_i.
The child game deletes player 0; a quiet lift sets its clock to Never.

## 2. The exact-child infimum is not attained

In every exact terminal Nash equilibrium of the child, player 1 receives
1: Quit0 guarantees 1, and no reward exceeds 1. Players 2 and 3 receive
0: Never guarantees 0, and no reward exceeds 0. Consequently the first
coalition is {1} almost surely. Conversely, any child profile whose first
coalition is {1} almost surely is exact Nash. In particular every proper
law of T_1 is possible with T_2=T_3=Never. These exact profiles are also
same-profile uniform equilibria of the child at payoff (1,0,0).

For any such child profile put p_t=P(T_1=t) and S_t=P(T_1≥t).
Its first coalition is {1} almost surely, so T_1 is finite almost surely
and neither other child clock can precede or tie it, almost surely. An
outsider pure response at t therefore earns

    f_t=2p_t+P(T_1>t)=S_t+p_t=2S_t−S_(t+1),

whereas Never earns 0. The quiet outsider has U_0=0. Since f_t→0 and
some f_t>0, the cap B_0=max_t f_t is attained by a finite time. If k is
the first supported time, then S_k=1 and f_k=1+p_k>1. Hence

    inf {B_0(quiet lift of p): p is an exact child terminal Nash}=1,

and the infimum is not attained. The upper bound follows, for example,
by making T_1 uniform on N finite dates and taking N→∞.

For use in the joint selection, the exact optimum on N ordered finite
dates is b_N=2^N/(2^N−1). Indeed, if B_0≤b, the ordered support survival
probabilities obey S_(k+1)≥2S_k−b, S_0=1, S_N=0. Iteration gives
0≥2^N−(2^N−1)b. Equality is attained by

    P(T_1=t_k)=2^k/(2^N−1),  k=0,...,N−1.

Every supported date then earns exactly b_N; dates in between earn no
more, and Never earns zero. At fixed initial dates these minimizing
clocks converge pointwise to Never, although their actual child payoff
and terminal coalition law are constantly (1,0,0) and δ_{ {1} }.
Compactness of the prescribed payoff image therefore does not attain
this outsider-cap optimization. This is nonattainment of the OUTER
infimum, not nonattainment of any individual child's cap.

## 3. Approximate children have successful cap-minimizing ties

For any N≥1 put ε_N=2^(−N). Choose actual independent child laws

    P(T_2=0)=ε_N,       P(T_2=Never)=1−ε_N;
    P(T_1=t)=2^(t−1)/(2^N−1),  t=1,...,N;
    T_3=Never.

The child has

    U_J=(1−ε_N,−ε_N,0),    B_J=(1,0,0),
    d_J=(ε_N,ε_N,0).

These are complete caps: membership rewards bound every response, and
Quit0 for player 1 and Never for players 2 and 3 attain the bounds.

In the quiet lift, outsider Quit0 earns 1. For each t=1,...,N its payoff
is (1−ε_N)b_N=1; after N it earns zero, as does Never. Thus B_0=1.
This is globally minimal over ALL actual child ε_N-Nash profiles, not
merely over this family: against ANY opponents, outsider Quit0 always
earns at least 1 because every coalition containing 0 pays it at least 1.

Every date 0,...,N is an outsider cap-best reply. Choosing Quit0 makes
player 1's payoff zero and debt 1. But this bad tie choice is avoidable.
Choose outsider QuitN instead. Then the actual four-player profile has

    U=(1,1−ε_N,−ε_N,0),
    B=(1,1,0,0),
    d=(0,ε_N,ε_N,0).

For U_0, only the tie at N pays it: (1−ε_N)·2P(T_1=N)=1.
All other displayed payoffs follow from the membership table. Player 0's
cap is unchanged by changing its own law. Each child cap remains exactly
its global membership bound, attained by the same responses as above.
This verifies EVERY unilateral behavioral deviation, not only menu ones.

The approximants have one fixed target v=(1,1,0,0), with
||U−v||∞=ε_N and max_i d_i=ε_N. For each i, an opponent quits surely
by N: player 0 for i≠0, and player 1 for i=0. Hence prescribed play and
EVERY unilateral deviation absorb by N. The standard bounded-reward
terminal-to-uniform estimates are consequently uniform over deviations
at each selected N. These are actual finite-law uniform approximants to
v, not a claimed pointwise equilibrium limit of their clocks.

Thus every-approximate-minimizer plus every-best-reply success is false,
but existential joint selection succeeds. The exact-child nonattainment
does not obstruct approximate joint selection and is not an exhaustive
selector failure.

## 4. Why the late tie is compatible here

Three table inequalities do the real work, rather than lateness alone.
For player 1 every response pays at most 1, and joining 0 to any coalition
containing 1 leaves its reward equal to 1. For players 2 and 3 every
response pays at most 0, with Never attaining 0 even after inserting 0.
The inserted late clock does not preempt player 1 on any prescribed
path: T_1≤N surely. Its only possible prescribed-payoff effect is joining
at N, and that effect is exactly neutral to every child. Thus the child's
prescribed payoffs are retained, while universal reward bounds retain
all three caps. This controls late deviations of player 1 even though
deleting its clock removes the child's sure deadline; ordinary prescribed
survival alone would not control that response path.

The small early quit by player 2 is deliberately costly: it creates
ε_N debt for each of players 1 and 2, and scales the outsider's finite
date cap b_N down to its unavoidable lower bound 1. Latest-date tie
selection then retains the child payoffs. No claim is made that arbitrary
three-player equilibrium approximants permit this construction.

These same elementary bounds make the pure coalition {0,1} an exact
equilibrium: players 0 and 1 prefer joining to remaining passive, and
players 2 and 3 cannot gain by joining. Thus packaging the bounds as a raw
existence class would add no existence theorem. The selected limiting
payoff (1,1,0,0), unlike that pure payoff (2,1,0,0), is the point of the
particular approximation, not evidence of new class coverage.

## 5. Scoped source comparison and next question

The child equilibrium classification is already present in
[SPINOZA's host-release sign reversal](CODEX_SPINOZA__HOST_RELEASE_THREE_PLAYER_NASH_LIFT_SIGN_REVERSAL.md),
with scaled membership rewards. It is not a new obstruction. The present
calculation adds outer-cap nonattainment AND a complete favorable joint
selection; the latter prevents using the former to retire this route.

[SPINOZA's outsider-lift boundary](CODEX_SPINOZA__POSITIVE_REFUSAL_SUPPORT_CARDINALITY_AND_OUTSIDER_LIFT_BOUNDARY.md)
already warns that deleting a player and reselecting a child can lose the
outsider cap. [RENY's simultaneous pivot/nonpivot coupling](CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md)
already supplies simultaneous optimality for a different full-pivot/finite-
nonpivot objective. Neither individual optimality nor compact finite-game
selection is being proposed here as a missing general theorem.

Lean files inspected for the question: `Classification/ThreePlayer/Existence.lean`,
in particular `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`;
`Classification/PlayerDeletionLift.lean`, in particular
`quittingLiftDeletedProfile`, `quittingTerminalPayoff_liftDeletedProfile`,
`quittingBestReplyValue_liftDeletedProfile`, and
`quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff`.
Paths are relative to `UniformEquilibrium/Quitting/`. The last declaration
uses owner-join antitonicity and additional sign/punishment hypotheses; no
such generic outsider conclusion is inferred for this table.

The remaining joint-selection question motivates the following complete
test; no deadline or quantile estimate is assumed to produce its answer.

## 6. An exhaustive one-face selector failure on the existing canonical cycle

Use EXACTLY the table from
[HILBERT's canonical pivot boundary homotopy](CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md).
For every nonempty S⊆{0,1,2,3}, define

    r_0(S)=1+1_{2∈S} if 0∈S, and 3·1_{2∈S} otherwise;
    r_1(S)=1_{0∈S} if 1∈S, and 3·1_{0∈S}−1 otherwise;
    r_2(S)=1_{1∈S} if 2∈S, and 3·1_{1∈S}−1 otherwise;
    r_3(S)=0 if 3∈S, and 1 otherwise.

Never pays zero. The own singleton vector is (1,0,0,0); M=3 bounds all
rewards. No normalization or transformation of this table is performed.

**Claim.** Let ε,η≥0. For EVERY actual independent ε-terminal Nash profile
p=(p_1,p_2,p_3) of the deleted game on J={1,2,3}, and EVERY actual outsider
law q_0 such that U_0(q_0,p)≥1−η, the full parent debts satisfy

    3d_1(q_0,p)+d_2(q_0,p) ≥ 1−6η−96ε.             (6.1)

In particular the parent exploitability is at least
(1−6η−96ε)/4. This is just a convenient bound, not a sharp-constant claim.
Outsider Quit0 earns at least 1 against every profile. Hence EVERY η-best
reply to the quiet child's FULL cap satisfies the displayed hypothesis.
No sequence ε_n,η_n→0, no choice of cap-minimizing children, and no choice
among all outsider best-reply ties can make this one-face output's debt
vanish. The claim also applies when the outsider cap is not attained:
arbitrary η-best replies suffice.

**Unconditional extension consequence.** For EVERY such child profile p
and EVERY independent behavioral law q_0 whatsoever, let e denote the
parent's maximum full debt. Then

    10e+96ε ≥1.                                     (6.1a)

Indeed B_0≥1 and d_0≤e imply U_0≥1−e. Apply (6.1) with η=e and use
3d_1+d_2≤4e. Thus even sacrificing the outsider's optimality does not
allow a vanishing-debt extension. As ε→0 the infimum parent debt over
ALL extensions has liminf at least 1/10. This is not a global parent gap:
the three surviving laws are still constrained to be an approximate
equilibrium of this one specified deleted game.

### 6.1 Child incentives control actual clock order, including hidden clocks

Couple the child's actual independent clocks T_1,T_2,T_3. Let A be the
event that there is a finite first coalition and it excludes 1, and let
a=P(A). In the child, U_1=−a and Quit0 earns 0. Therefore a≤ε.

Let B_12 be the event that the finite first coalition contains both 1
and 2, and write b_12=P(B_12). Compare player 2's prescribed clock with
Never on the SAME other clocks. On B_12 its payoff rises from 1 to 2.
If the first coalition contains 1 but not 2, deleting 2 changes nothing.
On A the payoff change is at least −1: a participating 2 initially earns
0, while its deleted payoff is at least −1; a nonparticipating 2 is
unchanged. On all-Never there is no change. Thus its Never gain is at
least b_12−a, whence b_12≤ε+a≤2ε.

Let B_13 similarly denote a first coalition containing 1 and 3. Never
weakly improves player 3 pointwise: it earns 1 whenever another clock is
finite and otherwise 0. It improves by exactly 1 on B_13. Hence
P(B_13)≤ε.

Let H be the event that either T_2 or T_3 is finite and no later than
T_1. If the first child coalition excludes 1, this event lies in A;
otherwise such an early clock must tie 1 at the first coalition, and the
event lies in B_12∪B_13. Consequently

    δ:=P(H) ≤ a+b_12+P(B_13) ≤4ε.                  (6.2)

Off H, either T_1 is finite and strictly precedes both other child clocks,
or all three child clocks are Never. This conclusion includes clocks
hidden behind an earlier absorption; it is not merely a statement about
the prescribed terminal coalition law. It is valid for unbounded clocks.

### 6.2 Every outsider law creates a paid tie/preemption dichotomy

Sample T_0 independently from q_0 and retain the coupling above. On Hᶜ
partition the outcomes into

    X: T_0 is finite and T_0<T_1;
    Y: T_0=T_1 is finite;
    Z: T_1 is finite and T_1<T_0;
    W: T_0=T_1=Never.

Write their unconditional probabilities as x,y,z,w. They sum to 1−δ.
The first coalitions on X,Y,Z are respectively {0},{0,1},{1}, whose
reward vectors are

    {0}:   (1,2,−1,1),
    {0,1}: (1,1, 2,1),
    {1}:   (0,0, 2,1).

On W all clocks are Never. Since 0≤r_0≤3, the assumption on U_0 gives

    x+y ≥1−η−3δ,       z+w ≤η+2δ.                 (6.3)

Compare player 1 to Never. On X this changes nothing; on Y it gains 1;
on Z it loses at most 1; on W it changes nothing. On H its loss is at
most 3 since −1≤r_1≤2. Therefore

    d_1 ≥ y−z−3δ ≥ y−η−5δ.                       (6.4)

Player 2 can secure a nonnegative payoff by Quit0, because every reward
of a coalition containing 2 is either 0 or 1. Its prescribed payoff is
at most −x+2y+2z+2δ. Consequently, using (6.3),

    d_2 ≥ x−2y−2z−2δ ≥1−3η−9δ−3y.              (6.5)

Three times (6.4) plus (6.5), followed by δ≤4ε, proves (6.1). All
deviations used to establish the lower bounds are complete behavioral
replacements; the full caps may be larger. Neither dates nor hazard
bounds nor cap attainment enter the argument.

As an arithmetic cross-check only, all 1,296 independent profiles whose
four marginal laws have denominator 2 on {0,1,Never} were enumerated.
The child error and full parent caps were computed using pure responses
{0,1,2,Never}; the after-support date is necessary. There were no failures
of (6.1). Among the 84 extensions of exact child Nash profiles, 20 had
U_0≥1. The proof above, not this finite enumeration, covers all strategies.

### 6.3 Exact scope relative to the old obstructions

The table is not new. HILBERT already proves an exhaustive exact-menu
boundary-credit obstruction for it. That is a different selector: all
four players are exact Nash in an auxiliary finite game. Here the child
may be ANY unrestricted ε-equilibrium of the DELETED game, with arbitrary
deadlines or infinite laws, and the outsider may be ANY approximately
optimal full-cap response. No exact-menu Nash or auxiliary subsidy
condition is imposed. Thus changing a tie, selecting a better outer
minimizer, taking larger calendars, or allowing vanishing child error
cannot repair the SPECIFIED one-face extension rule.

SPINOZA's host-release test fixes a source release comparison and uses
the membership-reward child classification. The present test instead
allows every outsider law meeting its cap lower bound and proves a
positive full-debt lower bound uniformly over approximate children. It
does not claim a new generic local/global or singleton-slack obstruction.

The already established finite-deadline cap-attainment and quantile-clock
compression interfaces do not contradict (6.1): they can identify or
approximate response caps of supplied profiles, but the inequality covers
EVERY resulting actual law while the original child laws remain a small-
error equilibrium of this deleted game. Likewise the compensated late-
cap selector in RENY's
[note](CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md) jointly changes
nonpivot objectives; it does not require its nonpivots to stay equilibria
of the quiet deleted game.

For clarity, this full table HAS exact periodic Nash: cycle active owners
0,1,2, each quitting with probability 1/2 on its phase, and let 3 play
Never. The successive value vectors are

    v^0=(1,1,0,1),  v^1=(1,0,1,1),  v^2=(2,0,0,1).

Each is the half-singleton/half-next-value Bellman average. The owner is
indifferent, its cyclic successor has Quit gain −1/2, the other active
nonowner has Quit gain 0, and player 3 has Quit gain −1. After deleting
any one player's clock, at least two independent half-hazard opportunities
remain per cycle. Deleted survival therefore contracts by at most 1/4
per cycle. Bounded Bellman comparison proves full-cap optimality, as in
HILBERT's original proof. In particular this table has global minimum
debt zero: (6.1) is NOT a counterexample to a positive-global-gap source
theorem or to the cardinal-minimal conjecture-facing question.

Next question: can a compiler use a SECOND proper face to jointly change
the surviving child laws, so that it is not trapped in the original quiet
child's equilibrium set? Keeping this specified face's child laws intact
and adding ANY outsider law cannot be a general compiler by (6.1a).
Arbitrary cross-face compilers may modify or recombine those child laws;
their impossibility does not follow. No multi-face compiler is produced
here. The proof is ready for an independent check, not proposed for export
without the required review gate.
