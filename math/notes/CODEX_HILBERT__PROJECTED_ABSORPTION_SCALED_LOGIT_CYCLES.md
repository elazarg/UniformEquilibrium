# Projected absorption-scaled logit cycles: a global test and its boundary

Identity: CODEX_HILBERT. Ordinary mathematics, not independently reviewed or
Lean-checked. No export claim.

**Outcome.** A finite-dimensional global fixed-point construction supplies
free punishment-floor annotations and absorption-scaled error estimates. Its
maximum-absorption selector escapes the existing SIGN fixed-prefix trap.
However, continuation of the known VANISH three-cycle through this particular
logit construction is impossible. No arbitrary-table weighted-packet
producer, or universal obstruction to one, is proved. This tranche stops at
that specific selection boundary.

## 1. Model and the actual candidate selection

There are four players, |r_i(S)|≤M for every nonempty quitting coalition,
M>0, and Never payoff zero. Complete behavioral laws and all unilateral
replacements are allowed. P_i is the infimum, over independent opponent
laws, of player i's unrestricted response cap. Thus P_i∈[−M,M].

For a product root q, put c(q)=∏_i(1−q_i), a(q)=1−c(q), and let Q_i(q)
and C_i(q,y) be its Quit and Continue endpoints against y. Write

    F_i(q,y)=q_iQ_i(q)+(1−q_i)C_i(q,y),
    A_i(q,y)=max(Q_i(q),C_i(q,y)),
    Reg_i(q,y)=A_i(q,y)−F_i(q,y).

Fix a period H≥1 and parameters κ,δ>0. On the finite-dimensional compact
convex domain

    q_t∈[0,1]⁴,       y_t∈∏_i[P_i,M],       t∈ℤ/Hℤ,

define θ_t=κ(a(q_t)+δ), and the simultaneous map

    q′_(t,i)=1/[1+exp((C_i(q_t,y_(t+1))−Q_i(q_t))/θ_t)],
    y′_t(i)=max(P_i,F_i(q_t,y_(t+1))).                (1)

Indices here are chronological; reverse them when reading a forward packet.
The map is continuous and maps this ONE reward-bounded box into itself.
Brouwer gives a fixed point. All its probabilities are strictly between zero
and one, so all row absorptions are positive for fixed κ,δ,H.

This is a logit fixed-point equation with a temperature evaluated at the
fixed point. It is not asserted to be Nash in a game where a player's
choice changes its own temperature and is differentiated through it.

The specified global selector is: among ALL fixed points of (1), maximize
min_t a(q_t). The fixed-point set is nonempty and closed in the displayed
compact domain, and the objective is continuous. Hence this maximum is
attained for every fixed finite H,κ,δ. Compactness is asserted at fixed H,
not for the union over periods. The reward box does not depend on H.

No source law, starting minimum point, prescribed tail, or cross-accuracy
compatibility is imposed. This is genuinely a joint search over every phase
annotation and every root coordinate.

## 2. What the fixed point gives without a charge assumption

First, for EVERY root q and y≥P,

    A_i(q,y)≥P_i.                                   (2)

For completeness, let α be i's opponent-Continue probability and L its
one-stage reward from nonempty opponent absorption while i Continues.
If α=1, C_i(q,y)=y_i≥P_i. If α<1, stationary opponents with this same
row have unrestricted cap max(Q_i,L/(1−α)), which is at least P_i by
the definition of punishment. Thus either Q_i≥P_i or
L+αy_i≥(1−α)P_i+αy_i≥P_i. This includes signed rewards and uses no
joint realization of the four separate punishment caps.

At a fixed point of (1), the elementary binary-entropy comparison gives

    Reg_i(q_t,y_(t+1))≤θ_t log 2.                    (3)

Indeed, its q_i maximizes the fixed-temperature expression
xQ_i+(1−x)C_i+θ_t[−x log x−(1−x)log(1−x)]. Comparing with a best pure
action proves (3). Because of (2), floor projection costs at most that regret:

    0≤y_t(i)−F_i(q_t,y_(t+1))
      =(P_i−F_i(q_t,y_(t+1)))_+≤Reg_i≤θ_t log 2.      (4)

Consequently the box and punishment floors are exact, and both required
weighted errors satisfy

    error_t/a(q_t)≤κ log 2 · [1+δ/a(q_t)].           (5)

There is no factor H. If a selected fixed point has min_t a(q_t)≥δ and
κ≤ε/2, it is a cyclic weighted packet of tolerance ε; repetition gives
every requested finite charge. The repeated roots themselves are NOT
asserted to be terminal approximate Nash. The weighted repair/forward
consumer performs a further construction and tests unrestricted deviations.

The genuinely missing producer implication is that, for every small κ,
some finite H and δ allow selection with δ/a(q_t) suitably controlled.
Brouwer and fixed-H maximization do not prove this. Their elementary uniform
lower bounds on root probabilities can be exponentially small in 1/(κδ),
far smaller than δ. Positive absorption at each fixed δ is insufficient.

The source overlap is explicit: the ordinary fixed-temperature soft cyclic
Brouwer construction is already in
`CODEX_SPINOZA__ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md`. The changes tested
here are floor projection and the endogenous absorption-scaled temperature,
using the new permission for weighted Bellman errors. Neither change alone
is a positive-charge selection theorem.

## 3. The global selector escapes the SIGN fixed-prefix trap

Use the already recorded table r_i(S)=2−1[i∈S]. Here P_i=1: Quit now
guarantees 1, and all-Never opponents have cap 1. Its trapped actual prefix
has u_i=11/8 and b_i=15/8, but those annotations are NOT imposed in (1).

Consider H=1. For any root with a>0, its stationary prescribed payoff is

    y_i(q)=2−q_i/a∈[1,2].                           (6)

It is an exact Bellman fixed point, so projection is inactive. The root
endpoint gap against (6) is

    C_i(q,y(q))−Q_i(q)=(1−α_i(q))/a.

The logit map after substituting (6) is therefore

    L_i(q)=1/[1+exp((1−α_i)/(κa(a+δ)))].             (7)

Choose player 0 as the distinguished owner and set η=exp(−1/(6κ)). For
sufficiently small κ, 27η/κ≤log 2. For every δ∈(0,1], map (7) preserves
the compact rectangle

    1/3≤q_0≤1/2,          0≤q_1,q_2,q_3≤η.

Indeed a≥1/3. For j≠0, 1−α_j≥q_0≥1/3 and
κa(a+δ)≤2κ, hence L_j≤η. For 0,
1−α_0≤3η and κa(a+δ)≥κ/9, so the exponent is between zero and
27η/κ≤log 2. Thus 1/3≤L_0≤1/2.

Brouwer on this rectangle proves an actual fixed point of (1), with
absorption at least 1/3. This is an asymmetric construction, not an average
of equilibria or empirical histories. In particular, for δ≤1/3 the GLOBAL
maximum-absorption selector at H=1 also has a≥1/3≥δ. Equations (3)–(5)
then give all-accuracy, arbitrary-charge weighted packets for this table.

As κ→0, this branch has q_0→1/2, q_j→0 for j≠0, and annotations tending
to (1,2,2,2). It leaves the old fixed-prefix restriction, whose caps were
bounded below by 15/8 in every coordinate. Thus the new freedom is used
substantively. This table's equilibrium existence was already known; the
result tests this actual selector rather than producing a new UE class.

The distinction from direct equilibrium selection matters: at each positive
κ all opponent hazards are positive. Player 0 can obtain 2 by Never, whereas
its stationary prescribed payoff tends to 1. Thus those stationary laws
have nonvanishing unrestricted player-0 debt. The weighted packet consumer,
not a claim that the stationary laws are approximately Nash, is the valid
route to equilibrium.

## 4. VANISH: continuation of its known three-cycle fails

Use the complete table in the second response of `gpt/VANISH.md`. Player 0
receives 1 when in the terminal coalition and 2 otherwise. For i∈{1,2,3},
with cyclic predecessor i⁻ and successor i⁺, set

    r_i(S)=0                              if i∈S,
           −1                             if i∉S and 0∈S,
           2·1[i⁻∈S]−1[i⁺∈S]             otherwise.

Its punishment vector is P=(1,0,0,0): the own Quit action guarantees the
listed coordinate, and all-Never opponents give the matching upper bound.
The known exact chronological three-cycle has roots

    q^A=(0,1/2,0,0),
    q^B=(0,0,1/2,0),
    q^C=(0,0,0,1/2),

and annotations

    y^A=(2,0,1,0),    y^B=(2,0,0,1),    y^C=(2,1,0,0).

Here y^A=F(q^A,y^B), and cyclically. These are exact Nash roots; some
unused Quit actions are weakly, not strictly, inferior.

**Proposition.** There is no sequence of H=3 fixed points of (1), with
κ_n→0 and 0<δ_n≤1, whose roots converge to this three-cycle. The
perturbations may be fully nonsymmetric across players and phases.

If such roots converged, their annotations would converge to the displayed
ones. To justify this without assuming it, take a compact subsequential
limit. The projected Bellman map on one full period has contraction factor
∏_t c(q^t)=1/8 at the limiting roots. Therefore its periodic annotations
are unique, and the displayed ones are that fixed point.

Write θ_A=κ(a(q^A)+δ) and similarly for B. Both absorptions tend to 1/2,
so θ_A→0 and θ_B/θ_A→1. All following quantities are along the alleged
sequence. Since Q_1=0 and q^A_1→1/2, the logit identity gives

    C_1(q^A,y^B)/θ_A
      =log((1−q^A_1)/q^A_1)→0.                     (8)

But q^B_1→0, so C_1(q^B,y^C)>0 eventually. Projection at coordinate 1,
whose floor is zero, is then inactive. The phase-B equations give

    y^B_1/θ_B
      =(1−q^B_1)log((1−q^B_1)/q^B_1)→+∞.           (9)

At phase A, player 2 has limiting Continue advantage 1 over Quit, and
player 0 also has limiting Continue advantage 1. Therefore, eventually,

    q^A_2≤exp(−1/(2θ_A)),
    q^A_0≤exp(−1/(2θ_A)).

The exact player-1 endpoint at phase A is

    C_1=−q^A_0+(1−q^A_0)
       [2q^A_3−q^A_2+(1−q^A_2)(1−q^A_3)y^B_1].

Dropping the nonnegative 2q^A_3 term yields

    C_1/θ_A≥−(q^A_0+q^A_2)/θ_A
       +(1−q^A_0)(1−q^A_2)(1−q^A_3)y^B_1/θ_A→+∞,

using (9) and θ_B/θ_A→1. This contradicts (8).

The failed implication is specifically “continue this exact cycle into
nearby full-support logit fixed points.” A vanishing probability assigned
to a weakly unused action requires its Continue gap divided by temperature
to diverge. Its Bellman value is then too large relative to the preceding
mixed owner's comparable temperature. The proof uses full-support logit
odds and comparable neighboring temperatures. Floor projection is NOT the
cause: it is inactive at the coordinate producing (9), and the same
contradiction applies with an exact unprojected Bellman equation there.

This does not exclude other H=3 components, different periods, nonsymmetric
global selectors, non-logit constructions, or the anchor-free WP producer.
No broader regularization family is investigated here.

## 5. Source boundary and stopping point

The narrow checked-source comparison used
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge` in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`;
its proof supplies the endpoint argument underlying (2), independently of
the new projection. The output specification is the frozen
`exports/ABSORPTION_WEIGHTED_FORWARD_PACKET_REDUCTION.md`.

The older `CODEX_CEDAR__ERGODIC_NASH_BELLMAN_RECURRENCE.md` already explains
why merely assuming positive invariant mean or growing exact charge is not
a producer. The common-temperature soft-cycle existence and its escaping
branches are recorded in the SPINOZA notes cited above and
`CODEX_SPINOZA__GROWING_PERIOD_HAZARD_CLOCK_AND_REPLICATOR_BOUNDARY.md`.
Those are relevant boundaries, not universal impossibility results for the
present free-annotation weighted specification.

The two whole-law notes
`CODEX_FRECHET_CYCLE__WHOLE_LAW_LOGIT_CANONICAL_BOUNDARY.md` and
`CODEX_FRECHET_CYCLE__TIME_PRIOR_LOGIT_GEOMETRIC_PRODUCER.md` were also read
in full. They already prove that exponentially suppressed strict mistakes
cannot generate certain finite odds between weakly tied stopping dates, and
that altered fixed time priors repair one different geometric fixture.
Their equations concern whole stopping-law probabilities on finite menus,
not cyclic root hazards with free projected annotations. Thus Section 4 is
a specific root/Bellman counterpart of an ALREADY KNOWN entropy-odds
selection obstruction, not discovery of a new general obstruction. No
priority or new game-class coverage is claimed.

The strongest general result here is the unconditional finite-dimensional
system (1) with (3)–(5). The outstanding selection estimate δ/a is unproved.
SIGN supplies a successful exact test; VANISH blocks the most direct local
continuation route to proving that estimate. No new general producer was
identified. A future attempt would need a genuinely global component
selection argument, not additional local temperature tuning.
