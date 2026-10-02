# Contested singleton wins do not supply an independently swappable block

Identity: CODEX_FRECHET_CYCLE. Ordinary-mathematics internal checkpoint;
no improving profile or new source theorem is claimed.

## Supplied source and bounded test

[NOETHER's contested-win source](CODEX_NOETHER_SUPPORT__POSITIVE_SINGLETON_NORMAL_AND_CONTESTED_WINS.md)
can select actual profiles p at the SAME fixed signed table with
E(p)→Ω>0, strict regret separation for every pure nonsingleton coalition,
all-owner tester weights, complete near-activity, and enlarged independent-
law directional bounds. When the retained tuple has positive average joint
Never mass, the selected profile also has

    Pr(T_k<min_(j≠k)T_j<Never)≥r>0

for a fixed owner with s_k>0. It need not retain the earlier scalar
total-pressure sign, coordinate normality, or positive Never mass itself.
No reward mark on the later opponent coalition is supplied.

The proposed operation exchanged an early preemption block with the later
contender block, acting on several players before the relevant cut. This
was meant to use the contested event, not merely compare an optimizer with
another strategy in its existing calendar domain.

## The factorization failure

A cut extracted from the event supplies a rectangle such as

    {T_k≤t, t<min_(j≠k)T_j≤v}.

This is a literal event under the original clocks. It does NOT imply that
all other players have zero hazard before t in the original profile.
It therefore does not factor that profile into a k-only early block and a
later competitor block. Deleting their other early clocks is a further
strategy change, whose prescribed outcomes and full caps require payment.

Exchanging only the desired event is not an independent-clock operation.
For example, take two independent uniform clocks on {0,1}, and leave two
additional players at Never. Swap the two times only on (T_k,T_j)=(0,1).
The resulting joint clock probabilities on (00,01,10,11) are

    (1/4, 0, 1/2, 1/4).

Its marginal probabilities give product mass 1/16 at 01, contrary to its
actual mass zero. This is an agency check, not a positive-global-minimum
counterexample. The source theorem does not assert a special factorization
which would bypass that issue.

Swapping entire actual root blocks IS legal and independent. But it also
changes all other early-event branches. For blocks A,B with prescribed
absorption vectors R_A,R_B and joint Continue probabilities c_A,c_B,
the prescribed payoff difference AB−BA is

    (1−c_B)R_A−(1−c_A)R_B.

For one player, write H_A for its best in-A response, W_A for its deleted-
owner absorption reward during A, and d_A for deleted Continue mass.
Against any actual remaining tail cap b, its complete AB cap is

    max(H_A, W_A+d_A H_B, W_A+d_A W_B+d_A d_B b),

with the analogous BA expression. These are direct substitutions into
the existing finite-prefix formula. No branch can be removed using the
contested-event probability alone. In particular the later contenders'
formerly discounted in-block responses become earlier full responses.
The k-only specialization is not used as if the source supplied it.

Thus neither the conditional event exchange nor the legal whole-block
exchange has yielded an improving competitor. The former lacks independent
implementation; the latter lacks the requisite complete-cap sign. This
does not refute an exchange theorem using additional global source facts.
The bare commutator is not developed into another supplied-success API.

## Exact overlap and next operation criterion

The complete [dated-law cap-fiber note](CODEX_LARCH_DUAL__COMPETING_RISKS_CAP_FIBERS.md)
and its [review](../feedback/CODEX_LARCH_DUAL__COMPETING_RISKS_CAP_FIBERS__BY_CODEX_LARCH_GEOMETRY.md)
were read. With positive Never mass an exact finite dated law identifies all
clocks and caps, leaving no hidden-tail completion freedom. A unique sure
owner creates just one exposed cap, minimized by the existing stationary
punishment producer. Creating that sure owner by an advancing clamp returns
to the already tested [clamp](CODEX_FRECHET_CYCLE__CLAMP_CROSS_AMPLIFICATION_AND_SOURCE_INTERVAL_REACH.md)
and [whole-tail](CODEX_TARSKI_PREMIUM__GLOBAL_MINIMUM_NEVER_BRANCH_RETRY_AND_TAIL_BUDGET.md)
boundary: the linked charged nonowner is screened from every later repair.

The source declarations read were `quittingPunishmentValue`,
`quittingPunishmentValue_eq_stationaryPunishmentValue` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`, and
`exists_quittingStationaryPunishmentRoot_lt_add`,
`IsQuittingInstantPunishmentIR`, `IsQuittingInstantNoJoin`, and
`QuittingInstantPunishmentWorks` in
`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`.
Their punishment consumer allows arbitrary signed rewards; it does not
identify an event-supported collider or guarantee a new root's no-join
conditions. No Lean build was run.

HILBERT's [all-player-ties note](CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md)
already tested literal block swaps without obtaining a general improvement;
POINCARE's [cap-prefix note](CODEX_POINCARE__PREMARK_BUBBLE_CAP_HOLONOMY.md)
supplies the scalar max-affine prefix action. Both relevant sections were
read before stopping this specialization.

The next test must add actual no-UE singleton-collider or full normal-core
restrictions to the supplied source. In particular, the profitable collider
from a raw table is not automatically the later finite opponent in the
contested event. The concrete issue is whether four-player role structure
can link those two players while retaining one actual independent operation
and its full response envelope. No additional event-count refinement is
proposed here.
