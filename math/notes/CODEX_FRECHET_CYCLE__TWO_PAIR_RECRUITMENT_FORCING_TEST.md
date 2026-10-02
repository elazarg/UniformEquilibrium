# Two-pair recruitment: exact full-behavior rejection of one forcing candidate

Author: CODEX_FRECHET_CYCLE.

Status: completed bounded negative-route test. The rational table below has
an exact stationary Nash profile against unrestricted behavioral deviations.
It therefore cannot supply incompatible affine pair-mass floors. This is
an internal rejection of one candidate, not a new general no-go, a negative
game, or a claim of new special-case existence coverage. No export is requested.

## 1. Source and exact intended forcing

The route was selected through `docs/TOOLKIT.md`. I read the complete current
sources `UniformEquilibrium/Quitting/Terminal/PairMassForcingConsumer.lean`
and `UniformEquilibrium/Quitting/Terminal/FinFourAllPairCrossingConsumer.lean`.
For actual independent behavioral laws let p_C be the probability of exact
finite first quitting coalition C, and let

    E = max_i (sup over complete unilateral behavioral laws U_i' − U_i).

`QuittingFinFourAllPairMassForcing` requires, for EVERY actual profile and
every pair C, constants A_C,B_C with p_C≥A_C−B_C E. A pair of intercepts
with sqrt(max(A_C,0))+sqrt(max(A_D,0))>1 is forbidden by the independent
clock law. The named consumers
`quittingTerminalExploitability_ge_finFourMaxPairCrossing`,
`exists_pureTime_gain_half_finFourMaxPairCrossing`, and
`no_uniformEquilibriumPayoff_of_finFourMaxPairCrossing_pos` then apply.
They do not construct any affine forcing from a reward table.

The files were external additions when this task was assigned. During this
read the worktree advanced externally to HEAD
`bba5f6a3c6c570e684b6b70a370e39322efffb79`; these two paths then had no
reported local diff. This is a literal source inspection, not a fresh Lean
build or an independent checked-status claim.

Narrow prior comparisons:

- `KEPLER_CLOCKCONE__ADJACENT_PAIR_REWARD_PRODUCER_SEARCH.md`, Sections 2–5,
  already rejects adjacent-pair inverse designs using complete stationary
  caps, including examples without pure coalition equilibria.
- `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`, Propositions 24–26, has the
  profile-adapted exact-pair atom / exact-triple deviation comparison and
  the obstruction to every preassigned finite deviation calendar.
- The same note, Propositions 37–39, has the compensated Never-deletion
  ledger, the positive-singleton polarity obstruction, and the late-solo
  refusal identity. A new deletion-only account would not bypass them.
- `CODEX_EULER__TWO_ANCHOR_NASH_SEGMENT_MINIMAX_ESCAPE.md` is a reviewed
  supplied-segment stationary compiler, not an arbitrary-table pair producer.
- `ideas/QUESTION_BACKLOG/INCENTIVE_GADGET.md` records that participant-only
  rewards and protected-anchor completions are already positive chambers.

These are separate existing mathematical results; none is used to infer a
gap for a new table. The present calculation uses one explicitly completed
table and tests its unrestricted caps before attempting an affine ledger.

## 2. The complete rational candidate

There are four players I={0,1,2,3}, with target pairs A={0,1}, B={2,3}.
The table has own singleton vector s=(1,0,0,0). For each nonempty S⊆I:

- If i∈S and |S|=1, set r_i(S)=s_i.
- If i∈S and |S|=2, set r_i(S)=7 when S=A or S=B, and −1 otherwise.
- If |S|=3, it contains exactly one target pair. Give its two members −1
  and its third member 4.
- At S=I, give every player −1.
- If i∉S and |S|≥2, give i the passive payoff 1.
- If i∉S and |S|=1, give player 0 payoff 0; give player 1 payoff −1 at
  S={0}; give every other such passive coordinate payoff 1.

These rules specify all fifteen rows, including all spectator coordinates.
Preabsorption and Never pay zero. Players randomize independently at each
live date; arbitrary unilateral changes to an entire stopping law are allowed.

The intended recruitment idea was to reward two pair outcomes, make every
cross-pair unattractive to its participants, reward a third player for joining
a target pair, and make the resulting triple or grand coalition unstable.
This completion does break every pure nonempty coalition:

- From a singleton, its target partner gains by joining.
- From a target pair, either outsider gains 4−1=3 by joining.
- From a cross-pair, some member gains by leaving: player 0 gains 1 when
  present, and otherwise player 1 gains 2.
- From a triple, a member of its contained target pair gains 1−(−1)=2
  by leaving for a cross-pair.
- From the grand coalition, every member gains 2 by leaving.

All-Never is not Nash because player 0 can earn 1 by quitting. The table
also fails both DP and supportwise LP on support {2,3}: both participants
have strictly positive pair premium 7. Thus the ordered/SLP/DP sufficient
screens do not supply the explanation below. No exclusion from every other
known positive class is asserted.

A preliminary version used constant passive payoff 1 even on singletons.
It was discarded immediately: a sufficiently slow proper clock of player 0,
with all others Never, is exact stationary Nash. That is only the familiar
positive passive-singleton screen, not evidence about the completed table.

## 3. An exact stationary escape

Write x=√2 and set

    q=(3x/5, 1, 1−x/3, 1−x/3).

Every displayed hazard is legal; players 0,2,3 mix strictly, and player 1
quits surely at every live date. Actual absorption is therefore immediate.
The repeated row still specifies every off-path continuation needed when
player 1 deviates.

For a player i let α_i=∏_{j≠i}(1−q_j), let Q_i be its pure Quit-now
payoff against this opponent root, and let R_i be the one-row payoff
contribution when i Continues and some opponent quits. Put
N_i=R_i/(1−α_i), the pure-Never payoff. Direct finite product expansion gives:

| i | α_i | Q_i | R_i | N_i |
|---|---|---|---|---|
| 0 | 0 | 7/9 | 7/9 | 7/9 |
| 1 | 2/9−2x/15 | 28/3−91x/15 | 7/9−2x/15 | (7/9−2x/15)/(7/9+2x/15) |
| 2 | 0 | 1 | 1 | 1 |
| 3 | 0 | 1 | 1 | 1 |

For example put z=x/3 and u=3x/5. Because player 1 quits surely,
Q_0=−1+8z²=7/9 while R_0=1−z²=7/9. For i=2,3,
Q_i=−1+5uz=1 and R_i=1. For player 1,

    Q_1=−1+(1−u)z²+8uz²+5(1−u)(1−z)²,
    R_1=1−(1−u)z²−2uz²,

which give the table. All α_i<1. The only strict comparison needed is

    (1−α_1)Q_1−R_1=(3283−2255x)/675>0.

Indeed x<10/7, so the numerator exceeds
(22981−22550)/7=431/7>0. Thus player 1 strictly prefers Quit-now to Never;
the other three players are indifferent.

These are COMPLETE response comparisons. Against stationary opponents,
quitting at any finite date n gives

    F_i(n)=R_i Σ_{t<n}α_i^t+α_i^n Q_i
          =N_i+α_i^n(Q_i−N_i).

Never gives N_i. For players 0,2,3 every pure date and Never therefore
pays exactly the prescribed value. For player 1, the expression is at most
Q_1, attained at date zero. An arbitrary behavioral deviation induces one
independent stopping law on the nonnegative integers and Never, so its
payoff is the corresponding mixture of these values. It cannot improve.
This argument includes histories unreached under the prescribed sure quitter:
when that owner deviates, the unchanged opponent clocks still use the same
stationary row. Therefore the profile is exact terminal Nash, E=0.

## 4. Consequence for the proposed forcing

At this exact equilibrium,

    p_A=u z²=2√2/15,       p_B=0.

Any all-behavior affine floors for these two pairs must satisfy
A_A≤2√2/15 and A_B≤0, regardless of their finite slopes. Thus their
zero-error square-root corner cannot be forbidden. More generally any six
all-profile pair floors must lie below the six actual equilibrium masses;
their fifteen pairwise projections obey the clock inequalities. The
all-crossing consumer cannot produce a positive gap for this table.

No numerical root search is used as proof. A read-only SymPy expansion
checked the four exact Q,R,α expressions in Section 3; the written formulas,
the rational inequality √2<10/7, and the full stopping-law mixture argument
establish the result. No Lean files, exports, or other authors' notes were
edited. This bounded candidate is rejected, with no further parameter tuning.

The still-open task is a raw-table mechanism forcing incompatible pair masses
for every small-exploitability law. Neither pure-coalition instability,
failure of DP/SLP, nor a supplied clock consumer provides that mechanism.
