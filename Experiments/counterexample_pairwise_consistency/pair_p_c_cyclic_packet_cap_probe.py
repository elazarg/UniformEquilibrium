"""Exact negative control for the P x C pair investigation.

The four-player rational table checked here has:

* a nonempty normalized singleton-packet family;
* a table-wide refusal margin delta = 1/21 on that entire family;
* punishment value zero for every player;
* a punishment-rational all-Continue zero-charge self-loop at zero; and
* an exact three-edge Bellman--Nash cycle with charge 3/2.

The last item means that the table deliberately FAILS the universal bounded
charge clause of C.  It is a negative control for the tempting inference
"uniform packet defect + local cap => bounded exact capacity".

All arithmetic is performed with fractions.  The finite packet scan is only
a regression (denominators at most GRID_DENOMINATOR); the continuum-wide
delta = 1/21 proof is given in the accompanying report.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


Q = Fraction
PLAYERS = range(4)
ACTIVE = range(3)
GRID_DENOMINATOR = 120
DELTA = Q(1, 21)

# Singleton rows for players 0, 1, 2.  Columns are singleton owners.
# Column 0 is (0,-1,2), column 1 is (2,0,-1), and column 2 is
# (-1,2,0).  Player 3 receives zero from these three singleton exits.
SINGLETON = (
    (Q(0), Q(2), Q(-1), Q(0)),
    (Q(-1), Q(0), Q(2), Q(0)),
    (Q(2), Q(-1), Q(0), Q(0)),
    (Q(0), Q(0), Q(0), Q(-1)),
)


def reward(coalition: frozenset[int], who: int) -> Q:
    """The complete 15-coalition reward table."""

    assert coalition
    if len(coalition) == 1:
        owner = next(iter(coalition))
        return SINGLETON[who][owner]
    return Q(0)


def all_coalitions() -> tuple[frozenset[int], ...]:
    return tuple(
        frozenset(group)
        for size in range(1, 5)
        for group in combinations(PLAYERS, size)
    )


def singleton_mixture(mass: tuple[Q, Q, Q, Q], who: int) -> Q:
    return sum((mass[owner] * reward(frozenset({owner}), who) for owner in PLAYERS), Q(0))


def refusal_value(mass: tuple[Q, Q, Q, Q], who: int) -> Q:
    assert mass[who] < 1
    numerator = sum(
        (mass[owner] * reward(frozenset({owner}), who) for owner in PLAYERS if owner != who),
        Q(0),
    )
    return numerator / (1 - mass[who])


def is_packet_mass(mass: tuple[Q, Q, Q, Q]) -> bool:
    """Packet feasibility after the report's exact target elimination.

    The punishment vector is zero.  Thus player 3 cannot carry mass (its solo
    reward is -1), all targets are forced to zero, and packet feasibility is
    precisely nonnegativity of the four singleton mixtures.
    """

    return (
        all(component >= 0 for component in mass)
        and sum(mass, Q(0)) == 1
        and mass[3] == 0
        and all(singleton_mixture(mass, who) >= 0 for who in PLAYERS)
    )


def product_action(owner: int, hazard: Q) -> tuple[Q, Q, Q, Q]:
    return tuple(hazard if who == owner else Q(0) for who in PLAYERS)  # type: ignore[return-value]


def continuation_payoff(action: tuple[Q, Q, Q, Q], value: tuple[Q, Q, Q, Q], who: int, quit_prob: Q) -> Q:
    """One-stage payoff when `who` replaces its component by quit_prob."""

    altered = list(action)
    altered[who] = quit_prob
    total = Q(0)
    for coalition in all_coalitions():
        probability = Q(1)
        for player in PLAYERS:
            probability *= altered[player] if player in coalition else 1 - altered[player]
        total += probability * reward(coalition, who)
    survival = Q(1)
    for probability in altered:
        survival *= 1 - probability
    return total + survival * value[who]


def successor(action: tuple[Q, Q, Q, Q], value: tuple[Q, Q, Q, Q]) -> tuple[Q, Q, Q, Q]:
    return tuple(continuation_payoff(action, value, who, action[who]) for who in PLAYERS)  # type: ignore[return-value]


def absorption(action: tuple[Q, Q, Q, Q]) -> Q:
    survival = Q(1)
    for probability in action:
        survival *= 1 - probability
    return 1 - survival


def assert_complete_table_and_punishment_floor() -> None:
    coalitions = all_coalitions()
    assert len(coalitions) == 15
    assert max(abs(reward(coalition, who)) for coalition in coalitions for who in PLAYERS) == 2

    # Players 0,1,2 guarantee zero by quitting immediately: every coalition
    # containing them pays them zero.  Against all-Continue opponents their
    # best payoff is max(solo, Never) = 0.
    for who in ACTIVE:
        assert all(reward(coalition, who) == 0 for coalition in coalitions if who in coalition)
        assert reward(frozenset({who}), who) == 0

    # Player 3 guarantees zero by Never: every coalition not containing 3
    # pays it zero.  Against all-Continue opponents its best payoff is Never
    # (zero), rather than its solo payoff -1.
    assert all(reward(coalition, 3) == 0 for coalition in coalitions if 3 not in coalition)
    assert reward(frozenset({3}), 3) == -1


def assert_packet_witness_and_exact_grid() -> int:
    uniform = (Q(1, 3), Q(1, 3), Q(1, 3), Q(0))
    assert is_packet_mass(uniform)
    assert tuple(singleton_mixture(uniform, who) for who in PLAYERS) == (
        Q(1, 3),
        Q(1, 3),
        Q(1, 3),
        Q(0),
    )
    assert all(refusal_value(uniform, who) == Q(1, 2) for who in ACTIVE)

    feasible_count = 0
    for denominator in range(1, GRID_DENOMINATOR + 1):
        for n0 in range(denominator + 1):
            for n1 in range(denominator - n0 + 1):
                n2 = denominator - n0 - n1
                mass = (Q(n0, denominator), Q(n1, denominator), Q(n2, denominator), Q(0))
                if not is_packet_mass(mass):
                    continue
                feasible_count += 1
                gains = []
                for who in ACTIVE:
                    mix = singleton_mixture(mass, who)
                    if mass[who] > 0 and mix > 0:
                        gains.append(refusal_value(mass, who) - mix)
                assert gains
                assert max(gains) >= DELTA
    return feasible_count


def assert_cap_and_charged_cycle() -> None:
    zero = (Q(0), Q(0), Q(0), Q(0))
    all_continue = (Q(0), Q(0), Q(0), Q(0))

    # Punishment floor chi is zero.  At value zero, each player's solo payoff
    # is at most zero, so all-Continue is an exact zero-charge self-loop.
    assert successor(all_continue, zero) == zero
    assert absorption(all_continue) == 0
    for who in PLAYERS:
        prescribed = continuation_payoff(all_continue, zero, who, Q(0))
        quit_now = continuation_payoff(all_continue, zero, who, Q(1))
        assert prescribed >= quit_now

    states = (
        (Q(0), Q(1), Q(0), Q(0)),
        (Q(0), Q(0), Q(1), Q(0)),
        (Q(1), Q(0), Q(0), Q(0)),
    )
    actions = tuple(product_action(owner, Q(1, 2)) for owner in ACTIVE)

    for index, (value, action) in enumerate(zip(states, actions)):
        expected = states[(index + 1) % len(states)]
        assert successor(action, value) == expected
        assert absorption(action) == Q(1, 2)
        for who in PLAYERS:
            prescribed = continuation_payoff(action, value, who, action[who])
            continue_value = continuation_payoff(action, value, who, Q(0))
            quit_value = continuation_payoff(action, value, who, Q(1))
            assert prescribed >= continue_value
            assert prescribed >= quit_value

    # Twenty repetitions are already a finite exact prefix of charge 30;
    # arbitrary repetition proves that no finite universal charge bound exists.
    repetitions = 20
    total_charge = sum((absorption(action) for action in actions * repetitions), Q(0))
    assert total_charge == 30


def main() -> None:
    assert_complete_table_and_punishment_floor()
    feasible_count = assert_packet_witness_and_exact_grid()
    assert_cap_and_charged_cycle()
    print("P x C cyclic packet/cap negative control: PASS")
    print(f"complete coalitions checked: {len(all_coalitions())}")
    print(f"exact feasible packet grid points checked: {feasible_count}")
    print(f"grid denominators: 1..{GRID_DENOMINATOR}")
    print(f"proved report margin delta: {DELTA}")
    print("local cap charge: 0")
    print("repeatable exact cycle charge: 3/2")
    print("classification: OPEN (candidate violates universal C)")


if __name__ == "__main__":
    main()
