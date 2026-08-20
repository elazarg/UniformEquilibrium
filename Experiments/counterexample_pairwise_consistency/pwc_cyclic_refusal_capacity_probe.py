"""Exact negative control for the P x W x C investigation.

One four-player rational quitting table carries, on shared data:

* the full table-wide packet margin delta = 1/21;
* the funded punishment-rational packet (lambda,z) = ((1/3,1/3,1/3,0),0);
* canonical small-hazard periodic windows whose normalized singleton-owner
  occupation is exactly lambda and whose fixed refusal player gains by more
  than delta; and
* a packet-support-aligned exact three-edge Nash--Bellman cycle of charge 3/2.

The last item deliberately violates universal finite charge capacity.  Thus
this is a negative control, not a P x W x C consistency witness.  It shows
exactly how the linked refusal branch can become charged progress when
collision rewards do not block the packet rotation.

All arithmetic uses fractions.  The continuum-wide packet and all-window
estimates are proved symbolically in the accompanying report; finite scans
here are exact regressions only.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


Q = Fraction
PLAYERS = range(4)
ACTIVE = range(3)
GRID_DENOMINATOR = 80
WINDOW_LIMIT = 18
DELTA = Q(1, 21)

# Rows are recipients and columns are singleton owners.
SINGLETON = (
    (Q(0), Q(2), Q(-1), Q(0)),
    (Q(-1), Q(0), Q(2), Q(0)),
    (Q(2), Q(-1), Q(0), Q(0)),
    (Q(0), Q(0), Q(0), Q(-1)),
)


def all_coalitions() -> tuple[frozenset[int], ...]:
    return tuple(
        frozenset(group)
        for size in range(1, 5)
        for group in combinations(PLAYERS, size)
    )


def reward(coalition: frozenset[int], who: int) -> Q:
    assert coalition
    if len(coalition) == 1:
        return SINGLETON[who][next(iter(coalition))]
    return Q(0)


def singleton_mixture(mass: tuple[Q, Q, Q, Q], who: int) -> Q:
    return sum(
        (mass[owner] * reward(frozenset({owner}), who) for owner in PLAYERS),
        Q(0),
    )


def refusal_value(mass: tuple[Q, Q, Q, Q], who: int) -> Q:
    assert mass[who] < 1
    return sum(
        (
            mass[owner] * reward(frozenset({owner}), who)
            for owner in PLAYERS
            if owner != who
        ),
        Q(0),
    ) / (1 - mass[who])


def is_packet_mass(mass: tuple[Q, Q, Q, Q]) -> bool:
    return (
        all(component >= 0 for component in mass)
        and sum(mass, Q(0)) == 1
        and mass[3] == 0
        and all(singleton_mixture(mass, who) >= 0 for who in PLAYERS)
    )


def product_action(owner: int, hazard: Q) -> tuple[Q, Q, Q, Q]:
    return tuple(
        hazard if who == owner else Q(0) for who in PLAYERS
    )  # type: ignore[return-value]


def continuation_payoff(
    action: tuple[Q, Q, Q, Q],
    value: tuple[Q, Q, Q, Q],
    who: int,
    quit_prob: Q,
) -> Q:
    altered = list(action)
    altered[who] = quit_prob
    total = Q(0)
    for coalition in all_coalitions():
        probability = Q(1)
        for player in PLAYERS:
            probability *= (
                altered[player] if player in coalition else 1 - altered[player]
            )
        total += probability * reward(coalition, who)
    survival = Q(1)
    for probability in altered:
        survival *= 1 - probability
    return total + survival * value[who]


def successor(
    action: tuple[Q, Q, Q, Q], value: tuple[Q, Q, Q, Q]
) -> tuple[Q, Q, Q, Q]:
    return tuple(
        continuation_payoff(action, value, who, action[who]) for who in PLAYERS
    )  # type: ignore[return-value]


def absorption(action: tuple[Q, Q, Q, Q]) -> Q:
    survival = Q(1)
    for probability in action:
        survival *= 1 - probability
    return 1 - survival


def periodic_value(
    phases: tuple[Q, ...], absorption_at, reward_at
) -> Q:
    """Value of one finite word repeated forever, from its first phase."""

    survival = Q(1)
    pass_reward = Q(0)
    for p in phases:
        pass_reward += survival * reward_at(p)
        survival *= 1 - absorption_at(p)
    assert survival < 1
    return pass_reward / (1 - survival)


def canonical_window(n: int) -> tuple[Q, ...]:
    return tuple(Q(1, 200 * 2**time) for time in range(n, 2 * n + 1))


def assert_table_packet_and_floor() -> int:
    coalitions = all_coalitions()
    assert len(coalitions) == 15
    assert max(
        abs(reward(coalition, who))
        for coalition in coalitions
        for who in PLAYERS
    ) == 2

    # Exact punishment vector chi=0.
    for who in ACTIVE:
        assert all(
            reward(coalition, who) == 0
            for coalition in coalitions
            if who in coalition
        )
        assert reward(frozenset({who}), who) == 0
    assert all(
        reward(coalition, 3) == 0 for coalition in coalitions if 3 not in coalition
    )
    assert reward(frozenset({3}), 3) == -1

    mass = (Q(1, 3), Q(1, 3), Q(1, 3), Q(0))
    assert is_packet_mass(mass)
    assert tuple(singleton_mixture(mass, who) for who in PLAYERS) == (
        Q(1, 3),
        Q(1, 3),
        Q(1, 3),
        Q(0),
    )
    assert all(refusal_value(mass, who) == Q(1, 2) for who in ACTIVE)

    feasible_count = 0
    for denominator in range(1, GRID_DENOMINATOR + 1):
        for n0 in range(denominator + 1):
            for n1 in range(denominator - n0 + 1):
                n2 = denominator - n0 - n1
                candidate = (
                    Q(n0, denominator),
                    Q(n1, denominator),
                    Q(n2, denominator),
                    Q(0),
                )
                if not is_packet_mass(candidate):
                    continue
                feasible_count += 1
                gains = []
                for who in ACTIVE:
                    mix = singleton_mixture(candidate, who)
                    if candidate[who] > 0 and mix > 0:
                        gains.append(refusal_value(candidate, who) - mix)
                assert gains and max(gains) >= DELTA
    return feasible_count


def assert_linked_refusal_windows() -> None:
    lower_refusal = Q(199, 399)
    lower_gap = Q(22, 133)
    assert lower_gap == lower_refusal - Q(1, 3)
    assert DELTA < lower_gap

    for n in range(WINDOW_LIMIT + 1):
        phases = canonical_window(n)
        assert phases and max(phases) <= Q(1, 200)

        # Three prescribed symmetric active hazards.  At one phase,
        # alpha=1-(1-p)^3 and recipient 0 gets p(1-p)^2 from the terminal
        # singleton row.  All collision rewards vanish.
        prescribed = periodic_value(
            phases,
            lambda p: 1 - (1 - p) ** 3,
            lambda p: p * (1 - p) ** 2,
        )

        # After player 0 refuses, the two remaining active hazards give
        # beta=1-(1-p)^2 and reward contribution p(1-p).
        refusal = periodic_value(
            phases,
            lambda p: 1 - (1 - p) ** 2,
            lambda p: p * (1 - p),
        )
        assert Q(0) <= prescribed <= Q(1, 3)
        assert refusal >= lower_refusal
        assert refusal - prescribed >= lower_gap > DELTA

        # Exact occupation bridge: all three singleton-owner contributions
        # agree phase by phase, hence also after chronological weighting and
        # periodic normalization.
        singleton_owner_weights = []
        for owner in ACTIVE:
            singleton_owner_weights.append(
                periodic_value(
                    phases,
                    lambda p: 1 - (1 - p) ** 3,
                    lambda p: p * (1 - p) ** 2,
                )
            )
        assert singleton_owner_weights[0] == singleton_owner_weights[1]
        assert singleton_owner_weights[1] == singleton_owner_weights[2]
        total_singleton = sum(singleton_owner_weights, Q(0))
        assert total_singleton > 0
        assert tuple(weight / total_singleton for weight in singleton_owner_weights) == (
            Q(1, 3),
            Q(1, 3),
            Q(1, 3),
        )


def assert_packet_aligned_charged_cycle() -> None:
    states = (
        (Q(0), Q(1), Q(0), Q(0)),
        (Q(0), Q(0), Q(1), Q(0)),
        (Q(1), Q(0), Q(0), Q(0)),
    )
    actions = tuple(product_action(owner, Q(1, 2)) for owner in ACTIVE)

    for index, (value, action) in enumerate(zip(states, actions)):
        assert successor(action, value) == states[(index + 1) % 3]
        assert absorption(action) == Q(1, 2)
        for who in PLAYERS:
            prescribed = continuation_payoff(action, value, who, action[who])
            wait = continuation_payoff(action, value, who, Q(0))
            quit_now = continuation_payoff(action, value, who, Q(1))
            assert prescribed >= wait
            assert prescribed >= quit_now

    assert sum((absorption(action) for action in actions), Q(0)) == Q(3, 2)
    repetitions = 20
    assert sum(
        (absorption(action) for action in actions * repetitions), Q(0)
    ) == 30


def main() -> None:
    feasible_count = assert_table_packet_and_floor()
    assert_linked_refusal_windows()
    assert_packet_aligned_charged_cycle()
    print("P x W x C linked-refusal negative control: PASS")
    print(f"complete coalitions checked: {len(all_coalitions())}")
    print(f"exact feasible packet grid points checked: {feasible_count}")
    print(f"exact canonical windows checked: 0..{WINDOW_LIMIT}")
    print(f"common packet/window margin: {DELTA}")
    print("exact normalized singleton occupation: (1/3,1/3,1/3,0)")
    print("packet-support cycle charge per turn: 3/2")
    print("classification: OPEN (shared candidate violates universal C)")


if __name__ == "__main__":
    main()
