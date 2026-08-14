"""Exact-rational audit of the cyclic four-player exposed T x P x W witness.

The common table and phantom tail originate in the T x P regression.  The
selected tail here is the one-date suffix ``shifted_root(t) = root(t + 1)``;
all canonical windows are formed only after that reindexing.  This is
important: the one-phase window at the discarded original date is an exact
equilibrium and would not satisfy W.

Every calculation below uses ``fractions.Fraction``.  Finite loops audit the
expanded table.  The accompanying report and Lean file give the arbitrary-
date/window algebra.  This probe neither searches for nor certifies optimized
finite-minimizer provenance.
"""

from fractions import Fraction


PLAYERS = tuple(range(4))
OWNER = 0
WINDOW_WITNESS = 2
SHIFT = 1
ETA = Fraction(1, 52)
CHECK_DATES = 256
CHECK_WINDOWS = 128


def reward(coalition: frozenset[int], who: int) -> int:
    """Cyclic singleton columns and constant -4 collision rewards."""

    assert coalition
    if len(coalition) >= 2:
        return -4
    quitter = next(iter(coalition))
    if who == quitter:
        return 1
    if who == (quitter + 1) % 4:
        return 4
    return 0


def hazard_absolute(time: int) -> Fraction:
    return Fraction(1, 2 ** (time + 2) - 1)


def hazard(time: int) -> Fraction:
    """Owner-0 hazard at reindexed tail date ``time``."""

    return hazard_absolute(time + SHIFT)


def absorption_absolute(time: int) -> Fraction:
    return Fraction(1, 2 ** (time + 1))


def survival_forever_absolute(time: int) -> Fraction:
    return 1 - absorption_absolute(time)


def value(time: int, who: int) -> Fraction:
    absolute = time + SHIFT
    absorption = absorption_absolute(absolute)
    if who == OWNER:
        return Fraction(1)
    if who == 1:
        return 1 + 3 * absorption
    return 1 - absorption


def debt(_time: int, who: int) -> Fraction:
    return Fraction(1 if who == OWNER else 0)


def honest_payoff(time: int, who: int) -> Fraction:
    absolute = time + SHIFT
    return absorption_absolute(absolute) * reward(frozenset({OWNER}), who)


def endpoint_values(time: int, who: int) -> tuple[Fraction, Fraction]:
    """Pure-Quit and pure-Continue endpoints at a shifted tail root."""

    p = hazard(time)
    if who == OWNER:
        return Fraction(1), value(time + 1, who)
    quit_now = (1 - p) * reward(frozenset({who}), who) + p * reward(
        frozenset({OWNER, who}), who
    )
    continue_now = p * reward(frozenset({OWNER}), who) + (
        1 - p
    ) * value(time + 1, who)
    return quit_now, continue_now


def opponent_continue_mass(time: int, who: int) -> Fraction:
    return Fraction(1) if who == OWNER else 1 - hazard(time)


def audit_shifted_tail() -> None:
    for time in range(CHECK_DATES):
        absolute = time + SHIFT
        p = hazard(time)
        assert 0 < p <= Fraction(1, 7)
        assert survival_forever_absolute(absolute) == (
            (1 - p) * survival_forever_absolute(absolute + 1)
        )

        for who in PLAYERS:
            quit_now, continue_now = endpoint_values(time, who)
            current = value(time, who)
            if who == OWNER:
                assert quit_now == continue_now == current
            else:
                assert continue_now == current
                assert quit_now <= current

            dynamic_update = max(
                quit_now,
                continue_now
                + opponent_continue_mass(time, who) * debt(time + 1, who),
            ) - current
            assert dynamic_update == debt(time, who)
            assert debt(time, who) == (
                opponent_continue_mass(time, who) * debt(time + 1, who)
            )

        all_continue = 1 - p
        for who in PLAYERS:
            own_hazard = p if who == OWNER else Fraction(0)
            assert debt(time, who) == (
                all_continue * debt(time + 1, who)
                + own_hazard * debt(time, who)
            )

        assert value(time, OWNER) - honest_payoff(time, OWNER) == (
            1 - absorption_absolute(absolute)
        )

    assert ETA <= debt(0, OWNER) <= 1


def singleton_mixture(mass: tuple[Fraction, ...], who: int) -> Fraction:
    return sum(
        mass[quitter] * reward(frozenset({quitter}), who)
        for quitter in PLAYERS
    )


def refusal_value(mass: tuple[Fraction, ...], who: int) -> Fraction:
    return sum(
        mass[quitter] * reward(frozenset({quitter}), who)
        for quitter in PLAYERS
        if quitter != who
    ) / (1 - mass[who])


def audit_selected_packet_and_tail_occupation() -> None:
    """The companion Lean theorem covers the whole feasible packet family."""

    packet = tuple(Fraction(1, 4) for _ in PLAYERS)
    target = tuple(Fraction(1) for _ in PLAYERS)
    for who in PLAYERS:
        mixture = singleton_mixture(packet, who)
        refusal = refusal_value(packet, who)
        assert mixture == Fraction(5, 4)
        assert refusal == Fraction(4, 3)
        assert target[who] < mixture
        assert mixture + ETA <= refusal

    tail_mass = (Fraction(1), Fraction(0), Fraction(0), Fraction(0))
    ghost_target = target
    assert tuple(singleton_mixture(tail_mass, who) for who in PLAYERS) == (
        Fraction(1),
        Fraction(4),
        Fraction(0),
        Fraction(0),
    )
    assert ghost_target[2] > singleton_mixture(tail_mass, 2)
    assert ghost_target[3] > singleton_mixture(tail_mass, 3)


def product(values: list[Fraction]) -> Fraction:
    result = Fraction(1)
    for value_at_phase in values:
        result *= value_at_phase
    return result


def window_phase_value(start: int, phase_time: int) -> Fraction:
    """Player 2's first-pass deterministic stop value at an absolute date."""

    survival_before = product(
        [1 - hazard_absolute(time) for time in range(start, phase_time)]
    )
    return survival_before * (1 - 5 * hazard_absolute(phase_time))


def audit_canonical_windows() -> None:
    for n in range(CHECK_WINDOWS):
        # The reindexed word (a~_n,...,a~_(2n)) is the original word at
        # absolute dates n+1,...,2n+1.
        start = n + SHIFT
        end = 2 * n + SHIFT
        pass_survival = product(
            [1 - hazard_absolute(time) for time in range(start, end + 1)]
        )
        telescoped = (
            survival_forever_absolute(start)
            / survival_forever_absolute(end + 1)
        )
        assert pass_survival == telescoped
        assert 0 < pass_survival < 1

        phase_values = [
            window_phase_value(start, phase_time)
            for phase_time in range(start, end + 1)
        ]
        assert all(value_at_phase > 0 for value_at_phase in phase_values)
        assert all(
            phase_values[index] < phase_values[index + 1]
            for index in range(len(phase_values) - 1)
        )

        # Every later-pass occurrence is multiplied by pass_survival^k.
        # Since all first-pass stop values are positive, the exact evaluator
        # is the last phase of the first pass; refusal/Never is zero.
        evaluator = max(Fraction(0), *phase_values)
        assert evaluator == phase_values[-1]
        assert evaluator >= phase_values[0]
        assert phase_values[0] == 1 - 5 * hazard_absolute(start)
        assert evaluator >= Fraction(2, 7) > ETA / 2

        # Owner 0 absorbs almost surely under periodic repetition, and its
        # singleton column pays player 2 zero.
        prescribed_delivery = Fraction(0)
        assert evaluator - prescribed_delivery > ETA / 2


def stationary_endpoints(
    p: Fraction, continuation: tuple[Fraction, ...], who: int
) -> tuple[Fraction, Fraction]:
    if who == OWNER:
        return Fraction(1), continuation[who]
    quit_now = (1 - p) * reward(frozenset({who}), who) + p * reward(
        frozenset({OWNER, who}), who
    )
    continue_now = p * reward(frozenset({OWNER}), who) + (
        1 - p
    ) * continuation[who]
    return quit_now, continue_now


def audit_global_failures() -> None:
    """An exact equilibrium/self-loop refutes global A and charge capacity."""

    p = Fraction(1, 3)
    stationary_value = (Fraction(1), Fraction(4), Fraction(0), Fraction(0))
    for who in PLAYERS:
        quit_now, continue_now = stationary_endpoints(
            p, stationary_value, who
        )
        if who == OWNER:
            assert quit_now == continue_now == stationary_value[who]
        else:
            assert quit_now == Fraction(-2, 3)
            assert continue_now == stationary_value[who]
            assert quit_now < continue_now

    # The stationary profile delivers the singleton-0 column exactly and is
    # an equilibrium against every behavioral deviation by pure-time
    # extremality.  The same exact floor-admissible Bellman state/action pair
    # can be repeated N times with charge N/3.
    assert tuple(reward(frozenset({OWNER}), who) for who in PLAYERS) == (
        1,
        4,
        0,
        0,
    )
    for length in (1, 2, 17, 101):
        assert length * p == Fraction(length, 3)


def main() -> None:
    audit_shifted_tail()
    audit_selected_packet_and_tail_occupation()
    audit_canonical_windows()
    audit_global_failures()
    print(f"shifted exact tail dates checked: {CHECK_DATES}")
    print(f"canonical windows checked: {CHECK_WINDOWS}")
    print(f"common eta/delta: {ETA}")
    print("window witness: player 2, exact last-phase branch, value >= 2/7")
    print("tail occupation: e_0; floor holds, funding fails in rows 2 and 3")
    print("global A and global charge capacity both fail on a p=1/3 self-loop")
    print("all exact rational audits passed")


if __name__ == "__main__":
    main()
