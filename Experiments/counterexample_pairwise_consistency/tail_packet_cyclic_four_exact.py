"""Exact-rational audit of the cyclic four-player exposed T x P witness.

The universal packet inequality and scalar tail identities are proved in
``TailPacketCyclicFourWitness.lean``.  This companion probe expands the common
reward table and checks every Bellman, endpoint-Nash, dynamic-debt, and honest
suffix formula at the first 256 dates using ``fractions.Fraction`` only.

It is a regression audit, not a finite search and not a proof of optimized
finite-minimizer provenance.
"""

from fractions import Fraction


PLAYERS = tuple(range(4))
OWNER = 0
ETA = Fraction(1, 52)
CHECK_DATES = 256


def reward(coalition: frozenset[int], who: int) -> int:
    """The shared reward table, with cyclic singleton rows and -4 elsewhere."""

    assert coalition
    if len(coalition) >= 2:
        return -4
    quitter = next(iter(coalition))
    if who == quitter:
        return 1
    if who == (quitter + 1) % 4:
        return 4
    return 0


def hazard(time: int) -> Fraction:
    return Fraction(1, 2 ** (time + 2) - 1)


def honest_absorption(time: int) -> Fraction:
    return Fraction(1, 2 ** (time + 1))


def survival_forever(time: int) -> Fraction:
    return 1 - honest_absorption(time)


def value(time: int, who: int) -> Fraction:
    absorption = honest_absorption(time)
    if who == OWNER:
        return Fraction(1)
    if who == 1:
        return 1 + 3 * absorption
    return 1 - absorption


def debt(_time: int, who: int) -> Fraction:
    return Fraction(1 if who == OWNER else 0)


def honest_payoff(time: int, who: int) -> Fraction:
    return honest_absorption(time) * reward(frozenset({OWNER}), who)


def endpoint_values(time: int, who: int) -> tuple[Fraction, Fraction]:
    """Pure-Quit and pure-Continue endpoints against the other coordinates."""

    p = hazard(time)
    next_value = value(time + 1, who)
    if who == OWNER:
        return Fraction(1), next_value
    quit_now = (1 - p) * reward(frozenset({who}), who) + p * reward(
        frozenset({OWNER, who}), who
    )
    continue_now = p * reward(frozenset({OWNER}), who) + (1 - p) * next_value
    return quit_now, continue_now


def opponent_continue_mass(time: int, who: int) -> Fraction:
    return Fraction(1) if who == OWNER else 1 - hazard(time)


def audit_tail() -> None:
    for time in range(CHECK_DATES):
        p = hazard(time)
        assert 0 < p < 1
        assert p <= Fraction(1, 2 ** (time + 1))
        assert survival_forever(time) == (1 - p) * survival_forever(time + 1)

        for who in PLAYERS:
            quit_now, continue_now = endpoint_values(time, who)
            current = value(time, who)

            # Bellman equality for the prescribed action: owner mixes, all
            # other players Continue purely.
            if who == OWNER:
                assert quit_now == continue_now == current
            else:
                assert continue_now == current
                assert quit_now <= current

            # Exact dynamic-debt update and the multiplicative conservation
            # law d_t(i) = c_i(a_t) d_{t+1}(i).
            dynamic_update = max(
                quit_now,
                continue_now
                + opponent_continue_mass(time, who) * debt(time + 1, who),
            ) - current
            assert dynamic_update == debt(time, who)
            assert debt(time, who) == (
                opponent_continue_mass(time, who) * debt(time + 1, who)
            )

        # The question's alternate conservation form
        # d_t = c(a_t)d_{t+1} + a_i,t d_t.
        all_continue = 1 - p
        for who in PLAYERS:
            own_hazard = p if who == OWNER else Fraction(0)
            assert debt(time, who) == (
                all_continue * debt(time + 1, who)
                + own_hazard * debt(time, who)
            )

        assert honest_payoff(time, OWNER) == honest_absorption(time)
        assert value(time, OWNER) - honest_payoff(time, OWNER) == (
            1 - honest_absorption(time)
        )

    assert ETA <= debt(0, OWNER) <= 1


def audit_one_packet() -> None:
    """Audit the symmetric packet; Lean handles the entire packet family."""

    mass = {who: Fraction(1, 4) for who in PLAYERS}
    target = {who: Fraction(1) for who in PLAYERS}
    for who in PLAYERS:
        mixture = sum(
            mass[quitter] * reward(frozenset({quitter}), who)
            for quitter in PLAYERS
        )
        refusal = sum(
            mass[quitter] * reward(frozenset({quitter}), who)
            for quitter in PLAYERS
            if quitter != who
        ) / (1 - mass[who])
        assert target[who] == reward(frozenset({who}), who)
        assert target[who] < mixture
        assert mixture + ETA <= refusal


def main() -> None:
    audit_tail()
    audit_one_packet()
    print(f"exact tail dates checked: {CHECK_DATES}")
    print(f"common eta/delta: {ETA}")
    print("all exact rational audits passed")
    print("scope: exposed equations only; optimized-minimizer provenance not checked")


if __name__ == "__main__":
    main()
