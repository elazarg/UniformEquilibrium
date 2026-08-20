"""Exact audit of the four-player Poincare construction in 172-Answer-GP.

The script deliberately uses only the Python standard library.  General
return-map identities are checked in the rational-function field Q(a,b), and
the positive fixed point is checked in Q(sqrt(889)).  Floating-point values
are printed only as diagnostics after all exact assertions have passed.

The answer specifies four pair bonuses but leaves the other pair rewards
open ("sufficiently low").  This audit completes the table by assigning every
other ordered joining bonus zero and assigning zero to pair spectators and to
all coalitions of size at least three.  The resulting full table lies in
the same reward box [0,2] as the singleton table.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import sqrt


F = Fraction
PLAYERS = tuple(range(4))
OWNER_CYCLE = (0, 1, 3, 2)
NEXT_OWNER = (1, 3, 2, 0)

# Rows are recipients; columns are singleton quitters.
EXCESS = (
    (F(0), F(-1, 3), F(2, 3), F(2, 3)),
    (F(2, 3), F(0), F(1), F(-1)),
    (F(-1, 3), F(2, 3), F(0), F(1)),
    (F(1), F(2, 3), F(-2, 3), F(0)),
)


class Polynomial:
    """A tiny exact polynomial ring Q[a,b], sufficient for this audit."""

    def __init__(self, terms: dict[tuple[int, int], Fraction] | None = None):
        self.terms = {
            degree: coefficient
            for degree, coefficient in (terms or {}).items()
            if coefficient
        }

    @staticmethod
    def constant(value: int | Fraction) -> "Polynomial":
        coefficient = F(value)
        return Polynomial({(0, 0): coefficient} if coefficient else {})

    @staticmethod
    def variable(which: int) -> "Polynomial":
        degree = (1, 0) if which == 0 else (0, 1)
        return Polynomial({degree: F(1)})

    def __add__(self, other: object) -> "Polynomial":
        rhs = as_polynomial(other)
        result = dict(self.terms)
        for degree, coefficient in rhs.terms.items():
            result[degree] = result.get(degree, F(0)) + coefficient
            if not result[degree]:
                del result[degree]
        return Polynomial(result)

    __radd__ = __add__

    def __neg__(self) -> "Polynomial":
        return Polynomial({degree: -coefficient for degree, coefficient in self.terms.items()})

    def __sub__(self, other: object) -> "Polynomial":
        return self + (-as_polynomial(other))

    def __rsub__(self, other: object) -> "Polynomial":
        return as_polynomial(other) - self

    def __mul__(self, other: object) -> "Polynomial":
        rhs = as_polynomial(other)
        result: dict[tuple[int, int], Fraction] = {}
        for (a_degree, b_degree), lhs_coefficient in self.terms.items():
            for (c_degree, d_degree), rhs_coefficient in rhs.terms.items():
                degree = (a_degree + c_degree, b_degree + d_degree)
                result[degree] = result.get(degree, F(0)) + lhs_coefficient * rhs_coefficient
        return Polynomial(result)

    __rmul__ = __mul__

    def __eq__(self, other: object) -> bool:
        try:
            return self.terms == as_polynomial(other).terms
        except TypeError:
            return False

    def is_zero(self) -> bool:
        return not self.terms


def as_polynomial(value: object) -> Polynomial:
    if isinstance(value, Polynomial):
        return value
    if isinstance(value, (int, Fraction)):
        return Polynomial.constant(value)
    raise TypeError(f"cannot coerce {type(value)!r} to Polynomial")


class RationalFunction:
    """An unreduced rational function; equality is exact cross multiplication."""

    def __init__(self, numerator: object, denominator: object = 1):
        self.numerator = as_polynomial(numerator)
        self.denominator = as_polynomial(denominator)
        if self.denominator.is_zero():
            raise ZeroDivisionError("zero polynomial denominator")

    @staticmethod
    def coerce(value: object) -> "RationalFunction":
        return value if isinstance(value, RationalFunction) else RationalFunction(value)

    def __add__(self, other: object) -> "RationalFunction":
        rhs = self.coerce(other)
        return RationalFunction(
            self.numerator * rhs.denominator + rhs.numerator * self.denominator,
            self.denominator * rhs.denominator,
        )

    __radd__ = __add__

    def __neg__(self) -> "RationalFunction":
        return RationalFunction(-self.numerator, self.denominator)

    def __sub__(self, other: object) -> "RationalFunction":
        return self + (-self.coerce(other))

    def __rsub__(self, other: object) -> "RationalFunction":
        return self.coerce(other) - self

    def __mul__(self, other: object) -> "RationalFunction":
        rhs = self.coerce(other)
        return RationalFunction(
            self.numerator * rhs.numerator,
            self.denominator * rhs.denominator,
        )

    __rmul__ = __mul__

    def __truediv__(self, other: object) -> "RationalFunction":
        rhs = self.coerce(other)
        if rhs.numerator.is_zero():
            raise ZeroDivisionError("zero rational function divisor")
        return RationalFunction(
            self.numerator * rhs.denominator,
            self.denominator * rhs.numerator,
        )

    def __rtruediv__(self, other: object) -> "RationalFunction":
        return self.coerce(other) / self

    def __eq__(self, other: object) -> bool:
        try:
            rhs = self.coerce(other)
        except TypeError:
            return False
        return self.numerator * rhs.denominator == rhs.numerator * self.denominator


def rf(value: object, denominator: object = 1) -> RationalFunction:
    return RationalFunction(value, denominator)


@dataclass(frozen=True)
class Quadratic:
    """An exact element rational + radical * sqrt(889)."""

    rational: Fraction = F(0)
    radical: Fraction = F(0)

    @staticmethod
    def coerce(value: object) -> "Quadratic":
        if isinstance(value, Quadratic):
            return value
        if isinstance(value, (int, Fraction)):
            return Quadratic(F(value), F(0))
        raise TypeError(f"cannot coerce {type(value)!r} to Quadratic")

    def __add__(self, other: object) -> "Quadratic":
        rhs = self.coerce(other)
        return Quadratic(self.rational + rhs.rational, self.radical + rhs.radical)

    __radd__ = __add__

    def __neg__(self) -> "Quadratic":
        return Quadratic(-self.rational, -self.radical)

    def __sub__(self, other: object) -> "Quadratic":
        return self + (-self.coerce(other))

    def __rsub__(self, other: object) -> "Quadratic":
        return self.coerce(other) - self

    def __mul__(self, other: object) -> "Quadratic":
        rhs = self.coerce(other)
        return Quadratic(
            self.rational * rhs.rational + 889 * self.radical * rhs.radical,
            self.rational * rhs.radical + self.radical * rhs.rational,
        )

    __rmul__ = __mul__

    def __truediv__(self, other: object) -> "Quadratic":
        rhs = self.coerce(other)
        norm = rhs.rational * rhs.rational - 889 * rhs.radical * rhs.radical
        if not norm:
            raise ZeroDivisionError("zero quadratic divisor")
        return self * Quadratic(rhs.rational / norm, -rhs.radical / norm)

    def __rtruediv__(self, other: object) -> "Quadratic":
        return self.coerce(other) / self

    def __eq__(self, other: object) -> bool:
        try:
            rhs = self.coerce(other)
        except TypeError:
            return False
        return self.rational == rhs.rational and self.radical == rhs.radical

    def sign(self) -> int:
        """Exact sign, comparing rational squares when the terms conflict."""
        u, v = self.rational, self.radical
        if not v:
            return (u > 0) - (u < 0)
        if u >= 0 and v > 0:
            return 1
        if u <= 0 and v < 0:
            return -1
        comparison = u * u - 889 * v * v
        if u > 0 and v < 0:
            return (comparison > 0) - (comparison < 0)
        # u < 0 < v: the radical wins exactly when comparison is negative.
        return (comparison < 0) - (comparison > 0)

    def __lt__(self, other: object) -> bool:
        return (self - self.coerce(other)).sign() < 0

    def __le__(self, other: object) -> bool:
        return (self - self.coerce(other)).sign() <= 0

    def __gt__(self, other: object) -> bool:
        return self.coerce(other) < self

    def __ge__(self, other: object) -> bool:
        return self.coerce(other) <= self

    def decimal(self) -> float:
        return float(self.rational) + float(self.radical) * sqrt(889)

    def __str__(self) -> str:
        if not self.radical:
            return str(self.rational)
        sign = "+" if self.radical > 0 else "-"
        coefficient = abs(self.radical)
        return f"{self.rational} {sign} {coefficient}*sqrt(889)"


Q = Quadratic


def check_symbolic_return_map() -> None:
    """Verify every Bellman phase and the displayed map in Q(a,b)."""
    a_polynomial = Polynomial.variable(0)
    b_polynomial = Polynomial.variable(1)
    a = rf(a_polynomial)
    b = rf(b_polynomial)
    zero = rf(0)

    d0_den = 2 - 3 * a
    d1_den = 4 + 3 * a - 6 * b
    d3_den = 4 - 5 * a - 2 * b
    return_den = 8 + 15 * a - 18 * b

    z0 = (zero, a, zero, b)
    q0 = 3 * a / 2
    z1 = (
        zero,
        zero,
        a / d0_den,
        (2 * b - 3 * a) / d0_den,
    )
    q1 = 3 * (2 * b - 3 * a) / (2 * d0_den)
    z2 = (
        (2 * b - 3 * a) / d1_den,
        zero,
        4 * (2 * a - b) / d1_den,
        zero,
    )
    q3 = 4 * (2 * a - b) / d1_den
    z3 = (
        (14 * b - 25 * a) / (3 * d3_den),
        4 * (2 * a - b) / d3_den,
        zero,
        zero,
    )
    q2 = (14 * b - 25 * a) / (2 * d3_den)
    z4 = (
        zero,
        (41 * a - 22 * b) / return_den,
        zero,
        2 * (-25 * a + 14 * b) / (3 * return_den),
    )

    states = (z0, z1, z2, z3, z4)
    hazards = (q0, q1, q3, q2)
    for phase, (owner, next_owner) in enumerate(zip(OWNER_CYCLE, NEXT_OWNER)):
        current, following, hazard = states[phase], states[phase + 1], hazards[phase]
        assert current[owner] == 0
        assert following[owner] == 0
        assert following[next_owner] == 0
        for who in PLAYERS:
            assert current[who] == (1 - hazard) * following[who] + hazard * EXCESS[who][owner]

    # The last state is exactly the map printed in the answer.
    assert z4[1] == (41 * a - 22 * b) / return_den
    assert z4[3] == 2 * (-25 * a + 14 * b) / (3 * return_den)


def fixed_phase(
    current: tuple[Quadratic, ...], owner: int, next_owner: int
) -> tuple[Quadratic, tuple[Quadratic, ...]]:
    """Select the hazard that zeros the next owner's coordinate."""
    hazard = current[next_owner] / EXCESS[next_owner][owner]
    survival = 1 - hazard
    following = tuple(
        (current[who] - hazard * EXCESS[who][owner]) / survival
        for who in PLAYERS
    )
    assert current[owner] == 0
    assert following[owner] == 0
    assert following[next_owner] == 0
    assert 0 < hazard < 1
    return hazard, following


# Ordered joining bonuses beta_(joiner, owner).
BETA = {(joiner, owner): F(0) for joiner in PLAYERS for owner in PLAYERS if joiner != owner}
BETA.update(
    {
        (2, 0): F(1, 6),
        (0, 1): F(1, 6),
        (1, 3): F(1, 2),
        (3, 2): F(1, 3),
    }
)
BLOCKER = {0: 2, 1: 0, 3: 1, 2: 3}


def payoff(quitters: frozenset[int], who: int) -> Fraction:
    """The completed rational payoff table used by the audit."""
    assert quitters
    if len(quitters) == 1:
        owner = next(iter(quitters))
        return 1 + EXCESS[who][owner]
    if len(quitters) == 2 and who in quitters:
        owner = next(player for player in quitters if player != who)
        return 1 + EXCESS[who][owner] + BETA[who, owner]
    # Pair spectators and all coordinates of larger coalitions are irrelevant
    # to this periodic profile and are fixed to zero for a complete game table.
    return F(0)


def cyclic_terminal_payoff(
    start: int, who: int, hazards: tuple[Quadratic, ...]
) -> Quadratic:
    """Exact infinite-horizon payoff by summing a geometric four-date cycle."""
    survival = Q(1)
    one_cycle = Q(0)
    for offset in range(4):
        phase = (start + offset) % 4
        owner = OWNER_CYCLE[phase]
        hazard = hazards[phase]
        one_cycle += survival * hazard * payoff(frozenset((owner,)), who)
        survival *= 1 - hazard
    assert 0 < survival < 1
    return one_cycle / (1 - survival)


def check_fixed_game() -> dict[str, object]:
    """Check the algebraic fixed point, Nash inequalities, and actual values."""
    coalitions = tuple(
        frozenset(group)
        for size in range(1, 5)
        for group in combinations(PLAYERS, size)
    )
    assert len(coalitions) == 15
    assert all(
        F(0) <= payoff(group, who) <= F(2)
        for group in coalitions
        for who in PLAYERS
    )

    rho = Q(F(95, 132), F(5, 132))
    a = Q(F(517, 450), F(-11, 450))
    b = Q(F(1, 270), F(7, 270))

    assert 66 * rho * rho - 95 * rho - 50 == 0
    # After cancelling a and the common return-map denominator, this is
    # exactly F_2(a,rho*a) = rho*F_1(a,rho*a).
    assert 2 * (-25 + 14 * rho) == 3 * rho * (41 - 22 * rho)
    assert b == rho * a
    assert a > 0 and b > 0

    # An explicit exact local contraction check.  Since 15-18*rho < 0,
    # every 0 < x <= 1/100 has return ratio bounded above by this endpoint.
    linear_ratio = (41 - 22 * rho) / 8
    endpoint_ratio = (41 - 22 * rho) / (8 + (15 - 18 * rho) / 100)
    assert 0 < linear_ratio < endpoint_ratio < F(1, 10)
    assert F(25, 14) < rho < 2
    small = Q(F(1, 100))
    small_b = rho * small
    small_hazards = (
        3 * small / 2,
        3 * (2 * small_b - 3 * small) / (2 * (2 - 3 * small)),
        4 * (2 * small - small_b) / (4 + 3 * small - 6 * small_b),
        (14 * small_b - 25 * small) / (2 * (4 - 5 * small - 2 * small_b)),
    )
    assert all(0 < hazard < 1 for hazard in small_hazards)

    return_den = 8 + 15 * a - 18 * b
    mapped_a = (41 * a - 22 * b) / return_den
    mapped_b = 2 * (-25 * a + 14 * b) / (3 * return_den)
    assert mapped_a == a
    assert mapped_b == b

    states: list[tuple[Quadratic, ...]] = [(Q(0), a, Q(0), b)]
    hazards: list[Quadratic] = []
    for owner, next_owner in zip(OWNER_CYCLE, NEXT_OWNER):
        hazard, following = fixed_phase(states[-1], owner, next_owner)
        hazards.append(hazard)
        states.append(following)
    assert states[-1] == states[0]
    assert all(coordinate >= 0 for state in states[:-1] for coordinate in state)

    outsider_slacks: dict[tuple[int, int], Quadratic] = {}
    continuation_ratios: dict[tuple[int, int], Quadratic] = {}
    for phase, owner in enumerate(OWNER_CYCLE):
        current, following = states[phase], states[phase + 1]
        hazard = hazards[phase]
        survival = 1 - hazard

        # The mixing owner's two pure endpoints agree exactly.
        owner_quit = Q(payoff(frozenset((owner,)), owner))
        owner_continue = 1 + following[owner]
        assert owner_quit == owner_continue == 1

        for who in PLAYERS:
            # Bellman consistency on the equilibrium path.
            bellman = survival * (1 + following[who]) + hazard * payoff(
                frozenset((owner,)), who
            )
            assert 1 + current[who] == bellman
            if who == owner:
                continue

            # Outsider's Continue and Quit endpoints against the owner mix.
            continue_value = bellman
            quit_value = survival * payoff(frozenset((who,)), who) + hazard * payoff(
                frozenset((who, owner)), who
            )
            ratio = survival * following[who] / hazard
            slack = continue_value - quit_value
            assert slack == hazard * (ratio - BETA[who, owner])
            assert slack >= 0
            continuation_ratios[who, owner] = ratio
            outsider_slacks[who, owner] = slack

    advertised_ratios = {
        (2, 0): Q(F(1, 3)),
        (0, 1): Q(F(1, 3)),
        (1, 3): Q(F(1)),
        (3, 2): Q(F(2, 3)),
    }
    for pair, expected in advertised_ratios.items():
        assert continuation_ratios[pair] == expected
        assert outsider_slacks[pair] > 0

    # Each pure singleton exit has its advertised strict pair joiner.
    for owner, blocker in BLOCKER.items():
        watching = payoff(frozenset((owner,)), blocker)
        joining = payoff(frozenset((owner, blocker)), blocker)
        assert joining - watching == BETA[blocker, owner] > 0

    exact_hazards = tuple(hazards)
    exact_states = tuple(states[:-1])
    # Even if one deviator suppresses every one of its prescribed hazards,
    # the other three owners still force geometric absorption.  This removes
    # the infinite-horizon boundary term in the one-stage-deviation argument.
    for deviator in PLAYERS:
        opponent_survival = Q(1)
        for owner, hazard in zip(OWNER_CYCLE, exact_hazards):
            if owner != deviator:
                opponent_survival *= 1 - hazard
        assert 0 < opponent_survival < 1
    for phase in range(4):
        for who in PLAYERS:
            assert cyclic_terminal_payoff(phase, who, exact_hazards) == 1 + exact_states[phase][who]

    return {
        "rho": rho,
        "a": a,
        "b": b,
        "hazards": exact_hazards,
        "states": exact_states,
        "ratios": continuation_ratios,
        "slacks": outsider_slacks,
    }


def print_table() -> None:
    coalitions = tuple(
        frozenset(group)
        for size in range(1, 5)
        for group in combinations(PLAYERS, size)
    )
    print("completed reward table (coalition: players 0,1,2,3):")
    for group in coalitions:
        label = "{" + ",".join(str(player) for player in sorted(group)) + "}"
        row = ", ".join(str(payoff(group, who)) for who in PLAYERS)
        print(f"  {label:9s}: ({row})")


def main() -> None:
    check_symbolic_return_map()
    certificate = check_fixed_game()

    print("general four-phase rational-function identities: PASS")
    print("quadratic fixed point, 16 Bellman identities, and 16 Nash endpoints: PASS")
    print("16 cyclic annotation/actual-terminal-payoff identities: PASS")
    print(f"rho = {certificate['rho']} ~= {certificate['rho'].decimal():.12f}")
    print(f"a*  = {certificate['a']} ~= {certificate['a'].decimal():.12f}")
    print(f"b*  = {certificate['b']} ~= {certificate['b'].decimal():.12f}")
    print("hazards in owner order 0,1,3,2:")
    for owner, hazard in zip(OWNER_CYCLE, certificate["hazards"]):
        print(f"  q_{owner} = {hazard} ~= {hazard.decimal():.12f}")
    print("advertised blocker continuation ratios:")
    for owner in OWNER_CYCLE:
        blocker = BLOCKER[owner]
        ratio = certificate["ratios"][blocker, owner]
        print(f"  beta_({blocker},{owner}) <= {ratio}")
    print_table()


if __name__ == "__main__":
    main()
