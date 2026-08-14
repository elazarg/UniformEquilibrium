"""Exact symbolic probe for the T x W positive-hazard witness.

This is not a floating-point search.  The file contains a tiny univariate
rational-function checker over ``fractions.Fraction`` so it has no external
dependencies.  Every asserted equality is checked after polynomial cross
multiplication over Q[X].  The accompanying report supplies the strategic
proof and the infinite-tail quantifiers.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable


def _trim(coeffs: Iterable[Fraction]) -> tuple[Fraction, ...]:
    result = list(coeffs)
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result or [Fraction(0)])


@dataclass(frozen=True)
class Poly:
    """A polynomial over Q, stored in increasing degree order."""

    coeffs: tuple[Fraction, ...]

    def __init__(self, coeffs: Iterable[int | Fraction]):
        object.__setattr__(self, "coeffs", _trim(Fraction(c) for c in coeffs))

    @staticmethod
    def coerce(value: int | Fraction | "Poly") -> "Poly":
        return value if isinstance(value, Poly) else Poly((value,))

    def __add__(self, other: int | Fraction | "Poly") -> "Poly":
        rhs = Poly.coerce(other)
        size = max(len(self.coeffs), len(rhs.coeffs))
        return Poly(
            (self.coeffs[i] if i < len(self.coeffs) else 0)
            + (rhs.coeffs[i] if i < len(rhs.coeffs) else 0)
            for i in range(size)
        )

    __radd__ = __add__

    def __neg__(self) -> "Poly":
        return Poly(-c for c in self.coeffs)

    def __sub__(self, other: int | Fraction | "Poly") -> "Poly":
        return self + (-Poly.coerce(other))

    def __rsub__(self, other: int | Fraction | "Poly") -> "Poly":
        return Poly.coerce(other) - self

    def __mul__(self, other: int | Fraction | "Poly") -> "Poly":
        rhs = Poly.coerce(other)
        result = [Fraction(0)] * (len(self.coeffs) + len(rhs.coeffs) - 1)
        for i, left in enumerate(self.coeffs):
            for j, right in enumerate(rhs.coeffs):
                result[i + j] += left * right
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> "Poly":
        assert exponent >= 0
        result = Poly((1,))
        base = self
        power = exponent
        while power:
            if power % 2:
                result = result * base
            base = base * base
            power //= 2
        return result

    def compose(self, affine: "Poly") -> "Poly":
        result = Poly((0,))
        for coefficient in reversed(self.coeffs):
            result = result * affine + coefficient
        return result

    @property
    def degree(self) -> int:
        return len(self.coeffs) - 1

    @property
    def leading(self) -> Fraction:
        return self.coeffs[-1]


@dataclass(frozen=True)
class Rat:
    """A rational function over Q[X], compared by cross multiplication."""

    numerator: Poly
    denominator: Poly

    def __init__(
        self,
        numerator: int | Fraction | Poly,
        denominator: int | Fraction | Poly = 1,
    ):
        num = Poly.coerce(numerator)
        den = Poly.coerce(denominator)
        assert den.coeffs != (Fraction(0),)
        object.__setattr__(self, "numerator", num)
        object.__setattr__(self, "denominator", den)

    @staticmethod
    def coerce(value: int | Fraction | Poly | "Rat") -> "Rat":
        return value if isinstance(value, Rat) else Rat(value)

    def __add__(self, other: int | Fraction | Poly | "Rat") -> "Rat":
        rhs = Rat.coerce(other)
        return Rat(
            self.numerator * rhs.denominator + rhs.numerator * self.denominator,
            self.denominator * rhs.denominator,
        )

    __radd__ = __add__

    def __neg__(self) -> "Rat":
        return Rat(-self.numerator, self.denominator)

    def __sub__(self, other: int | Fraction | Poly | "Rat") -> "Rat":
        return self + (-Rat.coerce(other))

    def __rsub__(self, other: int | Fraction | Poly | "Rat") -> "Rat":
        return Rat.coerce(other) - self

    def __mul__(self, other: int | Fraction | Poly | "Rat") -> "Rat":
        rhs = Rat.coerce(other)
        return Rat(
            self.numerator * rhs.numerator,
            self.denominator * rhs.denominator,
        )

    __rmul__ = __mul__

    def __truediv__(self, other: int | Fraction | Poly | "Rat") -> "Rat":
        rhs = Rat.coerce(other)
        assert rhs.numerator.coeffs != (Fraction(0),)
        return Rat(
            self.numerator * rhs.denominator,
            self.denominator * rhs.numerator,
        )

    def __rtruediv__(self, other: int | Fraction | Poly | "Rat") -> "Rat":
        return Rat.coerce(other) / self

    def __pow__(self, exponent: int) -> "Rat":
        assert exponent >= 0
        return Rat(self.numerator**exponent, self.denominator**exponent)

    def compose_affine(self, scale: int, shift: int) -> "Rat":
        affine = Poly((shift, scale))
        return Rat(
            self.numerator.compose(affine), self.denominator.compose(affine)
        )

    def equals(self, other: int | Fraction | Poly | "Rat") -> bool:
        rhs = Rat.coerce(other)
        return (
            self.numerator * rhs.denominator
            == rhs.numerator * self.denominator
        )

    def limit_at_infinity(self) -> Fraction:
        num_degree = self.numerator.degree
        den_degree = self.denominator.degree
        if num_degree < den_degree:
            return Fraction(0)
        if num_degree == den_degree:
            return self.numerator.leading / self.denominator.leading
        raise AssertionError("probe only requests finite rational limits")


X = Rat(Poly((0, 1)))


def p(index: Rat) -> Rat:
    return 1 / (index + 2) ** 2


def debt(index: Rat) -> Rat:
    return (index + 1) / (index + 2)


def value(index: Rat) -> Rat:
    return 2 * debt(index)


def zero(expr: Rat) -> None:
    assert expr.equals(0)


# Tail recursions in the date variable t.
p_t = p(X)
survival_t = 1 - p_t
d_t = debt(X)
d_next = debt(X + 1)
v_t = value(X)
v_next = value(X + 1)
zero(d_t - survival_t * d_next)
zero(v_t - survival_t * v_next)

# Owner endpoint and exact dynamic-debt update.  The second max branch is
# selected because v_t >= 1 and d_t > 0 on all natural dates.
owner_quit_endpoint = Rat(1)
owner_continue_endpoint = v_t
raised_continue_endpoint = owner_continue_endpoint + survival_t * d_next
zero(raised_continue_endpoint - (v_t + d_t))
zero((raised_continue_endpoint - v_t) - d_t)
assert value(Rat(0)).equals(owner_quit_endpoint)

# Canonical inclusive word n,...,2n.  These calculations now use X as n.
window_survival = (2 * X + 3) / (2 * X + 4)
window_absorption = 1 - window_survival
assert window_absorption.equals(1 / (2 * X + 4))

# Closed-form telescoping product:
# product_{k=L}^U (1 - 1/k^2) = (L-1)(U+1)/(LU).
lower = X + 2
upper = 2 * X + 2
telescoped_product = (lower - 1) * (upper + 1) / (lower * upper)
assert window_survival.equals(telescoped_product)

v_start = value(X)
v_end = value(2 * X + 1)
d_start = debt(X)
d_end = debt(2 * X + 1)
zero(v_start - window_survival * v_end)
zero(d_start - window_survival * d_end)

# Honest periodic delivery is zero.  The normalized drift is not o(m_n).
periodic_delivery = Rat(0)
zero(
    v_start
    - (window_absorption * periodic_delivery + window_survival * v_end)
)
normalized_endpoint_drift = (v_end - v_start) / window_absorption
normalized_restart_drift = (
    window_survival * (v_end - v_start) / window_absorption
)
assert normalized_endpoint_drift.equals(v_end)
assert normalized_restart_drift.equals(v_start)
assert normalized_endpoint_drift.limit_at_infinity() == 2
assert normalized_restart_drift.limit_at_infinity() == 2

# Literal finite evaluator branches.  Arbitrary behavioral deviations reduce
# to these branches by the repository's exact periodic-window theorem.
refusal_value = Fraction(0)
phase_zero_value = Fraction(1)
best_response_value = max(refusal_value, phase_zero_value)
honest_delivery = Fraction(0)
eta = Fraction(1, 2)
assert best_response_value == 1
assert best_response_value - honest_delivery > eta / 2

# Exact T bounds and limits.
assert debt(Rat(0)).equals(eta)
assert d_t.limit_at_infinity() == 1
assert v_t.limit_at_infinity() == 2
assert p_t.limit_at_infinity() == 0


if __name__ == "__main__":
    print("T x W exact rational-polynomial identities: PASS")
    print("window absorption m_n = 1/(2n+4)")
    print("(v_(2n+1)-v_n)/m_n = v_(2n+1) -> 2")
    print("((1-m_n)/m_n)(v_(2n+1)-v_n) = v_n -> 2")
    print("periodic evaluator (refusal, phase 0, best) = (0, 1, 1)")
