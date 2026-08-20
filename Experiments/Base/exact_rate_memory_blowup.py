"""E29: exact deterministic rate realization can require exponentially many states."""

from __future__ import annotations

from fractions import Fraction
import json
import math


def balanced_word(numerator: int, denominator: int) -> list[int]:
    return [
        ((t + 1) * numerator) // denominator - (t * numerator) // denominator
        for t in range(denominator)
    ]


def minimum_cycle_length(numerator: int, denominator: int) -> int:
    target = Fraction(numerator, denominator)
    for length in range(1, denominator + 1):
        if any(Fraction(ones, length) == target for ones in range(length + 1)):
            return length
    raise AssertionError("the denominator-length construction must work")


def run() -> dict[str, object]:
    checked = 0
    worst_discrepancy = Fraction(0)
    for denominator in range(2, 65):
        for numerator in range(1, denominator):
            if math.gcd(numerator, denominator) != 1:
                continue
            checked += 1
            assert minimum_cycle_length(numerator, denominator) == denominator
            word = balanced_word(numerator, denominator)
            assert sum(word) == numerator
            prefix = 0
            for length, bit in enumerate(word, start=1):
                prefix += bit
                discrepancy = abs(Fraction(prefix) - Fraction(length * numerator, denominator))
                worst_discrepancy = max(worst_discrepancy, discrepancy)
                assert discrepancy < 1

    power_family = []
    for exponent in range(1, 13):
        denominator = 2**exponent
        encoding_bits = Fraction(1).numerator.bit_length() + denominator.bit_length()
        power_family.append(
            {
                "rate": f"1/{denominator}",
                "input_bits": encoding_bits,
                "minimum_recurrent_states": denominator,
            }
        )

    return {
        "experiment": "E29",
        "status": "passed",
        "reduced_rates_checked": checked,
        "largest_denominator_exhaustively_checked": 64,
        "largest_observed_prefix_discrepancy": str(worst_discrepancy),
        "power_of_two_family": power_family,
        "conclusion": (
            "A deterministic recurrent controller with exact reduced rate a/b needs a cycle whose length is a multiple of b; the balanced b-cycle attains discrepancy below one.  Exact phase memory can therefore be exponential in the bit length of the rate."
        ),
        "limitation": (
            "Randomized controllers or approximate rates may compress this representation.  The lower bound is for explicit deterministic recurrent phase generators."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
