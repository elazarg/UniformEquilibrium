"""E15: random-phase sigma-delta realization of rational rate streams.

Let p_t=k_t/m.  Choose one phase R uniformly in {0,...,m-1}, initialize the
accumulator at R/m, and perform first-order error-feedback rounding.  For every
fixed phase, every prefix discrepancy is less than one.  Averaging over the
phase gives E[u_t]=p_t at every time, even for a time-varying rate stream.

E01 explains how two players can generate the phase robustly.  The remaining
strategic defect is that a public phase makes the entire future pulse sequence
predictable once the future p_t are known.
"""

from __future__ import annotations

import json
from fractions import Fraction


def sigma_delta(rate_numerators: list[int], denominator: int, phase: int):
    assert 0 <= phase < denominator
    assert all(0 <= numerator <= denominator for numerator in rate_numerators)
    residual = Fraction(phase, denominator)
    pulses = []
    discrepancies = []
    cumulative_pulse = Fraction(0)
    cumulative_rate = Fraction(0)
    for numerator in rate_numerators:
        rate = Fraction(numerator, denominator)
        residual += rate
        pulse = int(residual >= 1)
        residual -= pulse
        assert 0 <= residual < 1
        pulses.append(pulse)
        cumulative_pulse += pulse
        cumulative_rate += rate
        discrepancy = cumulative_pulse - cumulative_rate
        assert discrepancy == Fraction(phase, denominator) - residual
        assert abs(discrepancy) < 1
        discrepancies.append(discrepancy)
    return pulses, discrepancies


def run() -> dict:
    denominator = 11
    base_pattern = [1, 7, 0, 11, 3, 9, 2, 5, 10, 4, 8, 6]
    rate_numerators = (base_pattern * 40)[:400]
    all_pulses = []
    worst_prefix_discrepancy = Fraction(0)

    for phase in range(denominator):
        pulses, discrepancies = sigma_delta(rate_numerators, denominator, phase)
        all_pulses.append(pulses)
        worst_prefix_discrepancy = max(
            worst_prefix_discrepancy, max(abs(value) for value in discrepancies)
        )

    marginal_checks = []
    for time, numerator in enumerate(rate_numerators):
        pulse_count = sum(pulses[time] for pulses in all_pulses)
        assert pulse_count == numerator
        marginal_checks.append(Fraction(pulse_count, denominator))

    # Once the public phase and rate stream are known, prediction is perfect.
    chosen_phase = 3
    known_pulses, _ = sigma_delta(rate_numerators, denominator, chosen_phase)
    perfect_predictions = list(known_pulses)
    assert perfect_predictions == known_pulses

    return {
        "experiment": "E15",
        "status": "passed",
        "denominator": denominator,
        "phases_checked": denominator,
        "time_steps_checked": len(rate_numerators),
        "worst_prefix_discrepancy": str(worst_prefix_discrepancy),
        "all_one_time_marginals_exact": all(
            marginal == Fraction(numerator, denominator)
            for marginal, numerator in zip(marginal_checks, rate_numerators)
        ),
        "public_phase_predictability": "future pulses are exactly predictable",
        "conclusion": (
            "One robust finite random phase simultaneously gives exact rational "
            "one-time marginals and uniformly bounded pathwise prefix discrepancy."
        ),
        "limitation": (
            "The phase does not hide future pulses.  Strategic use requires either "
            "predictability to be harmless or a causal refresh mechanism preserving discrepancy."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
