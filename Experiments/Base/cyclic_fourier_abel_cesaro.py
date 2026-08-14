"""E20: Fourier-mode Abel/Cesaro separation for a slow cyclic kernel."""

from __future__ import annotations

import cmath
import json


def slow_mode_eigenvalue(root: complex, lam: float, coefficient: float) -> complex:
    return 1.0 - coefficient * lam + coefficient * lam * root


def abel_multiplier(eigenvalue: complex, lam: float) -> complex:
    return lam / (1.0 - (1.0 - lam) * eigenvalue)


def cesaro_multiplier(eigenvalue: complex, horizon: int) -> complex:
    if abs(eigenvalue - 1.0) < 1e-14:
        return 1.0 + 0.0j
    return (1.0 - eigenvalue**horizon) / (horizon * (1.0 - eigenvalue))


def encode(value: complex) -> list[float]:
    return [value.real, value.imag]


def run() -> dict:
    state_count = 5
    coefficient = 0.7
    lambdas = [1e-1, 1e-2, 1e-3, 1e-4, 1e-6]
    fixed_lambda = 0.02
    modes = []

    for frequency in range(state_count):
        root = cmath.exp(2j * cmath.pi * frequency / state_count)
        limit = 1.0 / (1.0 + coefficient * (1.0 - root))
        abel_samples = []
        errors = []
        for lam in lambdas:
            eigenvalue = slow_mode_eigenvalue(root, lam, coefficient)
            multiplier = abel_multiplier(eigenvalue, lam)
            abel_samples.append(encode(multiplier))
            errors.append(abs(multiplier - limit))
        if frequency == 0:
            assert max(errors) < 1e-10
        else:
            assert errors[-1] < errors[0]

        fixed_eigenvalue = slow_mode_eigenvalue(root, fixed_lambda, coefficient)
        cesaro_samples = [
            abs(cesaro_multiplier(fixed_eigenvalue, horizon))
            for horizon in [100, 1_000, 10_000, 100_000]
        ]
        if frequency == 0:
            assert all(abs(value - 1.0) < 1e-12 for value in cesaro_samples)
            assert abs(limit - 1.0) < 1e-12
        else:
            assert cesaro_samples[-1] < cesaro_samples[0]
            assert abs(limit) > 0.1

        modes.append(
            {
                "frequency": frequency,
                "abel_limit": encode(limit),
                "abel_samples": abel_samples,
                "fixed_policy_cesaro_magnitudes": cesaro_samples,
            }
        )

    return {
        "experiment": "E20",
        "status": "passed",
        "cyclic_state_count": state_count,
        "slow_transition_coefficient": coefficient,
        "modes": modes,
        "conclusion": (
            "Every nontrivial cyclic representation mode retains a nonzero Abel "
            "boundary-layer coefficient when transition speed is O(lambda), yet "
            "the same mode vanishes in the Cesaro limit of every fixed policy."
        ),
        "limitation": (
            "Fourier diagonalization applies to convolution/cyclic kernels; a general "
            "game requires transition-algebra invariant subspaces instead of characters."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
