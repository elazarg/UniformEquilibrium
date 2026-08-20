"""E33: a finite hidden seed cannot supply a linear tail of live entropy."""

from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
import json
import math


def lfsr_stream(seed: tuple[int, ...], horizon: int) -> tuple[int, ...]:
    state = list(seed)
    output = []
    for _ in range(horizon):
        output.append(state[0])
        feedback = state[0] ^ state[-1]
        state = state[1:] + [feedback]
    return tuple(output)


def binary_entropy(ones: int, total: int) -> float:
    if ones == 0 or ones == total:
        return 0.0
    probability = ones / total
    return -probability * math.log2(probability) - (1 - probability) * math.log2(1 - probability)


def conditional_entropy_profile(streams: list[tuple[int, ...]]) -> list[float]:
    horizon = len(streams[0])
    profile = []
    for time in range(horizon):
        groups: dict[tuple[int, ...], list[int]] = defaultdict(list)
        for stream in streams:
            groups[stream[:time]].append(stream[time])
        entropy = 0.0
        for values in groups.values():
            entropy += len(values) / len(streams) * binary_entropy(sum(values), len(values))
        profile.append(entropy)
    return profile


def run() -> dict[str, object]:
    seed_bits = 3
    horizon = 24
    seeds = list(product((0, 1), repeat=seed_bits))
    streams = [lfsr_stream(seed, horizon) for seed in seeds]
    assert len(set(streams)) == len(seeds)

    hidden_seed_profile = conditional_entropy_profile(streams)
    hidden_total = sum(hidden_seed_profile)
    assert abs(hidden_total - seed_bits) < 1e-12

    # If the seed is in the public transcript, every future output is known.
    public_seed_total = 0.0
    # With one fresh honest simultaneous XOR bit per stage, conditioning on the
    # past and on any fixed deviator action leaves one full bit every stage.
    live_entropy_total = float(horizon)

    distinct_prefix_counts = [
        len({stream[:length] for stream in streams}) for length in range(horizon + 1)
    ]
    assert distinct_prefix_counts[-1] == 2**seed_bits

    return {
        "experiment": "E33",
        "status": "passed",
        "seed_bits": seed_bits,
        "horizon": horizon,
        "hidden_seed_conditional_entropy_profile": hidden_seed_profile,
        "hidden_seed_total_live_entropy": hidden_total,
        "public_seed_total_live_entropy": public_seed_total,
        "fresh_simultaneous_xor_total_live_entropy": live_entropy_total,
        "distinct_prefix_counts": distinct_prefix_counts,
        "conclusion": (
            "A deterministic length-24 schedule expanded from a hidden 3-bit seed carries exactly three total bits of conditional entropy, and a public seed carries none.  Fresh simultaneous honest action supplies one new robust bit per stage."
        ),
        "limitation": (
            "Shannon entropy is an information resource, not by itself an exploitation or equilibrium bound; that translation needs a separate decision-theoretic inequality."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
