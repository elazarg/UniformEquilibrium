"""Loader for the original experiment script, used as the parity oracle.

The script under ``Experiments/singleton_collision_candidate_search/`` is
read-only and is never imported by the engine itself; only the tests load it,
by path, so that the engine's numbers can be compared against the numbers the
experiment actually produced.
"""

from __future__ import annotations

import importlib.util
import os
import random
import sys
from pathlib import Path

GAMES_DIR = Path(__file__).resolve().parents[2]
REPO_ROOT = GAMES_DIR.parent
REFERENCE_PATH = (
    REPO_ROOT
    / "Experiments"
    / "singleton_collision_candidate_search"
    / "singleton_collision_candidate_search.py"
)

if str(GAMES_DIR) not in sys.path:
    sys.path.insert(0, str(GAMES_DIR))

_MODULE_NAME = "singleton_collision_candidate_search_reference"


def load_reference():
    """Import the experiment script by path, once per process."""

    existing = sys.modules.get(_MODULE_NAME)
    if existing is not None:
        return existing
    spec = importlib.util.spec_from_file_location(_MODULE_NAME, REFERENCE_PATH)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load reference from {REFERENCE_PATH}")
    module = importlib.util.module_from_spec(spec)
    # The script defines a dataclass at import time, and dataclasses look the
    # defining module up in sys.modules, so registration must precede exec.
    sys.modules[_MODULE_NAME] = module
    # Importing by path would otherwise drop a __pycache__ entry next to the
    # experiment source, and everything outside Games/ is strictly read-only.
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = previous
    return module


def slow_tests_enabled() -> bool:
    return os.environ.get("GAMES_SLOW_TESTS", "") not in ("", "0", "false")


def random_table(rng: random.Random) -> tuple[tuple[float, ...], ...]:
    """A uniform random reward table in the model's payoff box."""

    rows = [[0.0] * 4 for _ in range(16)]
    for mask in range(1, 16):
        for i in range(4):
            rows[mask][i] = rng.uniform(-4.0, 4.0)
    return tuple(tuple(row) for row in rows)


def random_hazards(rng: random.Random, period: int, tiny: bool) -> list[list[float]]:
    """Random hazards; ``tiny`` draws log-uniformly down to ``1e-20``.

    The tiny regime is not exotic: the attacks park hazards near zero chasing
    the fine-block limit, and that is exactly where the cyclic solve is
    delicate, so parity has to be checked there too.
    """

    def draw() -> float:
        if tiny:
            return 10.0 ** rng.uniform(-20.0, 0.0)
        return rng.uniform(0.0, 1.0)

    return [[draw() for _ in range(4)] for _ in range(period)]
