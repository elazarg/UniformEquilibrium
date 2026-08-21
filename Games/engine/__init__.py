"""Shared scoring engine for the counterexample-search game portal.

Pure-stdlib, pure-function port of the math in
``Experiments/singleton_collision_candidate_search``.  Nothing here makes a
mathematical claim: every score is the best exploitability a bounded search
found, and every "survivor" verdict records search effort, not a theorem.
"""

from __future__ import annotations

__all__ = [
    "attacks",
    "battery",
    "curated",
    "evaluator",
    "filters",
    "library",
    "model",
    "rational",
]
