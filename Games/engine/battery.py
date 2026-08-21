"""Attack-level orchestration: replay, quick, standard, deep.

The battery runs its attacks cheapest first and reports the smallest
exploitability any of them found.  A lower score means some attack found a
profile close to an equilibrium, so the table is a worse counterexample
candidate; a higher score means the searched families all failed, which is
bounded search effort and never a proof.

Early abandon reproduces the experiment: pass ``abandon_at`` and the remaining
attacks are skipped once the running minimum drops to it, at which point the
reported score is only an upper bound on the minimum over the whole battery and
the untried attacks are recorded as ``null``.  The default runs everything.
"""

from __future__ import annotations

import math
import time
from typing import Callable, Optional, Sequence

from . import attacks as _attacks
from .library import replay_profiles
from .model import EPS_KILL, Table

LEVELS = ("replay", "quick", "standard", "deep")

#: Cheapest-first order of the search-time attacks, as in the experiment.
ATTACK_ORDER = (
    ("stationary", _attacks.attack_stationary),
    ("one_quitter_cyclic", _attacks.attack_one_quitter),
    ("general_periodic", _attacks.attack_general_periodic),
    ("two_quitter_periodic", _attacks.attack_two_quitter),
)

QUICK_ATTACK_ORDER = (
    ("stationary", _attacks.attack_stationary_quick),
    ("one_quitter_cyclic", _attacks.attack_one_quitter_quick),
    ("general_periodic", _attacks.attack_general_periodic_quick),
    ("two_quitter_periodic", _attacks.attack_two_quitter_quick),
)

ATTACK_NAMES = ("library_replay",) + tuple(name for name, _ in ATTACK_ORDER)

SURVIVOR_TIERS = {
    "replay": "unattacked",
    "quick": "survivor-quick",
    "standard": "survivor-standard",
    "deep": "survivor-deep",
}


def run_full_battery(table: Table, abandon_at: float = -math.inf) -> dict:
    """The experiment's search-time battery, key for key.

    Each attack searches its whole parameterized family, so the value it
    reports is that family's own best found exploitability.  Pass ``-inf`` to
    force the complete breakdown.
    """

    breakdown: dict[str, Optional[dict]] = {name: None for name, _ in ATTACK_ORDER}
    score = math.inf
    binding = None
    abandoned = False
    for name, attack in ATTACK_ORDER:
        report = attack(table)
        breakdown[name] = report
        if report["exploitability"] < score:
            score = report["exploitability"]
            binding = name
        if score <= abandon_at:
            abandoned = True
            break
    return {
        "score": score,
        "binding_attack": binding,
        "abandoned": abandoned,
        "breakdown": breakdown,
    }


def _library_entry(table: Table, profiles: Sequence) -> dict:
    replay = replay_profiles(table, profiles)
    return {
        "exploitability": replay["exploitability"],
        "profile": replay["profile"],
        "profiles_tried": replay["tried"],
        "source": replay["source"],
    }


def _run_sequence(
    table: Table,
    level: str,
    order: Sequence[tuple[str, Callable[[Table], dict]]],
    profiles: Sequence,
    abandon_at: float,
) -> dict:
    started = time.perf_counter()
    breakdown: dict[str, Optional[dict]] = {name: None for name in ATTACK_NAMES}
    score = math.inf
    binding = None
    abandoned = False
    entry = _library_entry(table, profiles)
    breakdown["library_replay"] = entry
    if entry["exploitability"] < score:
        score, binding = entry["exploitability"], "library_replay"
    if score > abandon_at:
        for name, attack in order:
            report = attack(table)
            breakdown[name] = report
            if report["exploitability"] < score:
                score = report["exploitability"]
                binding = name
            if score <= abandon_at:
                abandoned = True
                break
    else:
        abandoned = bool(order)
    return {
        "score": score,
        "binding_attack": binding,
        "level": level,
        "elapsed": time.perf_counter() - started,
        "abandoned": abandoned,
        "breakdown": breakdown,
    }


def run_deep(
    table: Table,
    profiles: Sequence = (),
    seed: int = _attacks.DEEP_SEED,
) -> dict:
    """Library replay followed by the experiment's deep re-attack.

    The deep stages share one seeded random stream in a fixed order, so they
    always all run; ``abandon_at`` is not offered here.  With an empty library
    the score is exactly the experiment's ``deep_reattack`` score.
    """

    started = time.perf_counter()
    entry = _library_entry(table, profiles)
    deep = _attacks.deep_reattack(table, seed=seed)
    breakdown: dict[str, Optional[dict]] = {"library_replay": entry}
    breakdown.update(deep["breakdown"])
    score = deep["score"]
    binding = deep["binding_attack"]
    if entry["exploitability"] < score:
        score, binding = entry["exploitability"], "library_replay"
    return {
        "score": score,
        "binding_attack": binding,
        "level": "deep",
        "elapsed": time.perf_counter() - started,
        "abandoned": False,
        "breakdown": breakdown,
    }


def run_level(
    table: Table,
    level: str = "standard",
    profiles: Sequence = (),
    abandon_at: Optional[float] = None,
) -> dict:
    """Run one attack level and report it in the portal's response shape.

    ``profiles`` is the attacker library, replayed first because it is nearly
    free.  ``abandon_at`` defaults to no abandonment, so the breakdown is
    complete; pass ``EPS_KILL`` to stop as soon as the table is dead.
    """

    if level not in LEVELS:
        raise ValueError(f"unknown attack level {level!r}")
    threshold = -math.inf if abandon_at is None else abandon_at
    if level == "deep":
        return run_deep(table, profiles)
    if level == "replay":
        return _run_sequence(table, level, (), profiles, threshold)
    order = QUICK_ATTACK_ORDER if level == "quick" else ATTACK_ORDER
    return _run_sequence(table, level, order, profiles, threshold)


def killing_profile(result: dict, eps_kill: float = EPS_KILL) -> Optional[dict]:
    """The wire profile of the binding attack, when the table is killed.

    Attack B is reported in the fine-block limit, so its hazard matrix is
    returned only when the shared evaluator also scores it at or below
    ``eps_kill``; otherwise there is no replayable killing profile to hand to
    the library even though B's family value killed.
    """

    if result["score"] > eps_kill:
        return None
    entry = result["breakdown"].get(result["binding_attack"])
    if not entry:
        return None
    profile = entry.get("profile")
    if profile is None:
        return None
    if entry.get("fine_block_limit"):
        if entry.get("profile_exploitability", math.inf) > eps_kill:
            return None
    return profile


def tier_for(
    score: float,
    level: str,
    exact: bool = False,
    eps_kill: float = EPS_KILL,
) -> str:
    """Evidence tier of a battery result, per DESIGN.md.

    Survivor tiers grade effort spent without a kill; they are never evidence
    that no killing profile exists.
    """

    if score <= eps_kill:
        if exact:
            return "exact"
        return "numerical-wide" if score < 0.5 * eps_kill else "numerical-narrow"
    return SURVIVOR_TIERS[level]


def status_for(score: float, level: str, eps_kill: float = EPS_KILL) -> str:
    """``killed`` when the score is at or below the kill threshold.

    A table that survives the deep level is ``verified`` in the bookkeeping
    sense of "deeply attacked and still standing", not in any mathematical
    sense.
    """

    if score <= eps_kill:
        return "killed"
    return "verified" if level == "deep" else "proposed"


def summarize(result: dict, eps_kill: float = EPS_KILL) -> dict:
    """Compact per-attack view: exploitability and profile, killed or not."""

    breakdown = {}
    for name, entry in result["breakdown"].items():
        if entry is None:
            breakdown[name] = None
            continue
        breakdown[name] = {
            "exploitability": entry["exploitability"],
            "profile": entry.get("profile"),
        }
    return {
        "score": result["score"],
        "binding_attack": result["binding_attack"],
        "level": result["level"],
        "elapsed": result["elapsed"],
        "abandoned": result["abandoned"],
        "killed": result["score"] <= eps_kill,
        "tier": tier_for(result["score"], result["level"], eps_kill=eps_kill),
        "killing_profile": killing_profile(result, eps_kill),
        "breakdown": breakdown,
    }
