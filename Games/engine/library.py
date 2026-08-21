"""Replay of the attacker library against a table.

Every profile that ever killed a table is kept and replayed against every new
candidate first.  Replay is cheap and exact given the profile: it is one
closed-form evaluation each, so a library of a few thousand profiles still
costs less than a single Nelder-Mead start.
"""

from __future__ import annotations

import math
from typing import Any, Iterable, Optional

from .evaluator import evaluate, periodic_exploitability
from .model import EPS_KILL, ModelError, Table, hazards_from_wire, hazards_to_wire


def _entry_hazards(entry: Any) -> tuple[list[list[float]], Optional[dict]]:
    """Accept a wire profile, a bare hazard matrix, or a library record."""

    if isinstance(entry, dict):
        if "hazards" in entry and "profile" not in entry:
            return hazards_from_wire(entry), entry
        profile = entry.get("profile")
        if profile is None:
            raise ModelError("library entry: no profile")
        return hazards_from_wire(profile), entry
    if isinstance(entry, (list, tuple)):
        return hazards_from_wire({"period": len(entry), "hazards": list(entry)}), None
    raise ModelError(f"library entry: unsupported {type(entry).__name__}")


def replay_profiles(table: Table, profiles: Iterable[Any]) -> dict:
    """Best (lowest exploitability) profile in ``profiles`` against ``table``.

    Returns the exploitability, the winning profile in wire form, its index in
    the input order, and the source record it came from when the input carried
    one.  An empty library gives ``inf`` and ``None``, which is the identity
    for the battery's running minimum.
    """

    best_value = math.inf
    best_profile: Optional[dict] = None
    best_index: Optional[int] = None
    best_source: Optional[dict] = None
    tried = 0
    for index, entry in enumerate(profiles):
        hazards, record = _entry_hazards(entry)
        tried += 1
        value = periodic_exploitability(table, hazards)
        if value < best_value:
            best_value = value
            best_profile = hazards_to_wire(hazards)
            best_index = index
            best_source = record
    return {
        "exploitability": best_value,
        "profile": best_profile,
        "index": best_index,
        "tried": tried,
        "source": _source_summary(best_source),
    }


def _source_summary(record: Optional[dict]) -> Optional[dict]:
    if not record:
        return None
    summary = {key: record[key] for key in ("id", "source") if key in record}
    return summary or None


def kills(
    table: Table, profiles: Iterable[Any], eps_kill: float = EPS_KILL
) -> list[dict]:
    """Every library profile whose exploitability is at or below ``eps_kill``."""

    found: list[dict] = []
    for index, entry in enumerate(profiles):
        hazards, record = _entry_hazards(entry)
        value = periodic_exploitability(table, hazards)
        if value <= eps_kill:
            found.append(
                {
                    "index": index,
                    "exploitability": value,
                    "profile": hazards_to_wire(hazards),
                    "source": _source_summary(record),
                }
            )
    return found


def explain(table: Table, profile: Any) -> dict:
    """Full evaluator detail for one library profile, for the UI."""

    hazards, _ = _entry_hazards(profile)
    detail = evaluate(table, hazards)
    detail["profile"] = hazards_to_wire(hazards)
    return detail
