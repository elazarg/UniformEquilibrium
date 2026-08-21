"""Curated tables: the Solan-Vieille seed and the experiment's chain bests.

The only I/O in the engine.  ``results.json`` under
``Experiments/singleton_collision_candidate_search/`` is read strictly
read-only; nothing here writes anywhere.

The scores carried alongside each table are the ones that experiment recorded.
They are the best exploitability its bounded search found -- for the chain
bests, the deep re-attack's verdict, which supersedes the search-time score.
None of them survived the kill threshold, so these tables are useful as
starting points and as calibration for the games, not as candidates.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

from .model import Table, table_from_labels, table_to_wire, seed_table

RESULTS_PATH = (
    Path(__file__).resolve().parents[2]
    / "Experiments"
    / "singleton_collision_candidate_search"
    / "results.json"
)

SEED_NOTE = (
    "Solan-Vieille (2001) Section 3 four-player quitting game. The known "
    "period-two repair on the pairs {1,3} and {2,4} drives exploitability to "
    "about zero, so the seed is a starting point, not a candidate."
)


def _load_results(path: Optional[Path] = None) -> Optional[dict]:
    source = Path(path) if path is not None else RESULTS_PATH
    try:
        with source.open(encoding="utf-8") as handle:
            return json.load(handle)
    except (OSError, ValueError):
        return None


def seed_entry(results: Optional[dict] = None) -> dict:
    table = seed_table()
    known: Optional[float] = None
    binding: Optional[str] = None
    if results:
        battery = results.get("seed_table", {}).get("battery", {})
        known = battery.get("score")
        binding = battery.get("binding_attack")
    note = SEED_NOTE
    if binding:
        note += f" Search battery score bound by {binding}."
    return {
        "id": "solan_vieille_seed",
        "name": "Solan-Vieille seed",
        "table": table_to_wire(table),
        "known_score": known,
        "note": note,
        "source": "Solan-Vieille 2001, Section 3",
    }


def chain_entries(results: Optional[dict]) -> list[dict]:
    if not results:
        return []
    entries: list[dict] = []
    for chain in results.get("chains", []):
        best = chain.get("best")
        if not best or "table" not in best:
            continue
        seed = chain.get("seed")
        deep = best.get("deep_reattack", {})
        known = deep.get("score", best.get("search_score"))
        note = (
            f"Best table of hill-climbing chain seed {seed} in the singleton "
            f"collision search: search-time score "
            f"{best.get('search_score'):.6g} bound by "
            f"{best.get('binding_attack')}, deep re-attack score "
            f"{deep.get('score'):.6g} bound by {deep.get('binding_attack')}. "
            "The deep verdict supersedes the search-time score; this table "
            "did not survive the kill threshold."
        )
        entries.append(
            {
                "id": f"chain_{seed}",
                "name": f"Chain {seed} best",
                "table": table_to_wire(table_from_labels(best["table"])),
                "known_score": known,
                "note": note,
                "source": (
                    "Experiments/singleton_collision_candidate_search/results.json"
                ),
            }
        )
    return entries


def curated_tables(path: Optional[Path] = None) -> list[dict]:
    """The curated set in wire form: seed first, then the three chain bests."""

    results = _load_results(path)
    return [seed_entry(results)] + chain_entries(results)


def curated_by_id(path: Optional[Path] = None) -> dict[str, dict]:
    return {entry["id"]: entry for entry in curated_tables(path)}


def curated_table(table_id: str, path: Optional[Path] = None) -> Optional[Table]:
    entry = curated_by_id(path).get(table_id)
    if entry is None:
        return None
    from .model import table_from_wire

    return table_from_wire(entry["table"])
