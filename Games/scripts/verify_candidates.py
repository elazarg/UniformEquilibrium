#!/usr/bin/env python3
"""Offline deep re-attack of proposed candidates.

Reads ``Games/data/candidates.jsonl``, replays the attacker library against
every proposed candidate and then hammers it with the deep battery, and appends
one update line per candidate recording the verdict.  Nothing is ever rewritten
in place: status changes are append-only update lines merged on read, so the
ledger keeps its full history.

What a verdict means:

* ``killed`` -- some profile in the searched families is an approximate
  equilibrium good enough to spoil the candidate, at or below ``eps_kill``.
  That is a positive finding about one profile and it is reliable up to
  floating point, or exact when the rational hardening succeeds.
* ``verified`` -- the deep battery found nothing.  That records bounded search
  effort over four parameterized families and is *not* evidence that no
  approximate equilibrium exists.

Run it standalone from anywhere:

    python3 Games/scripts/verify_candidates.py
"""

from __future__ import annotations

import argparse
import datetime
import json
import sys
import uuid
from pathlib import Path
from typing import Any, Callable, Iterable, Optional

GAMES_DIR = Path(__file__).resolve().parents[1]
if str(GAMES_DIR) not in sys.path:
    sys.path.insert(0, str(GAMES_DIR))

from engine import battery, model, rational  # noqa: E402

DEFAULT_DATA_DIR = GAMES_DIR / "data"
CANDIDATES_FILE = "candidates.jsonl"
PROFILES_FILE = "profiles.jsonl"


def now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).isoformat(
        timespec="seconds"
    ).replace("+00:00", "Z")


def read_lines(path: Path) -> list[dict]:
    """Every well-formed JSON object in a JSONL file, in file order."""

    if not path.exists():
        return []
    entries: list[dict] = []
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            try:
                payload = json.loads(line)
            except ValueError:
                continue
            if isinstance(payload, dict):
                entries.append(payload)
    return entries


def merge_records(lines: Iterable[dict]) -> list[dict]:
    """Fold append-only update lines into their records, oldest first.

    A line carrying ``update`` patches the record with the same ``id``; an
    update for an unknown id is kept aside rather than dropped, so a partial
    file never silently loses information.
    """

    records: dict[str, dict] = {}
    order: list[str] = []
    orphans: list[dict] = []
    for line in lines:
        identifier = line.get("id")
        if not isinstance(identifier, str):
            continue
        if "update" in line:
            record = records.get(identifier)
            if record is None:
                orphans.append(line)
                continue
            update = line["update"]
            if isinstance(update, dict):
                record.update(update)
            if "updated" in line:
                record["updated"] = line["updated"]
            continue
        if identifier not in records:
            records[identifier] = dict(line)
            order.append(identifier)
        else:
            records[identifier].update(line)
    merged = [records[identifier] for identifier in order]
    for orphan in orphans:
        merged.append({"id": orphan["id"], "orphan_update": orphan["update"]})
    return merged


def load_candidates(data_dir: Path) -> list[dict]:
    return merge_records(read_lines(data_dir / CANDIDATES_FILE))


def load_library(data_dir: Path) -> list[dict]:
    """Profiles from the shared library, newest last, deduplicated."""

    profiles: list[dict] = []
    seen: set[str] = set()
    for record in merge_records(read_lines(data_dir / PROFILES_FILE)):
        profile = record.get("profile")
        if not isinstance(profile, dict):
            continue
        try:
            hazards = model.hazards_from_wire(profile)
        except model.ModelError:
            continue
        digest = model.profile_hash(hazards)
        if digest in seen:
            continue
        seen.add(digest)
        profiles.append(record)
    return profiles


def append_line(path: Path, payload: dict, dry_run: bool = False) -> None:
    if dry_run:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(model.json_safe(payload), sort_keys=False))
        handle.write("\n")


def pending(records: Iterable[dict], statuses: tuple[str, ...]) -> list[dict]:
    chosen = []
    for record in records:
        if "table" not in record or "orphan_update" in record:
            continue
        if record.get("status", "proposed") in statuses:
            chosen.append(record)
    return chosen


def deep_attack(table, profiles) -> dict:
    return battery.run_level(table, "deep", profiles=profiles)


def verify_record(
    record: dict,
    profiles: list[dict],
    eps_kill: float,
    attack: Callable[[Any, list[dict]], dict] = deep_attack,
    harden: bool = True,
) -> dict:
    """Attack one candidate and return the update payload for it.

    The update carries the whole evaluation, the tier, the status, and the
    killing profile when there is one that the library can actually replay.
    """

    table = model.table_from_wire(record["table"])
    result = attack(table, profiles)
    summary = battery.summarize(result, eps_kill)
    killer = summary["killing_profile"]
    exact: Optional[dict] = None
    if harden and killer is not None:
        exact = rational.harden(table, killer["hazards"], eps_kill)
    tier = battery.tier_for(
        summary["score"],
        result["level"],
        exact=bool(exact and exact["kills"]),
        eps_kill=eps_kill,
    )
    update = {
        "evaluation": summary,
        "tier": tier,
        "status": battery.status_for(summary["score"], result["level"], eps_kill),
        "killed_by": killer,
        "verified_level": result["level"],
        "eps_kill": eps_kill,
    }
    if exact is not None:
        update["exact_check"] = {
            "kills": exact["kills"],
            "denominator": exact["denominator"],
            "profile": exact["profile"],
            "exploitability_exact": exact["exploitability_exact"],
            "claim": exact["claim"],
        }
        if exact["kills"]:
            update["killed_by"] = exact["profile"]
    return update


def profile_record(candidate: dict, update: dict) -> Optional[dict]:
    """A library record for the profile that killed this candidate."""

    killer = update.get("killed_by")
    if not killer:
        return None
    return {
        "id": str(uuid.uuid4()),
        "created": now(),
        "profile": killer,
        "source": {
            "game": "verify_candidates",
            "session": None,
            "candidate_id": candidate.get("id"),
        },
        "kills": [
            {
                "candidate_id": candidate.get("id"),
                "table_hash": model.table_hash(
                    model.table_from_wire(candidate["table"])
                ),
                "score": update["evaluation"]["score"],
            }
        ],
    }


def run(
    data_dir: Path,
    limit: Optional[int] = None,
    eps_kill: float = model.EPS_KILL,
    statuses: tuple[str, ...] = ("proposed",),
    dry_run: bool = False,
    record_profiles: bool = True,
    attack: Callable[[Any, list[dict]], dict] = deep_attack,
    harden: bool = True,
    log: Callable[[str], None] = print,
) -> list[dict]:
    candidates_path = data_dir / CANDIDATES_FILE
    profiles_path = data_dir / PROFILES_FILE
    records = load_candidates(data_dir)
    library = load_library(data_dir)
    queue = pending(records, statuses)
    if limit is not None:
        queue = queue[:limit]
    log(
        f"{len(records)} candidates on file, {len(library)} library profiles, "
        f"{len(queue)} to verify at eps_kill {eps_kill}"
    )
    updates: list[dict] = []
    for candidate in queue:
        try:
            update = verify_record(candidate, library, eps_kill, attack, harden)
        except model.ModelError as error:
            log(f"  {candidate.get('id')}: skipped, {error}")
            continue
        line = {"id": candidate["id"], "update": update, "updated": now()}
        append_line(candidates_path, line, dry_run)
        updates.append(line)
        evaluation = update["evaluation"]
        exact = update.get("exact_check")
        log(
            f"  {candidate['id']}: {update['status']} at "
            f"{evaluation['score']:.6g} "
            f"(binding {evaluation['binding_attack']}, tier {update['tier']}"
            + (
                f", exact denominator {exact['denominator']}"
                if exact and exact["kills"]
                else ""
            )
            + f", {evaluation['elapsed']:.1f}s)"
        )
        if record_profiles:
            entry = profile_record(candidate, update)
            if entry is not None:
                append_line(profiles_path, entry, dry_run)
                library.append(entry)
    log(
        f"appended {len(updates)} update line(s)"
        + (" (dry run: nothing written)" if dry_run else "")
    )
    return updates


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--data-dir",
        type=Path,
        default=DEFAULT_DATA_DIR,
        help="directory holding candidates.jsonl and profiles.jsonl",
    )
    parser.add_argument(
        "--limit", type=int, default=None, help="verify at most this many candidates"
    )
    parser.add_argument(
        "--eps-kill",
        type=float,
        default=model.EPS_KILL,
        help="exploitability at or below which a candidate is killed",
    )
    parser.add_argument(
        "--status",
        action="append",
        default=None,
        help="candidate status to verify; repeatable (default: proposed)",
    )
    parser.add_argument(
        "--level",
        choices=("quick", "standard", "deep"),
        default="deep",
        help="attack level; the deep level is the point of this script",
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="attack but write nothing"
    )
    parser.add_argument(
        "--no-record-profiles",
        action="store_true",
        help="do not append killing profiles to the shared library",
    )
    parser.add_argument(
        "--no-harden",
        action="store_true",
        help="skip the exact rational re-verification of killing profiles",
    )
    args = parser.parse_args(argv)

    level = args.level

    def attack(table, profiles) -> dict:
        return battery.run_level(table, level, profiles=profiles)

    run(
        data_dir=args.data_dir,
        limit=args.limit,
        eps_kill=args.eps_kill,
        statuses=tuple(args.status) if args.status else ("proposed",),
        dry_run=args.dry_run,
        record_profiles=not args.no_record_profiles,
        attack=attack,
        harden=not args.no_harden,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
