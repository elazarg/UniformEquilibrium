"""Append-only JSONL persistence for Games/data/, per Games/DESIGN.md.

Each file holds base records plus, later, `{"id", "update": {...}, "updated":
iso8601}` lines that patch a base record by id. Lines are never rewritten;
`JsonlFile.read_merged` reconstructs current state by folding update lines
onto their base record in file order. Every append is a single write() of one
JSON line plus flush, guarded by a lock, so concurrent writers (request
threads, background jobs) never interleave partial lines.
"""
from __future__ import annotations

import json
import threading
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


class JsonlFile:
    def __init__(self, path: Path):
        self._path = path
        self._lock = threading.Lock()

    def append(self, obj: Dict[str, Any]) -> None:
        line = json.dumps(obj) + "\n"
        with self._lock:
            with self._path.open("a", encoding="utf-8") as f:
                f.write(line)
                f.flush()

    def read_merged(self) -> List[Dict[str, Any]]:
        """Read all lines, merging update lines onto their base record.

        Returns records in first-seen (base-record) order. Matches
        Games/scripts/verify_candidates.py's merge_records: a second
        non-update line sharing an id is merged onto the existing record
        (never replaces it outright, so no field a prior line saw is lost),
        and an update line whose id has no preceding base record is dropped
        -- there is nothing to merge it onto. That last case should not
        arise under normal single-writer-per-id use (both readers of these
        files always append a record before any update to it); the
        underlying file itself is never truncated or rewritten either way,
        so no line is ever actually lost, only left out of this view.

        A line that isn't parseable JSON, or doesn't decode to a JSON object
        with a string "id", is skipped rather than raised -- matching
        merge_records again. Games/data/'s lines can never be removed even
        if one is corrupt (e.g. a process killed mid-append leaving a
        truncated final line), so raising here would turn that single bad
        line into a permanent 500 on every future read with no way to
        recover, which is worse than reading past it.
        """
        with self._lock:
            if not self._path.exists():
                return []
            text = self._path.read_text(encoding="utf-8")

        bases: Dict[str, Dict[str, Any]] = {}
        order: List[str] = []
        for line in text.splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except ValueError:
                continue
            if not isinstance(obj, dict):
                continue
            obj_id = obj.get("id")
            if not isinstance(obj_id, str):
                continue
            if "update" in obj:
                if obj_id in bases:
                    bases[obj_id].update(obj["update"])
                    if "updated" in obj:
                        bases[obj_id]["updated"] = obj["updated"]
                continue  # orphan update (no known base yet): deliberately
                # dropped from this view, not preserved as a stub record like
                # verify_candidates.py's merge_records does -- see the
                # docstring above for why. The line itself is never lost;
                # it's still sitting in the file, just excluded from here.
            if obj_id not in bases:
                order.append(obj_id)
                bases[obj_id] = obj
            else:
                bases[obj_id].update(obj)
        return [bases[i] for i in order]


class Storage:
    """Owns candidates.jsonl and profiles.jsonl under Games/data/."""

    def __init__(self, data_dir: Path):
        self.data_dir = data_dir
        self.data_dir.mkdir(parents=True, exist_ok=True)
        self.candidates = JsonlFile(self.data_dir / "candidates.jsonl")
        self.profiles = JsonlFile(self.data_dir / "profiles.jsonl")

    def add_candidate(self, record: Dict[str, Any]) -> None:
        self.candidates.append(record)

    def update_candidate(self, candidate_id: str, update: Dict[str, Any]) -> None:
        self.candidates.append({"id": candidate_id, "update": update, "updated": _now()})

    def list_candidates(self, limit: Optional[int] = 50) -> List[Dict[str, Any]]:
        records = list(reversed(self.candidates.read_merged()))  # newest first
        return records[:limit] if limit is not None else records

    def add_profile(self, record: Dict[str, Any]) -> None:
        self.profiles.append(record)

    def update_profile(self, profile_id: str, update: Dict[str, Any]) -> None:
        self.profiles.append({"id": profile_id, "update": update, "updated": _now()})

    def list_profiles(self, limit: Optional[int] = None) -> List[Dict[str, Any]]:
        records = list(reversed(self.profiles.read_merged()))  # newest first
        return records[:limit] if limit is not None else records
