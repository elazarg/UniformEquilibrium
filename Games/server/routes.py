"""Route handlers for the JSON API described in Games/DESIGN.md.

Each handler has signature (ctx, path_params, query, body) -> (status, payload).
HTTP dispatch, routing, and JSON (de)serialization live in server.handler;
this module is pure request-to-response logic so it's easy to unit test
without spinning up a real socket.
"""
from __future__ import annotations

import uuid
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional

from server import engine_adapter as engine
from server import validation
from server.jobs import JobRegistry
from server.persistence import Storage


class ApiError(Exception):
    """Carries the HTTP status a route wants; server.handler renders it as JSON."""

    def __init__(self, status: int, message: str):
        super().__init__(message)
        self.status = status


@dataclass
class Context:
    games_root: Path
    storage: Storage
    jobs: JobRegistry


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _require(body: Optional[Dict[str, Any]], key: str) -> Any:
    if body is None or key not in body:
        raise ApiError(400, f"missing '{key}'")
    return body[key]


def _validated_table(body: Optional[Dict[str, Any]]) -> Any:
    table = _require(body, "table")
    try:
        validation.validate_table(table)
    except validation.ValidationError as e:
        raise ApiError(400, str(e)) from e
    return table


def _validated_profile(body: Optional[Dict[str, Any]]) -> Any:
    profile = _require(body, "profile")
    try:
        validation.validate_profile(profile)
    except validation.ValidationError as e:
        raise ApiError(400, str(e)) from e
    return profile


def _engine_call(fn, *args, **kwargs):
    try:
        return fn(*args, **kwargs)
    except engine.EngineUnavailable as e:
        raise ApiError(503, "engine not ready") from e


def _library_profiles(ctx: Context):
    """The full attacker library: every profile ever submitted via
    POST /api/profiles, as stored records (not bare wire profiles) so the
    engine can report which stored profile matched via its "source" field.
    Per DESIGN.md, this is replayed against every table an attack touches.
    """
    return ctx.storage.list_profiles(limit=None)


# --- POST /api/evaluate -----------------------------------------------------

def evaluate(ctx: Context, path_params, query, body):
    table = _validated_table(body)
    profile = _validated_profile(body)
    result = _engine_call(engine.evaluate, table, profile)
    return 200, result


# --- POST /api/attack, GET /api/jobs/<id> -----------------------------------

def attack(ctx: Context, path_params, query, body):
    table = _validated_table(body)
    level = body.get("level", "standard") if body else "standard"
    try:
        validation.validate_attack_level(level)
    except validation.ValidationError as e:
        raise ApiError(400, str(e)) from e

    library_profiles = _library_profiles(ctx)

    if level == "deep":
        job_id = ctx.jobs.submit(engine.run_battery, table, "deep", library_profiles)
        return 200, {"job": job_id}

    result = _engine_call(engine.run_battery, table, level, library_profiles)
    return 200, result


def job_status(ctx: Context, path_params, query, body):
    job_id = path_params["job_id"]
    job = ctx.jobs.get(job_id)
    if job is None:
        raise ApiError(404, "unknown job id")
    return 200, job


# --- POST /api/attack_batch --------------------------------------------------

def attack_batch(ctx: Context, path_params, query, body):
    tables = _require(body, "tables")
    if not isinstance(tables, list) or not tables:
        raise ApiError(400, "'tables' must be a non-empty list")
    for i, t in enumerate(tables):
        try:
            validation.validate_table(t)
        except validation.ValidationError as e:
            raise ApiError(400, f"tables[{i}]: {e}") from e
    level = body.get("level", "replay")
    try:
        validation.validate_attack_level(level, allowed=validation.BATCH_LEVELS)
    except validation.ValidationError as e:
        raise ApiError(400, str(e)) from e
    library_profiles = _library_profiles(ctx)
    results = [_engine_call(engine.run_battery, t, level, library_profiles) for t in tables]
    return 200, {"results": results}


# --- POST /api/filters -------------------------------------------------------

def filters(ctx: Context, path_params, query, body):
    table = _validated_table(body)
    result = _engine_call(engine.run_filters, table)
    return 200, result


# --- GET /api/tables/curated --------------------------------------------------

def curated_tables(ctx: Context, path_params, query, body):
    tables = _engine_call(engine.load_curated)
    return 200, {"tables": tables}


# --- POST/GET /api/candidates -------------------------------------------------

def post_candidate(ctx: Context, path_params, query, body):
    table = _validated_table(body)
    game = _require(body, "game")
    session = _require(body, "session")
    provenance = body.get("provenance", {})
    if not isinstance(game, str) or not game:
        raise ApiError(400, "'game' must be a non-empty string")
    if not isinstance(session, str) or not session:
        raise ApiError(400, "'session' must be a non-empty string")
    if not isinstance(provenance, dict):
        raise ApiError(400, "'provenance' must be an object")

    # Authoritative at record time: the server re-scores at standard level
    # regardless of anything the client claims. Never persist client math.
    # The attacker library is replayed against every new candidate first
    # (DESIGN.md): every profile ever submitted via POST /api/profiles.
    evaluation = _engine_call(engine.run_battery, table, "standard", _library_profiles(ctx))
    score = evaluation.get("score")
    if not isinstance(score, (int, float)):
        raise ApiError(502, "engine returned a malformed attack result")

    # Evidence-tier and kill classification are engine domain logic (parity
    # with the reference script's thresholds and per-level survivor tiers is
    # a hard requirement), so it is computed there, not re-derived here.
    tier = _engine_call(engine.tier_for, score, "standard")
    status = _engine_call(engine.status_for, score, "standard")
    killed_by = _engine_call(engine.killing_profile, evaluation) if status == "killed" else None

    record = {
        "id": str(uuid.uuid4()),
        "created": _now(),
        "table": table,
        "game": game,
        "session": session,
        "provenance": provenance,
        "evaluation": evaluation,
        "tier": tier,
        "status": status,
        "killed_by": killed_by,
    }
    ctx.storage.add_candidate(record)
    return 200, {"id": record["id"], "record": record}


def get_candidates(ctx: Context, path_params, query, body):
    limit = 50
    if "limit" in query:
        try:
            limit = int(query["limit"][0])
        except (ValueError, IndexError):
            raise ApiError(400, "'limit' must be an integer")
        if limit <= 0:
            raise ApiError(400, "'limit' must be positive")
    return 200, {"candidates": ctx.storage.list_candidates(limit=limit)}


# --- POST /api/profiles -------------------------------------------------------

def post_profile(ctx: Context, path_params, query, body):
    profile = _validated_profile(body)
    source = _require(body, "source")
    if not isinstance(source, dict):
        raise ApiError(400, "'source' must be an object")
    if "game" not in source or "session" not in source:
        raise ApiError(400, "'source' must include 'game' and 'session'")
    if "table" not in source and "table_id" not in source:
        raise ApiError(400, "'source' must include 'table' or 'table_id'")
    if "table" in source:
        try:
            validation.validate_table(source["table"])
        except validation.ValidationError as e:
            raise ApiError(400, f"source.table: {e}") from e

    record = {
        "id": str(uuid.uuid4()),
        "created": _now(),
        "profile": profile,
        "source": source,
        "kills": [],
    }
    ctx.storage.add_profile(record)
    return 200, {"id": record["id"]}


# --- GET /api/stats -------------------------------------------------------------

def stats(ctx: Context, path_params, query, body):
    candidates = ctx.storage.list_candidates(limit=None)
    profiles = ctx.storage.list_profiles(limit=None)
    scores = [
        c["evaluation"]["score"]
        for c in candidates
        if isinstance(c.get("evaluation"), dict) and isinstance(c["evaluation"].get("score"), (int, float))
    ]
    kills = sum(1 for c in candidates if c.get("status") == "killed")
    games = sorted({c["game"] for c in candidates if c.get("game")})
    return 200, {
        "candidates": len(candidates),
        "best_score": max(scores) if scores else None,
        "library_profiles": len(profiles),
        "kills": kills,
        "games": games,
    }


# --- POST /api/harden ---------------------------------------------------------
# Per DESIGN.md's HTTP API section: rational-snap result from engine.rational
# .harden, backing the "exact" evidence tier and the sequencer's harden action.

def harden(ctx: Context, path_params, query, body):
    table = _validated_table(body)
    profile = _validated_profile(body)
    result = _engine_call(engine.harden, table, profile)
    return 200, result
