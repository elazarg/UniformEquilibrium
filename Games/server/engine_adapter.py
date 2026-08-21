"""Thin, easily-adjustable adapter between HTTP routes and Games/engine/.

Games/engine/ is built by a separate agent in parallel and may not exist
yet, or may only partially exist. Every access goes through get_module(),
which imports lazily so the server can start and serve static files/400s
regardless of engine readiness -- an EngineUnavailable is only raised when a
specific capability is actually requested by a route.

Tests inject stub submodules directly into sys.modules (e.g.
sys.modules["engine.evaluator"] = fake_module) before calling routes; no
real engine/ package is required for that to work.

Actual engine surface (confirmed against the landed Games/engine/ package;
each wrapper below isolates one call site so a future signature change only
touches this file):
    engine.evaluator.evaluate(table, hazards) -> dict (POST /api/evaluate shape)
    engine.filters.api_report(table, margin=0.1) -> dict (POST /api/filters shape, verbatim)
    engine.battery.run_level(table, level=..., profiles=(), abandon_at=None) -> dict
        (POST /api/attack shape; handles every level including "deep" itself)
    engine.battery.tier_for(score, level, exact=False, eps_kill=0.02) -> str
    engine.battery.status_for(score, level, eps_kill=0.02) -> str
    engine.battery.killing_profile(result, eps_kill=0.02) -> dict | None
    engine.library.replay_profiles(table, profiles) -> dict {"exploitability", "profile", ...}
    engine.curated.curated_tables() -> list[dict] (GET /api/tables/curated "tables")
    engine.rational.harden(table, hazards, eps_kill=0.02) -> dict (POST /api/harden)
"""
from __future__ import annotations

import importlib
from typing import Any


class EngineUnavailable(Exception):
    """Raised when a required engine.<name> submodule cannot be imported."""


def get_module(name: str) -> Any:
    try:
        return importlib.import_module(f"engine.{name}")
    except ImportError as exc:
        raise EngineUnavailable(f"engine.{name} not ready") from exc


def evaluate(table, profile):
    return get_module("evaluator").evaluate(table, profile["hazards"])


def run_battery(table, level, library_profiles=()):
    return get_module("battery").run_level(table, level=level, profiles=library_profiles)


def run_filters(table, margin=0.1):
    # engine.filters.api_report already returns the DESIGN.md wire shape
    # directly ({"pass", "pass_1_to_5", "margin", "first_failing", "filters":
    # {<six verbatim FILTER_NAMES keys>}}), so no reshaping is needed here.
    return get_module("filters").api_report(table, margin=margin)


def replay(table, profiles):
    return get_module("library").replay_profiles(table, profiles)


def load_curated():
    return get_module("curated").curated_tables()


def harden(table, profile):
    return get_module("rational").harden(table, profile["hazards"])


def tier_for(score, level, exact=False):
    return get_module("battery").tier_for(score, level, exact=exact)


def status_for(score, level):
    return get_module("battery").status_for(score, level)


def killing_profile(result):
    return get_module("battery").killing_profile(result)
