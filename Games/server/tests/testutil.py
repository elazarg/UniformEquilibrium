"""Shared test fixtures: a stub `engine` package injected via sys.modules
(server tests never import or require the real Games/engine/), plus sample
wire-format objects.

Default stub behavior mirrors the landed engine.battery tier/status rules
(see Games/engine/battery.py: tier_for, status_for, killing_profile) closely
enough for route tests to exercise real classification logic without
depending on the actual engine package.
"""
from __future__ import annotations

import sys
import types
from typing import Any, Callable, Dict, Optional

EPS_KILL = 0.02
SURVIVOR_TIERS = {
    "replay": "unattacked",
    "quick": "survivor-quick",
    "standard": "survivor-standard",
    "deep": "survivor-deep",
}


def sample_table():
    table = [[0.0, 0.0, 0.0, 0.0] for _ in range(16)]
    table[1] = [1.0, 0.0, 0.0, 0.0]
    table[2] = [0.0, 1.0, 0.0, 0.0]
    table[15] = [-1.0, -1.0, -1.0, -1.0]
    return table


def sample_profile():
    return {"period": 1, "hazards": [[0.5, 0.5, 0.5, 0.5]]}


def sample_evaluate_result():
    return {
        "exploitability": 0.03,
        "per_player": [0.03, 0.0, 0.0, 0.0],
        "on_path": [0.1, 0.2, 0.3, 0.4],
        "best_deviations": [{"player": 0, "value": 0.13, "policy": [True]}],
    }


def sample_attack_result(score: float = 0.03, level: str = "standard"):
    profile = sample_profile()
    return {
        "score": score,
        "binding_attack": "stationary",
        "level": level,
        "elapsed": 0.01,
        "breakdown": {
            "stationary": {"exploitability": score, "profile": profile},
        },
    }


def _default_tier_for(score, level, exact=False, eps_kill=EPS_KILL):
    if score <= eps_kill:
        if exact:
            return "exact"
        return "numerical-wide" if score < 0.5 * eps_kill else "numerical-narrow"
    return SURVIVOR_TIERS[level]


def _default_status_for(score, level, eps_kill=EPS_KILL):
    if score <= eps_kill:
        return "killed"
    return "verified" if level == "deep" else "proposed"


def _default_killing_profile(result, eps_kill=EPS_KILL):
    if result["score"] > eps_kill:
        return None
    entry = result["breakdown"].get(result["binding_attack"])
    if not entry:
        return None
    return entry.get("profile")


class StubEngine:
    """Installs fake engine.<name> submodules into sys.modules for the
    duration of a `with StubEngine(...) as stub:` block, then restores
    whatever was there before (including nothing).

    Pass callables to override a specific function, e.g.:
        StubEngine(evaluate=lambda table, hazards: {...})
    Every other function gets a harmless working default, so tests only
    need to specify what they care about. Pass `omit=("engine.evaluator",)`
    to simulate that submodule being genuinely unavailable (engine not
    ready): this poisons sys.modules with None, which forces ImportError
    regardless of whether the real engine/ package exists on disk.
    """

    _MODULE_NAMES = ("engine", "engine.evaluator", "engine.battery",
                      "engine.filters", "engine.library", "engine.curated",
                      "engine.rational")

    def __init__(
        self,
        evaluate: Optional[Callable] = None,
        run_level: Optional[Callable] = None,
        tier_for: Optional[Callable] = None,
        status_for: Optional[Callable] = None,
        killing_profile: Optional[Callable] = None,
        api_report: Optional[Callable] = None,
        replay_profiles: Optional[Callable] = None,
        curated_tables: Optional[Callable] = None,
        harden: Optional[Callable] = None,
        omit: tuple = (),
    ):
        self._functions: Dict[str, Dict[str, Callable]] = {
            "engine.evaluator": {
                "evaluate": evaluate or (lambda table, hazards: sample_evaluate_result()),
            },
            "engine.battery": {
                "run_level": run_level or (lambda table, level="standard", profiles=(), abandon_at=None:
                                            sample_attack_result(level=level)),
                "tier_for": tier_for or _default_tier_for,
                "status_for": status_for or _default_status_for,
                "killing_profile": killing_profile or _default_killing_profile,
            },
            "engine.filters": {
                # engine.filters.api_report already returns the DESIGN.md
                # wire shape directly; server.engine_adapter.run_filters is
                # now a pure pass-through, so the stub mirrors that shape too.
                "api_report": api_report or (lambda table, margin=0.1: {
                    "pass": True,
                    "pass_1_to_5": True,
                    "margin": margin,
                    "first_failing": None,
                    "filters": {
                        "1_toggle_instability": {"pass": True},
                        "2_viable_owner": {"pass": True},
                        "3_collider_and_preemptor": {"pass": True},
                        "4_preemption_cycle": {"pass": True},
                        "5_iterated_normal_core": {"pass": True},
                        "6_no_lcp_solution": {"pass": True},
                    },
                }),
            },
            "engine.library": {
                "replay_profiles": replay_profiles or (lambda table, profiles: {"exploitability": 0.5, "profile": None}),
            },
            "engine.curated": {
                "curated_tables": curated_tables or (lambda: []),
            },
            "engine.rational": {
                "harden": harden or (lambda table, hazards, eps_kill=EPS_KILL:
                                      {"profile": {"period": 1, "hazards": hazards}, "exploitability": 0.0, "tier": "exact"}),
            },
        }
        self._omit = set(omit)
        self._saved: Dict[str, Any] = {}

    def __enter__(self):
        for name in self._MODULE_NAMES:
            self._saved[name] = sys.modules.get(name)
        sys.modules["engine"] = types.ModuleType("engine")
        for mod_name, functions in self._functions.items():
            if mod_name in self._omit:
                sys.modules[mod_name] = None  # poison: forces ImportError, real files or not
                continue
            mod = types.ModuleType(mod_name)
            for fn_name, fn in functions.items():
                setattr(mod, fn_name, fn)
            sys.modules[mod_name] = mod
        return self

    def __exit__(self, exc_type, exc, tb):
        for name in self._MODULE_NAMES:
            saved = self._saved.get(name)
            if saved is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = saved
        return False
