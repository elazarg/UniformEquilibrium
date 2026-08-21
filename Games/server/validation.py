"""Wire-format validation for Games/DESIGN.md request bodies.

Deliberately independent of Games/engine/: these are structural and range
checks the server can and must perform itself, so malformed requests get a
clear 400 even when the engine package isn't available yet (see
server.engine_adapter for the separate 503-when-engine-missing path).
"""
from __future__ import annotations

from typing import Any, Sequence

TABLE_ROWS = 16
TABLE_COLS = 4
VALUE_MIN, VALUE_MAX = -4.0, 4.0
HAZARD_MIN, HAZARD_MAX = 0.0, 1.0
PERIOD_MIN, PERIOD_MAX = 1, 8

ATTACK_LEVELS = ("replay", "quick", "standard", "deep")
BATCH_LEVELS = ("replay", "quick")


class ValidationError(ValueError):
    """A request body violates the Games/DESIGN.md wire format."""


def _is_number(x: Any) -> bool:
    return isinstance(x, (int, float)) and not isinstance(x, bool)


def validate_table(table: Any) -> None:
    if not isinstance(table, list) or len(table) != TABLE_ROWS:
        raise ValidationError(f"table must be a list of {TABLE_ROWS} rows")
    for i, row in enumerate(table):
        if not isinstance(row, list) or len(row) != TABLE_COLS:
            raise ValidationError(f"table row {i} must be a list of {TABLE_COLS} numbers")
        for j, v in enumerate(row):
            if not _is_number(v):
                raise ValidationError(f"table[{i}][{j}] must be a number")
            if not (VALUE_MIN <= v <= VALUE_MAX):
                raise ValidationError(f"table[{i}][{j}]={v} out of range [{VALUE_MIN}, {VALUE_MAX}]")
    if any(v != 0 for v in table[0]):
        raise ValidationError("table row 0 (empty coalition) must be all zeros")


def validate_profile(profile: Any) -> None:
    if not isinstance(profile, dict):
        raise ValidationError("profile must be an object")
    period = profile.get("period")
    if not isinstance(period, int) or isinstance(period, bool):
        raise ValidationError("profile.period must be an integer")
    if not (PERIOD_MIN <= period <= PERIOD_MAX):
        raise ValidationError(f"profile.period must be in [{PERIOD_MIN}, {PERIOD_MAX}]")
    hazards = profile.get("hazards")
    if not isinstance(hazards, list) or len(hazards) != period:
        raise ValidationError("profile.hazards must have exactly `period` rows")
    for i, row in enumerate(hazards):
        if not isinstance(row, list) or len(row) != TABLE_COLS:
            raise ValidationError(f"profile.hazards[{i}] must be a list of {TABLE_COLS} numbers")
        for j, v in enumerate(row):
            if not _is_number(v):
                raise ValidationError(f"profile.hazards[{i}][{j}] must be a number")
            if not (HAZARD_MIN <= v <= HAZARD_MAX):
                raise ValidationError(
                    f"profile.hazards[{i}][{j}]={v} out of range [{HAZARD_MIN}, {HAZARD_MAX}]"
                )


def validate_attack_level(level: Any, allowed: Sequence[str] = ATTACK_LEVELS) -> None:
    if level not in allowed:
        raise ValidationError(f"level must be one of {list(allowed)}")
