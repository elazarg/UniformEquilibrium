"""Table and profile types, masks, validation, and hashing.

The mathematical model is fixed at four players.  A *table* is indexed by the
coalition bitmask of the players who quit; bit ``i`` set means player ``i``
quits.  Mask ``0`` is the no-absorption row and is always zero.  A *profile* is
a periodic per-player hazard matrix ``hazards[phase][player]``.

Everything here is a pure function.  The wire formats are the ones fixed by
``Games/DESIGN.md``: a table travels as sixteen rows of four numbers, a profile
as ``{"period": P, "hazards": [[h0, h1, h2, h3], ...]}``.
"""

from __future__ import annotations

import hashlib
import json
import math
from typing import Any, Iterable, Sequence

N = 4
PLAYERS = tuple(range(N))
MASKS = tuple(range(1 << N))
NONEMPTY = tuple(range(1, 1 << N))

PAYOFF_LO = -4.0
PAYOFF_HI = 4.0

#: Exploitability at or below which a table counts as killed (DESIGN.md).
EPS_KILL = 0.02
#: Filter margin ``g`` used by the necessary-condition screens.
MARGIN_G = 0.1
#: Largest period accepted on the wire.
MAX_PERIOD = 8

Vector = tuple[float, ...]
Table = tuple[Vector, ...]
Hazards = Sequence[Sequence[float]]


class ModelError(ValueError):
    """Raised when supplied data is not a legal table or profile.

    Subclasses :class:`ValueError`, and its message is written to be shown to
    whoever sent the bad data.
    """


#: Alias for callers that prefer to catch a name ending in ``ValidationError``.
#: The canonical name is :class:`ModelError`; both are the same class, so
#: ``except model.ValidationError`` and ``except model.ModelError`` catch the
#: same failures.
ValidationError = ModelError


def mask_of(players: Iterable[int]) -> int:
    answer = 0
    for who in players:
        answer |= 1 << who
    return answer


def members(mask: int) -> tuple[int, ...]:
    return tuple(i for i in PLAYERS if mask >> i & 1)


def mask_label(mask: int) -> str:
    """The ``{1,3}`` style one-based label used by the experiment results."""

    return "{" + ",".join(str(i + 1) for i in members(mask)) + "}"


def solo(table: Table, i: int) -> float:
    """Player ``i``'s payoff when ``i`` quits alone."""

    return table[1 << i][i]


def clamp_payoff(value: float) -> float:
    return min(PAYOFF_HI, max(PAYOFF_LO, value))


def table_from_dict(entries: dict[tuple[int, ...], Sequence[float]]) -> Table:
    """Build a table from a ``{(0, 1): payoff}`` coalition dictionary."""

    rows: list[Vector] = [(0.0,) * N for _ in MASKS]
    for coalition, payoff in entries.items():
        rows[mask_of(coalition)] = tuple(float(x) for x in payoff)
    return tuple(rows)


def _number(value: Any, where: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ModelError(f"{where}: expected a number, got {value!r}")
    number = float(value)
    if number != number or number in (float("inf"), float("-inf")):
        raise ModelError(f"{where}: expected a finite number, got {value!r}")
    return number


def table_from_wire(payload: Any) -> Table:
    """Validate and convert the wire table format (16 rows of 4 numbers)."""

    if not isinstance(payload, (list, tuple)):
        raise ModelError("table: expected an array of 16 rows")
    if len(payload) != len(MASKS):
        raise ModelError(f"table: expected {len(MASKS)} rows, got {len(payload)}")
    rows: list[Vector] = []
    for mask, row in enumerate(payload):
        if not isinstance(row, (list, tuple)) or len(row) != N:
            raise ModelError(f"table row {mask}: expected {N} numbers")
        values = tuple(
            _number(entry, f"table row {mask} entry {i}")
            for i, entry in enumerate(row)
        )
        for value in values:
            if value < PAYOFF_LO or value > PAYOFF_HI:
                raise ModelError(
                    f"table row {mask}: {value} outside "
                    f"[{PAYOFF_LO}, {PAYOFF_HI}]"
                )
        rows.append(values)
    if any(value != 0.0 for value in rows[0]):
        raise ModelError("table row 0 (nobody quits) must be all zeros")
    return tuple(rows)


def table_to_wire(table: Table) -> list[list[float]]:
    return [list(row) for row in table]


def table_from_labels(entries: dict[str, Sequence[float]]) -> Table:
    """Read the ``{"{1,3}": [...]}`` format used by the experiment results."""

    rows: list[Vector] = [(0.0,) * N for _ in MASKS]
    for label, payoff in entries.items():
        tokens = [token for token in label.strip("{}").split(",") if token.strip()]
        coalition = [int(token) - 1 for token in tokens]
        rows[mask_of(coalition)] = tuple(float(x) for x in payoff)
    return tuple(rows)


def table_to_labels(table: Table) -> dict[str, list[float]]:
    return {mask_label(mask): list(table[mask]) for mask in NONEMPTY}


def hazards_from_wire(payload: Any) -> list[list[float]]:
    """Validate and convert the wire profile format to a hazard matrix."""

    if not isinstance(payload, dict):
        raise ModelError("profile: expected an object with period and hazards")
    hazards = payload.get("hazards")
    if not isinstance(hazards, (list, tuple)) or not hazards:
        raise ModelError("profile: hazards must be a non-empty array")
    period = payload.get("period", len(hazards))
    if isinstance(period, bool) or not isinstance(period, int):
        raise ModelError("profile: period must be an integer")
    if period != len(hazards):
        raise ModelError(
            f"profile: period {period} disagrees with {len(hazards)} rows"
        )
    if not 1 <= period <= MAX_PERIOD:
        raise ModelError(f"profile: period must be in 1..{MAX_PERIOD}")
    matrix: list[list[float]] = []
    for t, row in enumerate(hazards):
        if not isinstance(row, (list, tuple)) or len(row) != N:
            raise ModelError(f"profile phase {t}: expected {N} hazards")
        values = [
            _number(entry, f"profile phase {t} player {i}")
            for i, entry in enumerate(row)
        ]
        for value in values:
            if value < 0.0 or value > 1.0:
                raise ModelError(f"profile phase {t}: hazard {value} outside [0, 1]")
        matrix.append(values)
    return matrix


def hazards_to_wire(hazards: Hazards) -> dict[str, Any]:
    rows = [[float(value) for value in row] for row in hazards]
    return {"period": len(rows), "hazards": rows}


#: What DESIGN.md's wire contract sends instead of ``inf``.  A score at or
#: above it means "this attack found no bound", not a real exploitability.
NO_BOUND = 1e9


def json_safe(payload: Any) -> Any:
    """Recursively replace non-finite floats, per DESIGN.md's wire contract.

    The battery uses ``inf`` as the identity of its running minimum, which is
    a fine Python value and not a JSON one: ``json.dumps`` writes it as the
    non-standard ``Infinity``, which strict parsers -- including a browser's
    ``JSON.parse`` -- reject.  Everything crossing the wire or reaching a
    ledger file goes through here first.

    The substitutions are the ones DESIGN.md fixes for the HTTP API, so the
    same value reads the same whether a client got it live from the server or
    later from the ledger: ``inf`` becomes ``NO_BOUND``, ``-inf`` becomes
    ``-NO_BOUND``, and ``nan`` becomes ``null``.  A consumer must therefore
    read a score at or above ``NO_BOUND`` as "nothing found", never as a
    number to compare against ``eps_kill``.
    """

    if isinstance(payload, float):
        if math.isnan(payload):
            return None
        if payload == math.inf:
            return NO_BOUND
        if payload == -math.inf:
            return -NO_BOUND
        return payload
    if isinstance(payload, dict):
        return {key: json_safe(value) for key, value in payload.items()}
    if isinstance(payload, (list, tuple)):
        return [json_safe(value) for value in payload]
    return payload


def validate_table(payload: Any) -> None:
    """Raise :class:`ModelError` unless ``payload`` is a legal wire table.

    A validate-only wrapper for callers that keep the payload as it arrived;
    :func:`table_from_wire` does the same checks and hands back the converted
    table, so prefer it when the value is about to be used.
    """

    table_from_wire(payload)


def validate_profile(payload: Any) -> None:
    """Raise :class:`ModelError` unless ``payload`` is a legal wire profile.

    The converting form is :func:`hazards_from_wire`.
    """

    hazards_from_wire(payload)


def canonical_json(payload: Any) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def table_hash(table: Table) -> str:
    """Stable content hash of a table; used to key library kills."""

    return hashlib.sha256(
        canonical_json(table_to_wire(table)).encode("utf-8")
    ).hexdigest()


def profile_hash(hazards: Hazards) -> str:
    return hashlib.sha256(
        canonical_json(hazards_to_wire(hazards)).encode("utf-8")
    ).hexdigest()


def seed_table() -> Table:
    """Solan-Vieille (2001) Section 3 table, players indexed 0..3 for 1..4."""

    return table_from_dict(
        {
            (0,): (1, 4, 0, 0),
            (1,): (4, 1, 0, 0),
            (2,): (0, 0, 1, 4),
            (3,): (0, 0, 4, 1),
            (0, 1): (1, 1, 1, 1),
            (0, 2): (1, 1, 1, 0),
            (0, 3): (1, 0, 1, 1),
            (1, 2): (0, 1, 1, 1),
            (1, 3): (1, 1, 0, 1),
            (2, 3): (1, 1, 1, 1),
            (0, 1, 2): (1, 0, 0, 0),
            (0, 1, 3): (0, 1, 0, 0),
            (0, 2, 3): (0, 0, 0, 1),
            (1, 2, 3): (0, 0, 1, 0),
            (0, 1, 2, 3): (-1, -1, -1, -1),
        }
    )
