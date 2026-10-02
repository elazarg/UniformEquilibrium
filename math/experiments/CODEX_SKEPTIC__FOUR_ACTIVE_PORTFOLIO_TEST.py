"""One exact four-active portfolio refinement; repository engine is read-only.

Run with PYTHONDONTWRITEBYTECODE=1. All generated data stay beside this file.
No floating-point value accepts a mathematical assertion.
"""

from fractions import Fraction as Q
from itertools import combinations, permutations, product
from pathlib import Path
import sys
import time


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
sys.path.insert(0, str(REPOSITORY / "Experiments" / "fin4_exact_search"))
from fin4_exact_search.engine import (
    ProfileCertificate, RationalLaw, RewardTable, UpperSearch,
    load_reward_table, qjson, read_json, terminal_semantics, write_json_atomic,
)
from CODEX_SKEPTIC__FINITE_PORTFOLIO_REGRESSIONS import (
    exact_exploitability, regret_rows, evaluate,
)


STEM = "CODEX_SKEPTIC__FOUR_ACTIVE"
TABLE = HERE / f"{STEM}_TABLE.json"
PORTFOLIO = HERE / f"{STEM}_PORTFOLIO.json.gz"
REPORT = HERE / f"{STEM}_REPORT.json"
CERTIFICATE = HERE / f"{STEM}_UPPER_CERTIFICATE.json.gz"
STATE = HERE / f"{STEM}_UPPER_STATE.json.gz"
OUTER_ERROR = Q(1, 5)
UPPER_TARGET = Q(1, 8)


def reward_table():
    """Player 0 is strategic; players 1,2,3 form a cyclic binary game."""
    predecessor = {1: 3, 2: 1, 3: 2}
    rows = []
    for mask in range(1, 16):
        if mask & 1:
            row = [Q(-1 if mask == 15 else 1)]
            for i in range(1, 4):
                pred_quits = bool(mask & (1 << predecessor[i]))
                if mask & (1 << i):
                    row.append(Q(-1 if pred_quits else 1))
                else:
                    row.append(Q(int(pred_quits)))
        else:
            row = [Q(int(mask == 14))]
            for i in range(1, 4):
                row.append(Q(0 if not mask & (1 << i)
                             else 1 if mask == 1 << i else -1))
        rows.append(tuple(row))
    return RewardTable(tuple(rows))


def pure_law(clock, date):
    return RationalLaw.pure(clock, date)


def half_cycle(order, rounds=4):
    clock = len(order) * rounds
    remaining = [Q(1)] * 4
    finite = [[Q(0)] * clock for _ in range(4)]
    for date, player in enumerate(order * rounds):
        finite[player][date] = remaining[player] / 2
        remaining[player] /= 2
    return tuple(RationalLaw(clock, tuple(finite[i]), remaining[i])
                 for i in range(4))


def portfolio():
    result = []
    for counts in product(range(3), repeat=4):
        laws = tuple(RationalLaw(1, (Q(c, 2),), Q(2-c, 2)) for c in counts)
        result.append(("ONE_DATE_" + "".join(map(str, counts)), laws))
    for size in (3, 4):
        for active in combinations(range(4), size):
            for order in permutations(active):
                result.append(("HALF_CYCLE_" + "".join(map(str, order)),
                               half_cycle(order)))
    for quitter in range(4):
        for punisher in range(4):
            if quitter == punisher:
                continue
            laws = [pure_law(5, None) for _ in range(4)]
            laws[quitter] = pure_law(5, 0)
            laws[punisher] = RationalLaw(5, (Q(0), *(Q(1, 4) for _ in range(4))), Q(0))
            result.append((f"COMPARISON_{quitter}_{punisher}", tuple(laws)))
    assert len(result) == 141
    return result


def own_laws(laws):
    return [{**{t: mass for t, mass in enumerate(law.finite) if mass},
             **({None: law.never} if law.never else {})} for law in laws]


def active_contexts(table):
    contexts = []
    for i in range(4):
        gains = []
        for mask in range(16):
            if mask & (1 << i):
                continue
            old = Q(0) if mask == 0 else table(mask, i)
            gains.append((table(mask | (1 << i), i) - old, mask))
        positive = max(gains)
        negative = min(gains)
        assert positive[0] > 0 > negative[0]
        assert table(1 << i, i) == 1
        contexts.append({"player": i, "join_background": positive[1],
                         "join_gain": qjson(positive[0]),
                         "leave_background": negative[1],
                         "leave_gain": qjson(-negative[0])})
    return contexts


def prepare():
    table = reward_table()
    table.validate_normalized()
    contexts = active_contexts(table)
    profiles = portfolio()
    records = []
    for name, laws in profiles:
        payoff, cap, debt, error = terminal_semantics(table, laws)
        records.append({"name": name, "clock_bound": laws[0].clock_bound,
                        "laws": [law.to_json() for law in laws],
                        "payoff": list(map(qjson, payoff)),
                        "cap": list(map(qjson, cap)),
                        "debt": list(map(qjson, debt)),
                        "exploitability": qjson(error)})
    minimum = min(Q(record["exploitability"]) for record in records)
    assert minimum > OUTER_ERROR, (minimum, OUTER_ERROR)
    attaining = [record["name"] for record in records
                 if Q(record["exploitability"]) == minimum]
    first = next((laws for name, laws in profiles if name == attaining[0]))
    independently = exact_exploitability(own_laws(first), first[0].clock_bound,
                                        tuple(x for row in table.values for x in row))
    assert independently == minimum
    write_json_atomic(TABLE, table.to_json())
    write_json_atomic(PORTFOLIO, {"profiles": records})
    report = {"table_hash": table.digest, "four_active_contexts": contexts,
              "portfolio_count": len(records), "outer_error": qjson(OUTER_ERROR),
              "upper_target": qjson(UPPER_TARGET),
              "portfolio_minimum": qjson(minimum), "minimum_profiles": attaining,
              "status": "exact_uncovered_table_prepared"}
    write_json_atomic(REPORT, report)
    print("Prepared", len(records), "profiles; exact minimum", minimum,
          "; outer target", OUTER_ERROR, flush=True)
    print("Minimum profiles:", ", ".join(attaining), flush=True)


def search():
    table = load_reward_table(TABLE)
    assert table == reward_table()
    report = read_json(REPORT)
    searcher = UpperSearch(table, UPPER_TARGET)
    started = time.monotonic()
    result = None
    quanta = 0
    while quanta < 2000 and time.monotonic() - started < 45:
        result = searcher.step()
        quanta += 1
        if result is not None:
            break
    write_json_atomic(STATE, searcher.to_state_json())
    report.update({"upper_quanta": quanta, "upper_profiles_tested": searcher.steps,
                   "upper_elapsed_seconds": time.monotonic() - started})
    if result is None:
        report["status"] = "bounded_upper_search_incomplete"
        write_json_atomic(REPORT, report)
        print("Incomplete bounded upper search after", searcher.steps, "profiles")
        return
    result.verify()
    write_json_atomic(CERTIFICATE, result.to_json())
    report["status"] = "upper_certificate_found_pending_cell_verification"
    write_json_atomic(REPORT, report)
    print("Upper certificate found:", result.exploitability,
          "clock", result.clock_bound, "after", searcher.steps, "profiles", flush=True)


def verify():
    table = load_reward_table(TABLE)
    assert table == reward_table()
    report = read_json(REPORT)
    stored = read_json(PORTFOLIO)["profiles"]
    expected = portfolio()
    assert len(stored) == len(expected)
    old_errors = []
    for record, (name, laws) in zip(stored, expected):
        assert record["name"] == name
        assert record["laws"] == [law.to_json() for law in laws]
        semantics = terminal_semantics(table, laws)
        assert list(map(qjson, semantics[0])) == record["payoff"]
        assert list(map(qjson, semantics[1])) == record["cap"]
        assert list(map(qjson, semantics[2])) == record["debt"]
        assert qjson(semantics[3]) == record["exploitability"]
        old_errors.append(semantics[3])
    certificate = ProfileCertificate.from_json(read_json(CERTIFICATE))
    certificate.verify()
    reward = tuple(x for row in table.values for x in row)
    decoded = own_laws(certificate.laws)
    rows = regret_rows(decoded, certificate.clock_bound)
    independent = max(Q(0), *(evaluate(row, reward) for row in rows))
    assert independent == certificate.exploitability
    radius = min(Q(1, 64), (min(old_errors)-OUTER_ERROR)/4,
                 (OUTER_ERROR-independent)/4)
    assert radius > 0
    old_lower = min(old_errors)-2*radius
    new_upper = independent+2*radius
    assert new_upper < OUTER_ERROR < old_lower
    lower = [max(Q(-1), r-radius) for r in reward]
    upper = [min(Q(1), r+radius) for r in reward]
    report.update({"status": "exact_uncovered_cell_reduced", "radius": qjson(radius),
                   "box_lower": list(map(qjson, lower)),
                   "box_upper": list(map(qjson, upper)),
                   "old_portfolio_regret_lower_on_box": qjson(old_lower),
                   "new_profile_regret_upper_on_box": qjson(new_upper),
                   "new_profile_exploitability": qjson(independent),
                   "new_profile_clock": certificate.clock_bound})
    write_json_atomic(REPORT, report)
    print("Exact independent profile check:", independent, flush=True)
    print("Full reward box radius", radius, ": old >=", old_lower,
          ">", OUTER_ERROR, "> new <=", new_upper, flush=True)


if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in {"prepare", "search", "verify"}:
        raise SystemExit("Usage: FOUR_ACTIVE_PORTFOLIO_TEST.py prepare|search|verify")
    {"prepare": prepare, "search": search, "verify": verify}[sys.argv[1]]()
