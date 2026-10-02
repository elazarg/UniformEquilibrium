"""One exact perturbed cyclic Fin4 refinement, with external engine read-only.

No optimizer, floating-point acceptance, package installation, or campaign.
The only new-profile search is at most five explicit cyclic truncations.
"""

from fractions import Fraction as Q
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "Experiments" / "fin4_exact_search"))
from fin4_exact_search.engine import (
    ProfileCertificate, RationalLaw, RewardTable, qjson, read_json,
    terminal_semantics, write_json_atomic,
)
from CODEX_SKEPTIC__FOUR_ACTIVE_PORTFOLIO_TEST import portfolio, own_laws
from CODEX_SKEPTIC__FINITE_PORTFOLIO_REGRESSIONS import regret_rows, evaluate


STEM = "CODEX_SKEPTIC__MULTIDATE"
TABLE = HERE / f"{STEM}_TABLE.json"
MANIFEST = HERE / f"{STEM}_OLD_PORTFOLIO.json.gz"
REPORT = HERE / f"{STEM}_REPORT.json"
CERTIFICATE = HERE / f"{STEM}_PROFILE_CERTIFICATE.json.gz"
OUTER_ERROR = Q(1, 5000)
UPPER_TARGET = Q(1, 10000)
RADIUS_CAP = Q(1, 100000)
HAZARDS = (Q(1398, 2797), Q(699, 1399), Q(2796, 5593))


def reward_table(perturbed=True):
    passive = (Q(1199, 400) if perturbed else Q(3), Q(3), Q(3))
    rows = []
    for mask in range(1, 16):
        row = []
        for i in range(3):
            pred = bool(mask & (1 << ((i-1) % 3)))
            row.append((Q(1+int(pred)) if mask & (1 << i)
                        else passive[i]*int(pred))/3)
        row.append(Q(1 if mask & 8 else 2, 3))
        rows.append(tuple(row))
    return RewardTable(tuple(rows))


def cycle_laws(rounds):
    clock = 3*rounds
    finite = [[Q(0)]*clock for _ in range(4)]
    never = [Q(1)]*4
    for date in range(clock):
        i = date % 3
        finite[i][date] = never[i]*HAZARDS[i]
        never[i] *= 1-HAZARDS[i]
    return tuple(RationalLaw(clock, tuple(finite[i]), never[i]) for i in range(4))


def phase_check(table):
    """Exact Bellman and root-response check of the motivating infinite cycle."""
    phase_values = []
    for phase in range(3):
        row = []
        for i in range(3):
            if phase == (i-1) % 3:
                passive = Q(1199, 400) if i == 0 else Q(3)
                row.append((1+(passive-1)*HAZARDS[phase])/3)
            else:
                row.append(Q(1, 3))
        row.append(Q(2, 3))
        phase_values.append(tuple(row))
    endpoint_rows = []
    for phase in range(3):
        root_mask = 1 << phase
        hazard = HAZARDS[phase]
        tail = phase_values[(phase+1) % 3]
        prescribed = tuple(hazard*table(root_mask, i)+(1-hazard)*tail[i]
                           for i in range(4))
        assert prescribed == phase_values[phase]
        for i in range(4):
            if i == phase:
                quit, cont = table(root_mask, i), tail[i]
                assert quit == cont == prescribed[i]
            else:
                quit = hazard*table(root_mask | (1 << i), i)+(1-hazard)*table(1 << i, i)
                cont = prescribed[i]
                assert quit <= cont
            endpoint_rows.append({"phase": phase, "player": i,
                                  "quit": qjson(quit), "continue": qjson(cont)})
    return phase_values, endpoint_rows


def run():
    table = reward_table()
    table.validate_normalized()
    base = reward_table(False)
    distance = max(abs(a-b) for row_a, row_b in zip(table.values, base.values)
                   for a, b in zip(row_a, row_b))
    assert distance == Q(1, 1200)
    stationary_floor = Q(1, 300)-2*distance
    assert stationary_floor == Q(1, 600) > OUTER_ERROR
    phases, endpoints = phase_check(table)

    old_profiles = portfolio()
    old_profiles.append(("PREVIOUS_SURE_OWNER_THIRDS", (
        RationalLaw(1, (Q(1),), Q(0)),
        *(RationalLaw(1, (Q(1, 3),), Q(2, 3)) for _ in range(3)),
    )))
    assert len(old_profiles) == 142
    records = []
    for name, laws in old_profiles:
        payoff, cap, debt, error = terminal_semantics(table, laws)
        records.append({"name": name, "clock_bound": laws[0].clock_bound,
                        "laws": [law.to_json() for law in laws],
                        "payoff": list(map(qjson, payoff)),
                        "cap": list(map(qjson, cap)),
                        "debt": list(map(qjson, debt)),
                        "exploitability": qjson(error)})
    old_minimum = min(Q(record["exploitability"]) for record in records)
    assert old_minimum > OUTER_ERROR
    write_json_atomic(TABLE, table.to_json())
    write_json_atomic(MANIFEST, {"profiles": records})

    tests = []
    result = None
    for rounds in range(4, 9):
        laws = cycle_laws(rounds)
        cert = ProfileCertificate.build(table, laws, UPPER_TARGET)
        tests.append({"rounds": rounds, "clock_bound": 3*rounds,
                      "exploitability": qjson(cert.exploitability)})
        print("Cyclic truncation:", rounds, "rounds, E=", cert.exploitability,
              flush=True)
        if cert.exploitability < UPPER_TARGET:
            cert.verify()
            result = cert
            break

    report = {"table_hash": table.digest, "outer_error": qjson(OUTER_ERROR),
              "upper_target": qjson(UPPER_TARGET),
              "old_portfolio_count": len(records),
              "old_portfolio_minimum": qjson(old_minimum),
              "old_minimizers": [record["name"] for record in records
                                 if Q(record["exploitability"]) == old_minimum],
              "distance_from_base": qjson(distance),
              "stationary_floor_from_reviewed_mathematics": qjson(stationary_floor),
              "hazards": list(map(qjson, HAZARDS)),
              "periodic_values": [list(map(qjson, row)) for row in phases],
              "periodic_root_endpoints": endpoints, "truncation_tests": tests,
              "status": "bounded_profile_search_incomplete"}
    if result is None:
        write_json_atomic(REPORT, report)
        print("No strict certificate among the five prescribed truncations")
        return

    independent_rows = regret_rows(own_laws(result.laws), result.clock_bound)
    flat_reward = tuple(x for row in table.values for x in row)
    independent = max(Q(0), *(evaluate(row, flat_reward) for row in independent_rows))
    assert independent == result.exploitability
    assert all(law.never > 0 for law in result.laws)
    assert all(mass < 1 for law in result.laws for mass in law.finite)
    # Use only one quarter of each certified strict center margin.  The first
    # proposed radius 1/100000 failed the old-portfolio margin check; it was
    # rejected before saving any certificate or robustness report.
    radius = min(RADIUS_CAP, (old_minimum-OUTER_ERROR)/4,
                 (OUTER_ERROR-independent)/4,
                 (stationary_floor-OUTER_ERROR)/4)
    assert radius > 0
    old_on_box = old_minimum-2*radius
    new_on_box = independent+2*radius
    stationary_on_box = stationary_floor-2*radius
    assert new_on_box < OUTER_ERROR < min(old_on_box, stationary_on_box)
    write_json_atomic(CERTIFICATE, result.to_json())
    report.update({"status": "exact_multidate_refinement_verified",
                   "new_profile_clock": result.clock_bound,
                   "new_profile_exploitability": qjson(independent),
                   "radius": qjson(radius),
                   "old_portfolio_lower_on_box": qjson(old_on_box),
                   "new_profile_upper_on_box": qjson(new_on_box),
                   "stationary_lower_on_box": qjson(stationary_on_box),
                   "box_lower": [qjson(max(Q(-1), r-radius)) for r in flat_reward],
                   "box_upper": [qjson(min(Q(1), r+radius)) for r in flat_reward]})
    write_json_atomic(REPORT, report)
    print("Old portfolio minimum:", old_minimum, "target:", OUTER_ERROR)
    print("Verified new clock:", result.clock_bound, "; full E:", independent)
    print("Box radius:", radius, "; stationary lower:", stationary_on_box)


def verify():
    table = reward_table()
    assert RewardTable.from_json(read_json(TABLE)) == table
    cert = ProfileCertificate.from_json(read_json(CERTIFICATE))
    cert.verify()
    assert cert.reward == table
    assert cert.laws == cycle_laws(cert.clock_bound//3)
    expected = portfolio()
    expected.append(("PREVIOUS_SURE_OWNER_THIRDS", (
        RationalLaw(1, (Q(1),), Q(0)),
        *(RationalLaw(1, (Q(1, 3),), Q(2, 3)) for _ in range(3)),
    )))
    records = read_json(MANIFEST)["profiles"]
    assert len(records) == len(expected) == 142
    for record, (name, laws) in zip(records, expected):
        assert record["name"] == name
        assert record["laws"] == [law.to_json() for law in laws]
        assert qjson(terminal_semantics(table, laws)[3]) == record["exploitability"]
    report = read_json(REPORT)
    old_minimum = min(Q(record["exploitability"]) for record in records)
    radius = Q(report["radius"])
    stationary_floor = Q(1, 600)
    assert radius > 0
    assert cert.exploitability+2*radius < OUTER_ERROR
    assert OUTER_ERROR < min(old_minimum-2*radius, stationary_floor-2*radius)
    assert Q(report["old_portfolio_minimum"]) == old_minimum
    assert Q(report["new_profile_exploitability"]) == cert.exploitability
    assert Q(report["old_portfolio_lower_on_box"]) == old_minimum-2*radius
    assert Q(report["new_profile_upper_on_box"]) == cert.exploitability+2*radius
    assert Q(report["stationary_lower_on_box"]) == stationary_floor-2*radius
    phase_check(table)
    print("Verified exact table, all142 old profiles, and new full-cap certificate")


if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in {"run", "verify"}:
        raise SystemExit("Usage: MULTIDATE_PORTFOLIO_TEST.py run|verify")
    {"run": run, "verify": verify}[sys.argv[1]]()
