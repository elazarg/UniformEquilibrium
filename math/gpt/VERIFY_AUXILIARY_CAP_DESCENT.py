#!/usr/bin/env python3
"""Verify a three-date Fin4 full-response certificate using exact arithmetic.

Run:
    python VERIFY_AUXILIARY_CAP_DESCENT.py

Only Python's standard library is required. The root candidates were found
numerically; this checker neither trusts nor reruns that search. It verifies
all finite claims with Fraction arithmetic, including a separate enumeration
of every relevant pure response (three early dates, one late date, and Never).
It is not a proof of the general existence theorems in the accompanying note.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

N = 4
M, KAPPA = F(17, 4), F(3, 8)
R = {
    1: (1, -2, F(-15, 4), 0),
    2: (F(-5, 2), 0, 1, -3),
    4: (F(-7, 4), F(-5, 4), 0, F(-5, 2)),
    8: (-2, F(-3, 4), -4, 0),
    3: (2, 1, F(-3, 4), F(-3, 4)),
    5: (-3, F(1, 2), F(1, 2), F(-13, 4)),
    # The sole change to the uploaded fixture is the last entry here.
    9: (F(-7, 4), F(1, 2), F(-9, 4), F(-1, 4)),
    6: (F(-3, 2), F(-3, 2), -2, F(-3, 2)),
    10: (F(1, 2), -2, F(1, 2), F(-15, 4)),
    12: (F(1, 4), F(-3, 4), 1, 1),
    7: (0, -3, F(7, 4), F(-17, 4)),
    11: (F(5, 4), F(-9, 4), 0, -4),
    13: (F(-1, 2), F(-5, 2), F(3, 2), F(-15, 4)),
    14: (F(-3, 4), F(-1, 4), F(-1, 2), F(-9, 4)),
    15: (-1, F(-7, 4), F(-7, 2), F(3, 2)),
}
R = {coalition: tuple(map(F, row)) for coalition, row in R.items()}
SINGLETONS = tuple(R[1 << i][i] for i in range(N))
CONSTRUCTION_ROOTS = tuple(tuple(map(F, row)) for row in (
    ('2386017/76096933', '80356906/99365033',
     '70243795/97732973', '47300903/49023997'),
    ('1301064/76252885', '80642351/99011632',
     '64515646/90051035', '76346577/78824219'),
    ('1200151/75057758', '4958849/6085172',
     '59882048/83601291', '74463212/76862663'),
))


def endpoints(q: tuple[F, ...], v: list[F]) -> tuple[list[F], list[F], list[F]]:
    quit_values, continue_values, deleted_survival = [], [], []
    for i in range(N):
        qi = ci = beta = F(0)
        for coalition in range(1 << N):
            if coalition & (1 << i):
                continue
            mass = F(1)
            for j in range(N):
                if j != i:
                    mass *= q[j] if coalition & (1 << j) else 1 - q[j]
            qi += mass * R[coalition | (1 << i)][i]
            ci += mass * (R[coalition][i] if coalition else v[i])
            if coalition == 0:
                beta = mass
        quit_values.append(qi)
        continue_values.append(ci)
        deleted_survival.append(beta)
    return quit_values, continue_values, deleted_survival


def root_regrets(q: tuple[F, ...], v: list[F]) -> list[F]:
    quit_values, continue_values, _ = endpoints(q, v)
    return [max(quit_values[i], continue_values[i])
            - q[i] * quit_values[i] - (1 - q[i]) * continue_values[i]
            for i in range(N)]


def prefix(q: tuple[F, ...], u: list[F], b: list[F]) -> tuple[list[F], list[F]]:
    quit_values, continue_values, beta = endpoints(q, u)
    new_u = [q[i] * quit_values[i] + (1 - q[i]) * continue_values[i]
             for i in range(N)]
    new_b = [max(quit_values[i], continue_values[i] + beta[i] * (b[i] - u[i]))
             for i in range(N)]
    return new_u, new_b


def stopping_laws(rows: tuple[tuple[F, ...], ...]) -> list[list[F]]:
    laws = []
    for i in range(N):
        survival, masses = F(1), []
        for row in rows:
            masses.append(survival * row[i])
            survival *= 1 - row[i]
        masses.append(survival)  # final index denotes Never
        assert sum(masses) == 1 and min(masses) >= 0
        laws.append(masses)
    return laws


def direct_payoff(laws: list[list[F]]) -> list[F]:
    never = len(laws[0]) - 1
    result = [F(0)] * N
    for times in product(range(never + 1), repeat=N):
        mass = F(1)
        for i, time in enumerate(times):
            mass *= laws[i][time]
        first = min(times)
        if first == never:
            continue
        coalition = sum(1 << i for i, time in enumerate(times) if time == first)
        for i in range(N):
            result[i] += mass * R[coalition][i]
    return result


def direct_pure_reply_values(laws: list[list[F]], player: int) -> list[F]:
    # Insert an unused finite date immediately before Never. All subsequent
    # finite dates have the same payoff, since every opponent is then Never.
    expanded = [law[:-1] + [F(0), law[-1]] for law in laws]
    never = len(expanded[0]) - 1
    opponents = [j for j in range(N) if j != player]
    values = []
    for response in range(never + 1):
        value = F(0)
        for opponent_times in product(range(never + 1), repeat=N - 1):
            times, mass = [response] * N, F(1)
            for j, time in zip(opponents, opponent_times):
                times[j] = time
                mass *= expanded[j][time]
            first = min(times)
            if first == never:
                continue
            coalition = sum(1 << j for j in range(N) if times[j] == first)
            value += mass * R[coalition][player]
        values.append(value)
    return values


def verify() -> dict:
    assert SINGLETONS == (1, 0, 0, 0)
    assert max(abs(x) for row in R.values() for x in row) == M
    for coalition, row in R.items():
        ga = (row[0] - 1 + row[1]) / 2
        gb = (row[2] + row[3]) / 2
        upper = ((F(1), F(-3, 4)) if coalition == 3 else
                 ((F(-3, 4), F(1)) if coalition == 12 else (F(-1), F(-1))))
        assert ga <= upper[0] and gb <= upper[1]
    joining = [R[1 | (1 << j)][j] - R[1][j] for j in (1, 2, 3)]
    assert joining == [3, F(17, 4), F(-1, 4)]
    assert R[3][0] > SINGLETONS[0] and R[3][1] > SINGLETONS[1]
    assert all((R[3][i] + R[12][i]) / 2 == SINGLETONS[i] + F(1, 8)
               for i in range(N))
    zero = tuple(F(0) for _ in range(N))
    for coalition in range(1, 1 << N):
        assert any(R.get(coalition ^ (1 << i), zero)[i] > R[coalition][i]
                   for i in range(N))

    u, b = [F(0)] * N, [max(F(0), si) for si in SINGLETONS]
    A = KAPPA / (4 * M + KAPPA)
    assert A == F(3, 139)
    trace = []
    for index, q in enumerate(CONSTRUCTION_ROOTS, start=1):
        assert all(0 <= qi <= 1 for qi in q)
        debt = [b[i] - u[i] for i in range(N)]
        total = sum(debt)
        t = min(total, KAPPA / 2)
        h = total - t
        auxiliary = [bi - h for bi in b]
        tolerance = A * t / (4 * N)
        errors = root_regrets(q, auxiliary)
        assert max(errors) <= tolerance
        assert min(auxiliary[i] - SINGLETONS[i] for i in range(N)) <= -KAPPA / 2
        survival = F(1)
        for qi in q:
            survival *= 1 - qi
        absorption = 1 - survival
        assert absorption >= A / 2
        new_u, new_b = prefix(q, u, b)
        new_debt = [new_b[i] - new_u[i] for i in range(N)]
        new_total = sum(new_debt)
        assert min(new_debt) >= 0
        assert new_total <= total - absorption * t + sum(errors)
        assert new_total <= total - A * t / 4
        trace.append({
            'prefix': index,
            'root': list(map(str, q)),
            'maximum_auxiliary_root_regret': str(max(errors)),
            'total_debt': str(new_total),
            'total_debt_decimal': float(new_total),
            'maximum_debt_decimal': float(max(new_debt)),
        })
        u, b = new_u, new_b

    chronological = tuple(reversed(CONSTRUCTION_ROOTS))
    laws = stopping_laws(chronological)
    assert direct_payoff(laws) == u
    replies = [direct_pure_reply_values(laws, i) for i in range(N)]
    assert [max(values) for values in replies] == b
    debt = [b[i] - u[i] for i in range(N)]
    assert sum(debt) < F(14, 10**8)   # 1.4e-7
    assert max(debt) < F(11, 10**8)   # 1.1e-7
    return {
        'reward_table_bitmasks': {str(S): list(map(str, row)) for S, row in R.items()},
        'construction_roots': [list(map(str, q)) for q in CONSTRUCTION_ROOTS],
        'chronological_roots': [list(map(str, q)) for q in chronological],
        'stopping_laws_dates_0_1_2_Never': [list(map(str, law)) for law in laws],
        'U': list(map(str, u)), 'B': list(map(str, b)),
        'pure_reply_values_dates_0_1_2_late_Never': [list(map(str, x)) for x in replies],
        'debts': list(map(str, debt)),
        'debt_sum': str(sum(debt)), 'exploitability': str(max(debt)),
        'trace': trace,
    }


if __name__ == '__main__':
    record = verify()
    destination = Path(__file__).with_name('AUXILIARY_CAP_DESCENT_CERTIFICATE.json')
    destination.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print('PASS: all 15 two-pair table inequalities; negative joining gain; product-low failure.')
    print('PASS: positive correlated surplus; all 15 immediate-coalition toggle exclusions.')
    print('PASS: all three rational auxiliary-root and complete-debt descent certificates.')
    print('PASS: independently enumerated payoffs and all 20 pure-response values.')
    print('Full exploitability:', float(F(record['exploitability'])))
    print('Total complete debt:', float(F(record['debt_sum'])))
    print('Certificate written to:', destination)
