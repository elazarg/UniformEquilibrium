"""Exact finite-clock regressions; no completeness or all-table claim."""

from fractions import Fraction as Q
import gzip
from itertools import product
import json
from pathlib import Path
import sys


def outcome(draw):
    dates = [date for date in draw if date is not None]
    if not dates:
        return None
    first = min(dates)
    return sum(1 << i for i, date in enumerate(draw) if date == first)


def coalition_law(laws):
    result = {mask: Q(0) for mask in range(1, 16)}
    for atoms in product(*(list(law.items()) for law in laws)):
        mass = Q(1)
        for _, probability in atoms:
            mass *= probability
        mask = outcome(tuple(date for date, _ in atoms))
        if mask is not None:
            result[mask] += mass
    return result


def regret_rows(laws, clock_bound):
    base = coalition_law(laws)
    rows = []
    for i in range(4):
        for date in [*range(clock_bound + 1), None]:
            changed = list(laws)
            changed[i] = {date: Q(1)}
            deviated = coalition_law(changed)
            rows.append(tuple(
                deviated[mask] - base[mask] if player == i else Q(0)
                for mask in range(1, 16) for player in range(4)
            ))
    return rows


def evaluate(row, reward):
    return sum((a * b for a, b in zip(row, reward)), Q(0))


def positive_solo_reward():
    return tuple(
        Q(3 if not mask & (1 << i) else 1 if mask == 1 << i else 2)
        for mask in range(1, 16) for i in range(4)
    )


def exact_exploitability(laws, clock_bound, reward):
    return max(Q(0), *(evaluate(row, reward)
                      for row in regret_rows(laws, clock_bound)))


def box_row_max(row, lower, upper):
    return sum((a * (hi if a >= 0 else lo)
                for a, lo, hi in zip(row, lower, upper)), Q(0))


def uncovered_reward():
    return tuple(
        Q((0 if mask & 3 == 0 else -1 if mask & 3 == 3 else 1)
          * (1 if i == 0 else -1)) if i < 2
        else Q(-1 if mask & (1 << i) else 0)
        for mask in range(1, 16) for i in range(4)
    )


def check_uncovered_seeds():
    reward = uncovered_reward()
    table_path = Path(__file__).with_name("CODEX_SKEPTIC__UNCOVERED_PURE_SEEDS.json")
    table = json.loads(table_path.read_text())
    assert tuple(Q(table["rewards"][str(mask)][i])
                 for mask in range(1, 16) for i in range(4)) == reward
    debts = []
    for mask in range(16):
        laws = [{0 if mask & (1 << i) else None: Q(1)} for i in range(4)]
        debts.append(exact_exploitability(laws, 1, reward))
    assert min(debts) == 1
    assert all(debt > Q(7, 8) for debt in debts)
    print("Uncovered seed regrets by masks 0..15:", ", ".join(map(str, debts)))


def check_emitted_certificate(path):
    with gzip.open(path, "rt") as stream:
        certificate = json.load(stream)
    reward = tuple(Q(certificate["reward"]["rewards"][str(mask)][i])
                   for mask in range(1, 16) for i in range(4))
    assert reward == uncovered_reward()
    clock_bound = certificate["clock_bound"]
    laws = [{**{date: Q(mass) for date, mass in enumerate(law["finite"])},
             None: Q(law["never"])} for law in certificate["laws"]]
    assert all(sum(law.values()) == 1 for law in laws)
    rows = regret_rows(laws, clock_bound)
    exact_regret = max(Q(0), *(evaluate(row, reward) for row in rows))
    assert exact_regret == Q(certificate["exploitability"]) == Q(1, 2)
    assert exact_regret < Q(certificate["epsilon"]) == Q(3, 4)
    epsilon, radius = Q(7, 8), Q(1, 32)
    lower = tuple(max(Q(-1), value - radius) for value in reward)
    upper = tuple(min(Q(1), value + radius) for value in reward)
    mixed_upper = max(Q(0), *(box_row_max(row, lower, upper) for row in rows))
    seed_lowers = []
    for mask in range(16):
        seed = [{0 if mask & (1 << i) else None: Q(1)} for i in range(4)]
        witness = max(regret_rows(seed, 1), key=lambda row: evaluate(row, reward))
        seed_lowers.append(-box_row_max(tuple(-a for a in witness), lower, upper))
    assert mixed_upper < epsilon < min(seed_lowers)
    print(f"Independent emitted-profile regret: {exact_regret}")
    print(f"Reward box radius {radius}: mixed <= {mixed_upper}; "
          f"all seeds >= {min(seed_lowers)}; target {epsilon}")


def main():
    reward = positive_solo_reward()
    never = [{None: Q(1)} for _ in range(4)]
    singleton = [{0: Q(1)}, *never[1:]]
    reset = [
        {0: Q(1, 4), 4: Q(3, 4)},
        {1: Q(1, 3), 4: Q(2, 3)},
        {2: Q(1, 2), None: Q(1, 2)},
        {3: Q(1)},
    ]
    assert exact_exploitability(never, 0, reward) == 1
    assert exact_exploitability(singleton, 1, reward) == 0
    assert exact_exploitability(reset, 5, reward) == Q(1, 2)
    assert {mask: mass for mask, mass in coalition_law(reset).items()
            if mass} == {1 << i: Q(1, 4) for i in range(4)}
    normalized = tuple(value / 3 for value in reward)
    epsilon = Q(1, 16)
    radius = epsilon / 4
    lower = tuple(max(Q(-1), value - radius) for value in normalized)
    upper = tuple(min(Q(1), value + radius) for value in normalized)
    leaf_max = max(Q(0), *(box_row_max(row, lower, upper)
                           for row in regret_rows(singleton, 1)))
    assert leaf_max < epsilon
    print("Positive-solo Never / singleton / reset regrets: 1, 0, 1/2")
    print("Reset singleton coalition masses: 1/4 each")
    print(f"60-dimensional rational box leaf: regret <= {leaf_max} < {epsilon}")
    check_uncovered_seeds()


if __name__ == "__main__":
    main()
    if len(sys.argv) > 1:
        check_emitted_certificate(sys.argv[1])
