"""Independent exact small-law tests of the adaptive-face obstruction.

Run: python experiments/CODEX_NOETHER_SUPPORT__CHECK_ADAPTIVE_FACE_OBSTRUCTION.py
No files are written. Complete response menus retain the after-support date.
Finite enumerations are evidence only, not the unrestricted-clock proof.
"""

from fractions import Fraction
from itertools import product


def reward(coalition):
    if not coalition:
        return (0, 0, 0, 0)
    return (
        1 if 0 in coalition else 2 * int(2 in coalition),
        (2 * int(0 in coalition) - 1) * int(1 in coalition),
        (2 * int(1 in coalition) - 1) * int(2 in coalition),
        int(3 in coalition),
    )


def payoff(clocks):
    finite = [t for t in clocks if t is not None]
    if not finite:
        return (0, 0, 0, 0)
    first = min(finite)
    return reward({i for i, time in enumerate(clocks) if time == first})


def audit_engine(denominator):
    times = (0, 1, None)
    responses = (0, 1, 2, None)
    cache = {}

    def pure_values(i, opponents):
        key = (i, opponents)
        if key not in cache:
            others = [j for j in range(4) if j != i]
            values = []
            for response in responses:
                value = 0
                for choices in product(range(3), repeat=3):
                    clocks = [None] * 4
                    clocks[i] = response
                    weight = 1
                    for j, law, choice in zip(others, opponents, choices):
                        clocks[j] = times[choice]
                        weight *= law[choice]
                    value += weight * payoff(clocks)[i]
                values.append(value)
            cache[key] = tuple(values)
        return cache[key]

    def profile_debts(profile):
        debts = []
        for i in range(4):
            values = pure_values(i, profile[:i] + profile[i + 1 :])
            prescribed = sum(profile[i][k] * values[j] for k, j in enumerate((0, 1, 3)))
            debts.append(denominator * max(values) - prescribed)
        return debts

    never = (0, 0, denominator)

    def all_errors(profile):
        parent = max(profile_debts(profile))
        children = []
        for omitted in range(4):
            quiet = profile[:omitted] + (never,) + profile[omitted + 1 :]
            debts = profile_debts(quiet)
            children.append(max(debts[:omitted] + debts[omitted + 1 :]))
        return parent, children

    return all_errors


def half_grid():
    denominator = 2
    laws = [(a, b, denominator - a - b) for a in range(3) for b in range(3 - a)]
    errors = audit_engine(denominator)
    minima = [None] * 4
    count = 0
    for profile in product(laws, repeat=4):
        parent, children = errors(profile)
        for omitted, child in enumerate(children):
            joint = parent + child
            assert joint > 0
            minima[omitted] = joint if minima[omitted] is None else min(minima[omitted], joint)
        count += 1
    print("half-grid profiles:", count, "minimum parent+child errors:", [Fraction(x, 16) for x in minima])


def hidden_tail_family():
    denominator = 8
    errors = audit_engine(denominator)
    minima = [None] * 4
    count = 0
    for tails in product(range(5), repeat=3):
        profile = tuple((4, tail, 4 - tail) for tail in tails) + ((8, 0, 0),)
        parent, children = errors(profile)
        assert parent == 0
        for omitted, child in enumerate(children):
            minima[omitted] = child if minima[omitted] is None else min(minima[omitted], child)
        count += 1
    print("exact parent hidden-tail profiles:", count, "minimum child errors:", [Fraction(x, 8**4) for x in minima])
    assert minima[:3] == [8**4 // 2] * 3
    assert Fraction(minima[3], 8**4) >= Fraction(1, 8)


def next_date_identity():
    count = 0
    for t1, t2 in product((0, 1, 2, None), repeat=2):
        q1, q2 = int(t1 == 0), int(t2 == 0)
        before = payoff((0, t1, t2, None))[0]
        after = payoff((1, t1, t2, None))[0]
        assert before == 1
        assert after == 2 * q2 + (1 - q1) * (1 - q2)
        count += 1
    print("hidden-tail next-date identities:", count, "PASS")


if __name__ == "__main__":
    next_date_identity()
    half_grid()
    hidden_tail_family()
