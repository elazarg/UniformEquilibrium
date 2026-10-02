"""Independent exact audit of TARSKI's canonical child-extension inequality.

Run from math/: python experiments/CODEX_NOETHER_SUPPORT__CHECK_ALL_CHILD_EXTENSIONS.py
Uses integer arithmetic only; writes no files. The exhaustive small-menu test
is evidence, not a proof for unrestricted clocks. Pointwise checks also test
the hidden-clock event inequalities separately from any equilibrium filter.
"""

from itertools import product


def reward(coalition):
    if not coalition:
        return (0, 0, 0, 0)
    return (
        1 + int(2 in coalition) if 0 in coalition else 3 * int(2 in coalition),
        int(0 in coalition) if 1 in coalition else 3 * int(0 in coalition) - 1,
        int(1 in coalition) if 2 in coalition else 3 * int(1 in coalition) - 1,
        0 if 3 in coalition else 1,
    )


def payoff(clocks):
    finite = [t for t in clocks if t is not None]
    if not finite:
        return (0, 0, 0, 0)
    first = min(finite)
    return reward({i for i, t in enumerate(clocks) if t == first})


def replaced(clocks, i, time):
    return clocks[:i] + (time,) + clocks[i + 1 :]


def pointwise_check():
    count = 0
    for clocks in product((0, 1, 2, None), repeat=4):
        t0, t1, t2, t3 = clocks
        child = (None, t1, t2, t3)
        finite = [t for t in child if t is not None]
        coalition = {i for i, t in enumerate(child) if finite and t == min(finite)}
        a = bool(coalition and 1 not in coalition)
        b12 = 1 in coalition and 2 in coalition
        b13 = 1 in coalition and 3 in coalition
        h = any(t is not None and (t1 is None or t <= t1) for t in (t2, t3))
        uc = payoff(child)
        assert uc[1] == -int(a)
        assert payoff(replaced(child, 2, None))[2] - uc[2] >= int(b12) - int(a)
        assert payoff(replaced(child, 3, None))[3] - uc[3] >= int(b13)
        assert int(h) <= int(a) + int(b12) + int(b13)

        x = not h and t0 is not None and (t1 is None or t0 < t1)
        y = not h and t0 is not None and t0 == t1
        z = not h and t1 is not None and (t0 is None or t1 < t0)
        w = not h and t0 is None and t1 is None
        assert sum(map(int, (x, y, z, w, h))) == 1
        u = payoff(clocks)
        assert u[0] <= int(x) + int(y) + 3 * int(h)
        assert payoff(replaced(clocks, 1, None))[1] - u[1] >= int(y) - int(z) - 3 * int(h)
        assert u[2] <= -int(x) + 2 * int(y) + 2 * int(z) + 2 * int(h)
        assert payoff(replaced(clocks, 0, 0))[0] >= 1
        assert payoff(replaced(clocks, 2, 0))[2] >= 0
        count += 1
    return count


def compositions(total):
    return [(a, b, total - a - b) for a in range(total + 1) for b in range(total - a + 1)]


def exact_menu_check(denominator):
    times = (0, 1, None)
    responses = (0, 1, 2, None)
    laws = compositions(denominator)
    response_cache = {}

    def pure_values(i, opponents):
        key = (i, opponents)
        if key not in response_cache:
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
                    value += weight * payoff(tuple(clocks))[i]
                values.append(value)
            response_cache[key] = tuple(values)
        return response_cache[key]

    def profile_values(profile):
        prescribed, debts = [], []
        for i in range(4):
            opponents = profile[:i] + profile[i + 1 :]
            f = pure_values(i, opponents)
            u = sum(profile[i][k] * f[j] for k, j in enumerate((0, 1, 3)))
            prescribed.append(u)
            debts.append(denominator * max(f) - u)
        return prescribed, debts

    never = (0, 0, denominator)
    total = exact_children = 0
    scale = denominator**4
    for child in product(laws, repeat=3):
        _, child_debts = profile_values((never,) + child)
        epsilon = max(child_debts[1:])
        for outsider in laws:
            u, d = profile_values((outsider,) + child)
            eta = max(0, scale - u[0])
            assert 3 * d[1] + d[2] + 6 * eta + 96 * epsilon >= scale
            assert 10 * max(d) + 96 * epsilon >= scale
            exact_children += int(epsilon == 0)
            total += 1
    return total, exact_children


def periodic_check():
    values = ((1, 1, 0, 1), (1, 0, 1, 1), (2, 0, 0, 1))
    for owner in range(3):
        current, following = values[owner], values[(owner + 1) % 3]
        singleton = reward({owner})
        assert tuple(singleton[i] + following[i] for i in range(4)) == tuple(2 * v for v in current)
        for i in range(4):
            if i == owner:
                assert singleton[i] == following[i]
            else:
                twice_quit = reward({owner, i})[i] + reward({i})[i]
                expected_twice_gain = -2 if i == 3 else (-1 if i == (owner + 1) % 3 else 0)
                assert twice_quit - 2 * current[i] == expected_twice_gain


if __name__ == "__main__":
    print("pointwise clock outcomes:", pointwise_check())
    periodic_check()
    print("periodic Bellman identities and all four root comparisons: PASS")
    for denominator in (2, 3):
        total, exact_children = exact_menu_check(denominator)
        print(f"denominator={denominator}: {total} parent profiles, {exact_children} exact-child extensions, PASS")
