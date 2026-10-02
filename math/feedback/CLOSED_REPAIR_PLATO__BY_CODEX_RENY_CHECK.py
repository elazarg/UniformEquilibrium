"""Independent exact finite-event checks for CLOSED_REPAIR_PLATO.md.

This is a rational-arithmetic verifier of the displayed coefficients, not a
substitute for the five-event reduction for arbitrary stopping laws.
"""

from fractions import Fraction as F
from itertools import product


R = {
    0: (0, 0, 0, 0),
    1: (1, 3, 3, 1),
    2: (-4, 0, -2, -1),
    4: (2, 2, 0, -3),
    8: (3, -2, -2, 0),
    3: (1, 0, -2, -3),
    5: (0, -1, 3, 0),
    9: (1, 2, 3, -2),
    6: (-1, -1, 1, 1),
    10: (4, -4, -4, 4),
    12: (-4, 4, 1, 1),
    7: (-3, 2, 2, 4),
    11: (4, -2, -3, -2),
    13: (-2, 0, -3, 2),
    14: (0, -4, -2, 2),
    15: (-2, 17, -9, -6),
}
NEVER = None
HALF = {0: F(1, 2), NEVER: F(1, 2)}
PIVOT = {0: F(1, 2), 2: F(1, 4), NEVER: F(1, 4)}
G = {2: F(1)}
EVENTS = {"x": 0, "n": NEVER, "a": 3, "b": 2, "c": 1}
Z = F(3, 32)


def payoff(profile):
    ans = [F(0)] * 4
    for atoms in product(*(list(law.items()) for law in profile)):
        dates = [item[0] for item in atoms]
        weight = F(1)
        for _, mass in atoms:
            weight *= mass
        finite = [date for date in dates if date is not NEVER]
        if not finite:
            continue
        first = min(finite)
        mask = sum(1 << i for i, date in enumerate(dates) if date == first)
        for i in range(4):
            ans[i] += weight * R[mask][i]
    return ans


def replace(profile, player, law):
    result = list(profile)
    result[player] = law
    return result


def pure_gain(profile, player, date):
    return payoff(replace(profile, player, {date: F(1)}))[player] - payoff(profile)[player]


def cap(profile, player):
    # Every integer gap and one date past all finite atoms are represented.
    last = max([0] + [t for law in profile for t in law if t is not NEVER])
    return max(payoff(replace(profile, player, {t: F(1)}))[player]
               for t in tuple(range(last + 2)) + (NEVER,))


def vector(profile):
    u = payoff(profile)
    b = [cap(profile, i) for i in range(4)]
    return u, b, [b[i] - u[i] for i in range(4)]


def display(name, values):
    print(name, tuple(str(v) for v in values))


source = [HALF] * 4
u, b, d = vector(source)
assert u == [F(0), F(1), F(-7, 8), F(-1, 8)]
assert d == [F(1, 8), F(0), F(0), F(0)]
for i in range(4):
    assert pure_gain(source, i, 0) == pure_gain(source, i, NEVER) == 0
display("source U", u)
display("source B", b)
display("source d", d)

family = [PIVOT, HALF, HALF, HALF]
u, b, d = vector(family)
assert u == [F(1, 32), F(35, 32), F(-25, 32), F(-3, 32)]
assert b == [F(1, 8), F(19, 16), F(-11, 16), F(-1, 16)]
assert d == [Z, Z, Z, F(1, 32)]
display("family U", u)
display("family B", b)
display("family d", d)

for event, date in (("u", 0), ("lambda", 2), ("nu", NEVER)):
    profile = replace(source, 0, {date: F(1)})
    d0 = cap(profile, 0) - payoff(profile)[0]
    n1 = pure_gain(profile, 1, NEVER)
    n2 = pure_gain(profile, 2, NEVER)
    assert F(3, 4)*d0 + F(2, 21)*n1 + F(13, 84)*n2 == Z
    display("pivot coefficient " + event, [d0, n1, n2])

rows = {}
for j in (1, 2, 3):
    rows[j] = {}
    for event, date in EVENTS.items():
        profile = replace(family, j, {date: F(1)})
        u = payoff(profile)
        dj = cap(profile, j) - u[j]
        h = payoff(replace(profile, 0, G))[0] - u[0]
        late = pure_gain(profile, 0, 4)
        n1 = pure_gain(profile, 1, NEVER)
        n2 = pure_gain(profile, 2, NEVER)
        rows[j][event] = (dj, h, late, n1, n2)
        display(f"mover {j} event {event} [D,H,L,N1,N2]", rows[j][event])
        if j == 1:
            certificate = F(29, 38)*dj + F(51, 380)*h + F(9, 380)*late + F(3, 38)*n2
            assert certificate == Z + (F(9, 76) if event == "b" else 0)
            assert dj == F(3, 16)*(event in ("x", "b", "c"))
            assert h-late == F(5, 4)*(event in ("a", "b"))
        elif j == 2:
            certificate = F(91, 106)*dj + F(3, 53)*late + F(9, 106)*n1
            assert certificate == Z + (F(15, 848) if event == "a" else F(9, 53) if event == "c" else 0)
        else:
            certificate = F(7, 10)*late + F(11, 40)*n1 + F(1, 40)*n2
            assert certificate == Z + (F(29, 160) if event == "a" else F(21, 128) if event == "b" else 0)

# Equality-case restrictions, checked as coefficient identities.
def field(j, event, index):
    return rows[j][event][index]

assert [field(2, e, 0) for e in ("x", "n", "b")] == [F(3, 16), F(0), F(0)]
assert (field(2, "x", 2)+field(2, "n", 2))/2 == Z
assert field(2, "b", 2)-field(2, "n", 2) == F(3, 16)

# For player 3, eliminating n=1-x-c gives exactly the two stated equations.
late0 = field(3, "n", 2)
latex = field(3, "x", 2)-late0
latec = field(3, "c", 2)-late0
ratio = latex / 5
assert latec == 3*ratio and Z-late0 == F(5, 2)*ratio
n10 = field(3, "n", 3)
n1x = field(3, "x", 3)-n10
n1c = field(3, "c", 3)-n10
ratio = n1x / 15
assert n1c == 7*ratio and Z-n10 == F(15, 2)*ratio

# Independent mixed-law tests of the five-event reduction, including gaps
# and tail dates beyond the original single-atom representatives.
tests = [
    ({1: F(2, 5), 3: F(3, 5)},
     {0: F(1, 7), 2: F(2, 7), 3: F(1, 7), 7: F(2, 7), NEVER: F(1, 7)}),
    ({2: F(1, 3), 5: F(1, 3), 9: F(1, 3)},
     {0: F(1, 5), 1: F(1, 5), 5: F(1, 5), 12: F(1, 5), NEVER: F(1, 5)}),
]
for g, mu in tests:
    weights = {event: F(0) for event in EVENTS}
    for s, gs in g.items():
        for t, mt in mu.items():
            event = "x" if t == 0 else "n" if t is NEVER else "a" if s < t else "b" if s == t else "c"
            weights[event] += gs*mt
    assert sum(weights.values()) == 1
    pivot = {0: F(1, 2), NEVER: F(1, 4)}
    pivot.update({s: gs/4 for s, gs in g.items()})
    for j in (1, 2, 3):
        profile = replace([pivot, HALF, HALF, HALF], j, mu)
        u = payoff(profile)
        actual = (
            cap(profile, j)-u[j],
            payoff(replace(profile, 0, g))[0]-u[0],
            pure_gain(profile, 0, 20),
            pure_gain(profile, 1, NEVER),
            pure_gain(profile, 2, NEVER),
        )
        predicted = tuple(sum(weights[e]*rows[j][e][k] for e in EVENTS) for k in range(5))
        assert actual == predicted

equilibrium = [{0: F(1)}, {NEVER: F(1)}, {NEVER: F(1)}, {NEVER: F(1)}]
assert vector(equilibrium) == ([F(1), F(3), F(3), F(1)], [F(1), F(3), F(3), F(1)], [F(0)]*4)
print("All asserted exact rational identities passed.")
