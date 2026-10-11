"""Exact rational checks of two ten-edge cubic obstructions.

Run: python math/notes/CODEX_EMMY_BOX__CUBIC_FORWARD_MOMENT_CHECK.py
Requires SymPy. Uses no floating-point decisions or external solver.
"""

from itertools import product
import sympy as sp

R = sp.Rational
ROOTS = [
    (0, R(7, 10), R(9, 10), 0),
    (R(7, 10), R(7, 10), 0, 0),
    (0, 0, 0, R(1, 40)),
    (R(1, 2), R(1, 10), 0, R(7, 10)),
    (0, R(1, 2), 0, R(7, 10)),
    (R(7, 10), R(7, 10), 0, 0),
    (R(1, 1000), 0, 0, 0),
    (R(1, 10), 0, 0, 0),
    (0, 0, R(7, 20), 0),
    (R(9, 10), 0, 0, R(7, 10)),
]
VALUES = [
    (12, -8, R(17, 3), -12),
    (-R(4, 3), R(17, 3), 12, -R(48, 5)),
    (R(41, 39), R(261, 130), R(38, 39), 1),
    (R(136, 27), -11, 12, -R(2, 3)),
    (6, -R(25, 3), R(52, 5), -3),
    (-R(4, 3), R(17, 3), 0, 0),
    (1, 12, 12, 12),
    (1, R(11, 9), R(17, 10), R(8, 9)),
    (R(21, 130), R(6, 13), 1, R(399, 130)),
    (R(17, 3), 12, -12, -8),
]


def reward(mask):
    coalition = {i for i in range(4) if mask >> i & 1}
    if len(coalition) == 1:
        owner = next(iter(coalition))
        result = [0] * 4
        result[owner], result[(owner + 2) % 4] = 1, 4
        return result
    if len(coalition) == 2:
        donor = [i for i in coalition if (i + 1) % 4 in coalition]
        if donor:
            result = [1] * 4
            result[donor[0]], result[(donor[0] + 1) % 4] = -1, 2
            return result
        return [0 if i in coalition else 1 for i in range(4)]
    if len(coalition) == 3:
        return [-1 if i in coalition else 10 for i in range(4)]
    return [9] * 4


ORBITS = []
for degree in range(1, 4):
    for exponents in product(range(degree + 1), repeat=4):
        rotations = [exponents[j:] + exponents[:j] for j in range(4)]
        if sum(exponents) == degree and exponents == min(rotations):
            ORBITS.append(exponents)
assert len(ORBITS) == 9


def features(value):
    return sp.Matrix([
        sum(sp.prod(value[i] ** exponents[(i + j) % 4] for i in range(4))
            for j in range(4))
        for exponents in ORBITS
    ])


def edge(root, value):
    root, value = list(map(R, root)), list(map(R, value))
    quit_values, continue_values = [], []
    for i in range(4):
        alpha = sp.prod(1 - root[j] for j in range(4) if j != i)
        quit_value = continue_reward = R(0)
        for mask in range(16):
            if mask >> i & 1:
                continue
            mass = sp.prod(root[j] if mask >> j & 1 else 1 - root[j]
                           for j in range(4) if j != i)
            quit_value += mass * reward(mask | 1 << i)[i]
            if mask:
                continue_reward += mass * reward(mask)[i]
        continue_value = continue_reward + alpha * value[i]
        assert (quit_value == continue_value if root[i] > 0
                else quit_value <= continue_value)
        quit_values.append(quit_value)
        continue_values.append(continue_value)
    target = [root[i] * quit_values[i] + (1 - root[i]) * continue_values[i]
              for i in range(4)]
    assert all(-12 <= x <= 12 for x in value + target)
    charge = 1 - sp.prod(1 - q for q in root)
    assert charge > 0
    return target, features(value) - features(target), charge


columns, charges = [], []
for number, (root, value) in enumerate(zip(ROOTS, VALUES), 1):
    target, column, charge = edge(root, value)
    columns.append(column)
    charges.append(charge)
    print(f"edge {number}: target={target}, charge={charge}")

matrix = sp.Matrix.hstack(*columns)
assert matrix.rank() == 9
kernel = matrix.nullspace()
assert len(kernel) == 1
weights = kernel[0] / kernel[0][-1]
assert all(weight > 0 for weight in weights)
assert matrix * weights == sp.zeros(9, 1)
total_charge = sum(a * w for a, w in zip(charges, weights))
assert total_charge > 0
print("all ten exact weights strictly positive; moment defect exactly zero")
print("weights with last weight 1:")
for weight in weights:
    print(weight)
print("positive total weighted charge:", total_charge)


# A separate certificate entirely in the nonnegative reward-hull simplex.
# Roots have denominator1000; fractions specify quiet-source interpolation.
SECOND_ROOT_NUMERATORS = [
    (0, 0, 16, 10), (0, 0, 156, 87), (0, 100, 218, 0),
    (0, 0, 293, 85), (436, 0, 0, 516), (0, 426, 442, 0),
    (0, 52, 188, 18), (169, 0, 175, 0), (273, 0, 0, 146),
    (175, 136, 157, 133),
]
SECOND_QUIET_FRACTIONS = [
    (1, 0, 0, 8), (2, 0, 8, 5), (1, 10, 4, 1),
    (2, 0, 8, 3), (10, 1, 0, 6), (1, 3, 4, 1),
    (2, 6, 3, 3), (3, 3, 2, 2), (0, 1, 1, 4),
    (10, 8, 9, 9),
]


def nonnegative_source(root, fractions):
    value = []
    for i in range(4):
        x, y, w = root[(i - 1) % 4], root[(i + 2) % 4], root[(i + 1) % 4]
        alpha = (1 - x) * (1 - y) * (1 - w)
        quit = 12*w*x*y - w*x + w*y - 2*w - 2*x*y + x - y + 1
        stop = 4*y - 3*x*y - 3*y*w + x*w + 11*x*y*w
        threshold = (quit - stop) / alpha
        lower = max(R(0), threshold)
        value.append(threshold if root[i] else
                     lower + (10 - lower) * R(fractions[i], 10))
    return value


second_columns, second_charges = [], []
for number, (numerators, fractions) in enumerate(
        zip(SECOND_ROOT_NUMERATORS, SECOND_QUIET_FRACTIONS), 1):
    root = [R(x, 1000) for x in numerators]
    value = nonnegative_source(root, fractions)
    target, column, charge = edge(root, value)
    # edge() independently enumerates the literal raw rewards and ALL agents.
    assert all(0 <= x <= 10 for x in value + target)
    assert sum(value) <= R(99, 10) and sum(target) <= R(99, 10)
    second_columns.append(column)
    second_charges.append(charge)
    print(f"nonnegative edge {number}: source={value}, target={target}, charge={charge}")

second_matrix = sp.Matrix.hstack(*second_columns)
assert second_matrix.rank() == 9
second_kernel = second_matrix.nullspace()
assert len(second_kernel) == 1
second_weights = second_kernel[0] / second_kernel[0][-1]
assert all(weight > 0 for weight in second_weights)
assert second_matrix * second_weights == sp.zeros(9, 1)
assert sum(a * w for a, w in zip(second_charges, second_weights)) > 0
print("nonnegative reward-hull certificate: all ten weights strictly positive;")
print("exactly zero cubic moment defect and strictly positive total charge")
