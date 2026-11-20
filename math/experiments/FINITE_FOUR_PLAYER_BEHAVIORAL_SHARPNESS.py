"""Verify passive reward completions for all 116 literal singleton calibrations.

Every sign check uses integer Bernstein coefficients. Run without Python's -O.
"""
from itertools import combinations, product
from math import prod

from FIN4_SINGLETON_SIGN_CLASSES import EDGES, I, WITNESSES, boundary_faces, calibrate, canonical


# Positive box capacities in census order. Dashes use the passive rewards below.
BOXES = (
    "1111 3253 1111 1221 1111 1111 2121 1111 - - 1111 1111 1122 - 1111 1111 1111 1111 1111 - 1111",
    "1111 3242 1111 1231 1111 2121 1111 1221 1111 1111 2121 1111 1111 4753 1212 1111 1111 1111 1111 1111 1221 1111 - 2113 2137 1111 1111 - - 1111 1111 1112 - 1111 1111 1111 2212 1111 1111 1231 1111 1111 1111 1111 1111 1252",
    "1111 2121 1111 1231 1111 1111 1231 1111 1111 3542 1111 1111 1111 1231 1111 1111 1221 1111 1111 1111 1252 2125 - - 2113 - 3213 1111 1231 1111 1111 1111 1252 1111 1111 - 1111 1111 1252",
    "1111 1111 1252 1111 1111 1252 2113 - 1111 1252",
)

# In each row the three rival pairs are in lexicographic order, followed by the rival triple.
PASSIVE_REWARDS = {
    (0, 8): ((7, 13, -12, 1), (-2, -10, 16, 1), (14, 13, -2, 1), (-13, 8, 4, 1)),
    (0, 9): ((15, 12, 4, 1), (-6, -12, 2, -1), (10, 15, -3, 1), (-8, -1, 8, 1)),
    (0, 13): ((12, -3, -13, 3), (-6, 11, 4, 12), (9, 5, -2, -2), (-12, 1, -13, 3)),
    (0, 19): ((2, 1, -9, 1), (15, -1, 12, 1), (11, 11, 9, 1), (-7, 7, 8, 1)),
    (1, 22): ((13, 7, -1, 1), (-4, 13, 6, 1), (16, 13, -6, 1), (-10, 13, 10, 1)),
    (1, 27): ((3, -11, 15, 1), (10, 2, 11, 1), (-3, 1, 13, 1), (6, -5, 10, 1)),
    (1, 28): ((13, 7, 15, -6), (2, -8, -6, -2), (-15, 11, 3, 1), (2, -6, -9, -6)),
    (1, 32): ((3, 8, -2, 1), (13, 8, 7, 1), (-2, 16, -2, 1), (-15, 10, 10, -1)),
    (2, 22): ((7, -5, 3, 1), (14, 13, -1, 1), (-1, 10, 16, 1), (2, -6, 11, 1)),
    (2, 23): ((4, -7, 14, -6), (-1, 16, -10, 3), (-7, -14, 3, 12), (3, -6, 12, 12)),
    (2, 25): ((-3, 11, -8, 1), (-2, -2, 10, 1), (11, 11, -1, 1), (-15, 9, 16, 1)),
    (2, 35): ((15, 8, -2, 1), (-3, -7, 6, 1), (8, 5, 8, 1), (-11, 10, -8, 1)),
    (3, 7): ((2, 8, -1, 1), (-13, -6, 4, 1), (10, 7, -2, 1), (-1, 13, 2, 1)),
}


def bisect(coefficients, shape, axis):
    """Split one tensor-product Bernstein array; each child uses a common positive scale."""
    stride = prod(shape[axis + 1:])
    width = shape[axis]
    left = [0] * len(coefficients)
    right = left.copy()
    for block in range(0, len(coefficients), stride * width):
        for pos in range(block, block + stride):
            next_pos = pos + stride
            a, b = coefficients[pos], coefficients[next_pos]
            if width == 2:
                left[pos], left[next_pos] = 2*a, a+b
                right[pos], right[next_pos] = a+b, 2*b
            else:
                last = next_pos + stride
                c = coefficients[last]
                middle = a + 2*b + c
                left[pos], left[next_pos], left[last] = 4*a, 2*(a+b), middle
                right[pos], right[next_pos], right[last] = middle, 2*(b+c), 4*c
    return left, right


def exclude(fields, shape, sure, quiet):
    pending = [(fields, 0)]
    checked = 0
    while pending:
        rows, depth = pending.pop()
        checked += 1
        if any((i not in quiet and min(row) > 0) or (i not in sure and max(row) < 0)
               for i, row in enumerate(rows)):
            continue
        assert shape and depth < 140, "Uncertified cell"
        axis = depth % len(shape)
        left, right = zip(*(bisect(row, shape, axis) for row in rows))
        pending.extend(((left, depth + 1), (right, depth + 1)))
    return checked


def count_cells(g, higher):
    rewards = {}
    for i in I:
        opponents = tuple(j for j in I if j != i)
        rewards[i, ()] = 0
        for j in opponents:
            rewards[i, (j,)] = g[i][j]
        for team, value in zip((*combinations(opponents, 2), opponents), higher[i]):
            rewards[i, team] = value

    checked = 0
    for mode in product(range(3), repeat=4):
        quiet = {i for i in I if mode[i] == 0}
        free = [i for i in I if mode[i] == 1]
        sure = {i for i in I if mode[i] == 2}
        if sure:
            fields = [[] for i in I]
            for bits in product((0, 1), repeat=len(free)):
                quitters = sure | {j for j, bit in zip(free, bits) if bit}
                for i in I:
                    fields[i].append(rewards[i, tuple(sorted(quitters - {i}))])
            checked += exclude(fields, (2,) * len(free), sure, quiet)
            continue

        # With no sure owner, divide the field by its largest hazard r.
        for pivot in free:
            fields = [[] for i in I]
            remaining = [j for j in free if j != pivot]
            for degree in range(3):
                for bits in product((0, 1), repeat=len(remaining)):
                    quitters = {pivot} | {j for j, bit in zip(remaining, bits) if bit}
                    for i in I:
                        rivals = tuple(sorted(quitters - {i}))
                        linear = sum(g[i][j] for j in rivals)
                        quadratic = sum(rewards[i, (j, k)] - g[i][j] - g[i][k]
                                        for j, k in combinations(rivals, 2))
                        endpoints = (2*linear, 2*linear + quadratic, 2*rewards[i, rivals])
                        fields[i].append(endpoints[degree])
            checked += exclude(fields, (3,) + (2,) * len(remaining), sure, quiet)
    return checked


def calibrations():
    strict = []
    for entries in WITNESSES:
        g = [[0] * 4 for i in I]
        for (i, j), value in zip(EDGES, entries):
            g[i][j] = value
        strict.append(g)
    yield strict
    for ties, faces in boundary_faces({canonical(g) for g in strict}):
        if ties:
            yield [calibrate(face)[2] for face in faces]


def main():
    counts = []
    used = set()
    for ties, matrices in enumerate(calibrations()):
        codes = BOXES[ties].split()
        assert len(codes) == len(matrices)
        cells = 0
        for index, (g, code) in enumerate(zip(matrices, codes)):
            if code == '-':
                key = (ties, index)
                used.add(key)
                higher = PASSIVE_REWARDS[key]
            else:
                b = tuple(map(int, code))
                assert len(b) == 4 and min(b) > 0
                g = [[value*b[j] for j, value in enumerate(row)] for row in g]
                higher = []
                for i in I:
                    rivals = tuple(j for j in I if j != i)
                    higher.append([sum(g[i][j] for j in team)
                                   for team in (*combinations(rivals, 2), rivals)])
            cells += count_cells(g, higher)
        counts.append((len(matrices), cells))
    assert used == set(PASSIVE_REWARDS)
    assert [n for n, _ in counts] == [21, 46, 39, 10]
    print("Calibrations and exact cells by number of singleton ties:", counts)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O to enable all certificate checks")
    main()
