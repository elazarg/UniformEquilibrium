"""Exact interval certificates for the normalized regret bounds in the coverage map."""
from itertools import combinations, product

from FIN4_ONE_JOINING_BOUNDARIES import matrix
from FIN4_SINGLETON_SIGN_CLASSES import WITNESSES

PLAYERS = range(4)
UNIT = 1 << 17
# Class 9 also has the separate, analytical 1/16 crossed-pair certificate.
DENOMINATORS = (12, 12, 12, 12, 12, 10, 9, 9, 12, 12, 12, 13, 12, 12, 10, 9, 9, 8, 8, 8, 8)


def count_boxes(signs, receivers, denominator):
    positive = [[j for j in PLAYERS if signs[i][j] > 0] for i in PLAYERS]
    selected = [[j for j in PLAYERS if receivers[j] == i] for i in PLAYERS]

    def visit(lower, upper):
        total_lower, total_upper = sum(lower), sum(upper)
        if total_lower > UNIT or total_upper < UNIT:
            return 1
        # Each coordinate equals one minus the sum of the other three.
        lower, upper = (
            [max(lower[i], UNIT - total_upper + upper[i]) for i in PLAYERS],
            [min(upper[i], UNIT - total_lower + lower[i]) for i in PLAYERS],
        )
        for i in PLAYERS:
            factor = (UNIT + denominator * sum(upper[j] for j in positive[i])
                      - sum(lower[j] for j in selected[i]))
            if upper[i] * factor <= UNIT * UNIT:
                return 1
        axis = max(PLAYERS, key=lambda i: upper[i] - lower[i])
        middle = (upper[axis] + lower[axis]) // 2
        if middle <= lower[axis]:
            raise ArithmeticError("An unresolved box reached the integer grid scale")
        left_upper, right_lower = upper.copy(), lower.copy()
        left_upper[axis] = right_lower[axis] = middle
        return 1 + visit(lower, left_upper) + visit(right_lower, upper)

    return visit([0] * 4, [UNIT] * 4)


def certify(signs, denominator):
    choices = [[i for i in PLAYERS if signs[i][j] < 0] for j in PLAYERS]
    assert all(choices)
    return sum(count_boxes(signs, receivers, denominator) for receivers in product(*choices))


def certify_crossed_pairs():
    """Each of the four cells chooses one weak or one of two strong conflicts."""
    cells = tuple(product(range(2), repeat=2))
    for choices in product(("weak", "left", "right"), repeat=4):
        edges = []
        for (i, j), kind in zip(cells, choices):
            # The two endpoints are in distinct copies of the four cells.
            left = (1 - i, j) if kind == "left" else (i, j)
            right = (i, 1 - j) if kind == "right" else (i, j)
            edges.append((left, right, kind != "weak"))
        for size, strong_count in ((4, 0), (2, 2), (3, 1)):
            for subset in combinations(edges, size):
                left, right, strong = zip(*subset)
                if len(set(left)) == len(set(right)) == size and sum(strong) == strong_count:
                    break
            else:
                continue
            break
        else:
            raise ArithmeticError(f"No disjoint conflict certificate for {choices}")


if __name__ == "__main__":
    total = 0
    for label, (witness, denominator) in enumerate(zip(WITNESSES, DENOMINATORS, strict=True), 1):
        signs = matrix(witness)
        coarse = certify(signs, 8)
        stronger = coarse if denominator == 8 else certify(signs, denominator)
        total += coarse
        print(f"Class {label:2}: 1/{denominator} in {stronger} boxes")
    print(f"All 21 classes pass 1/8 in {total} boxes")
    certify_crossed_pairs()
    print("Class 9 passes the 81 disjoint-conflict checks for 1/16")
