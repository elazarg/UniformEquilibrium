"""Check witness 3 on the two ordered halves of the four-owner simplex."""
from itertools import permutations

from RANK_FOUR_RECIPROCAL_CORE import PLAYERS, check_cell


# Each hexadecimal digit is one training date's nonempty owner mask.
SCHEDULES = (
    "1248112124244888",
    "12c12121c2cc",
    "14a14141a4aa",
    "21c21212c1cc",
    "429424249299",
    "2841282482148411",
    "4128414214821288",
    "4182414814281822",
    "4fffb",
    "4812448481811222",
    "4821482418248121",
    "8128412814284124",
    "8142814281428142",
    "8218421824184214",
)
SELECTORS = (0, 1, 2, 2, 1, 1, 3, 3, 3, 4, 3, 5, 6, 7, 8, 8, 9, 10, 11, 12, 13, 11, 11, 11)


def main():
    donors = ((3,), (3,), (1,), (1, 2))
    totals = {0: [0, 0, 0], 2: [0, 0, 0]}
    orders = tuple(permutations(PLAYERS))
    assert len(orders) == len(SELECTORS)
    for order, selector in zip(orders, SELECTORS):
        axis = 2 if min(order.index(0), order.index(3)) < order.index(2) else 0
        donor, = donors[axis]
        perm = (axis, *(i for i in PLAYERS if i not in (axis, donor)), donor)
        vertices = tuple(tuple(int(i in order[:k]) for i in perm) for k in range(1, 5))
        schedule = tuple(tuple(perm.index(i) for i in PLAYERS if int(mask, 16) & (1 << i))
                         for mask in SCHEDULES[selector])
        faces = tuple((u, perm.index(p), perm.index(n)) for u, i in enumerate(perm)
                      for p in donors[i] for n in PLAYERS if n != i and n not in donors[i])
        words, gains = check_cell(schedule, vertices, faces)
        for i, number in enumerate((1, words, gains)):
            totals[axis][i] += number
    print("axis, tetrahedra, weighted words, exact gains", totals)


if __name__ == "__main__":
    main()
