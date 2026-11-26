"""Certify the bounded matched-pair region with a high observer in each group."""
from fractions import Fraction as Q
from itertools import product
from multiprocessing import Pool

from SIX_DATE_MATCHED_BOX import FOUR, ROTATED_FOUR, SIX, canonical, split, verify

# At the lower end of the high-observer interval, a second six-date roster is needed.
TWO_SOLOS_FOUR_JOINT = (
    ((2,), (3,), (0,2), (1,3), (0,2), (1,3)),
    (.918, .434, .287, .054, .170, .579, .414, .678, .734, .700),
)
GROUPS = ((0,2),(1,3))


def accepted(cell):
    if min(lo for lo,_ in cell)>=-Q(1,2):
        return True  # Previously certified middle cube.
    if any(all(-Q(1,2)<=cell[i][0] and cell[i][1]<=Q(1,3) for i in group)
           for group in GROUPS):
        return True  # Analytic paired-observer interval.
    rotations = [cell[k:]+cell[:k] for k in range(4)]
    for rotated in rotations:
        if (max(hi for _,hi in rotated[:2])<=-Q(3,4)
                and min(lo for lo,_ in rotated[2:])>=Q(1,2)):
            return True  # Previously certified low/high rectangle.
    for calendar in [FOUR, ROTATED_FOUR, SIX, TWO_SOLOS_FOUR_JOINT]:
        for rotated in rotations:
            if verify(calendar, rotated, Q(0)):
                return True
    return False


if __name__=='__main__':
    edges = (Q(-1),Q(-3,4),Q(-1,2),Q(0),Q(1,3),Q(1,2),Q(2,3))
    intervals = tuple(zip(edges,edges[1:]))
    cells = sorted({canonical(cell) for cell in product(intervals, repeat=4)
                    if all(any(cell[i][0]>=Q(1,3) for i in group) for group in GROUPS)})
    count = 0
    with Pool(4) as pool:
        for depth in range(28):
            results = pool.map(accepted,cells)
            remaining = [cell for cell, ok in zip(cells,results) if not ok]
            count += len(cells)-len(remaining)
            print(f'Depth {depth}: {len(cells)} cells, {len(remaining)} to split.',flush=True)
            if not remaining:
                print(f'High observer in each pair certified on {count} cyclic representatives.',flush=True)
                break
            cells = sorted({child for cell in remaining for child in split(cell)})
        else:
            raise ArithmeticError('Incomplete parameter cover')
