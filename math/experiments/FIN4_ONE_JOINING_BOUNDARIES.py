"""Exact support checks for choosing one joining reward at tied singleton comparisons.

Run with python math/experiments/FIN4_ONE_JOINING_BOUNDARIES.py. The input
is the canonical census checked by FIN4_SINGLETON_SIGN_CLASSES.py.
"""
from itertools import combinations, permutations

from FIN4_SINGLETON_SIGN_CLASSES import EDGES, I, WITNESSES, boundary_faces, canonical


def matrix(entries):
    rows = [[0] * 4 for _ in I]
    for (i, j), value in zip(EDGES, entries):
        rows[i][j] = value
    return rows


def possible_support(rows, omitted, support):
    for i in I:
        if i == omitted:
            continue
        signs = [rows[i][j] for j in support if j != i]
        low, high = min(signs, default=0), max(signs, default=0)
        if i in support and not (low < 0 < high or low == high == 0):
            return False
        if i not in support and high <= 0 and low < 0:
            return False
    return True


def has_common_rival(rows):
    for omitted in I:
        rivals = set(I) - {omitted}
        if not any(rows[i][j] < 0 and rows[j][i] < 0 and min(rows[i][k], rows[j][k]) < 0
                   for i, j, k in permutations(rivals)):
            continue
        common = set(rivals)
        for size in range(4):
            for active in combinations(rivals, size):
                if possible_support(rows, omitted, (*active, omitted)):
                    common.intersection_update(active)
        if common:
            return True
    return False


def has_negative_joining_exterior(rows):
    """Try a reciprocal core or the three-row conditions with the fourth row free."""
    for i, c, d, k in permutations(I):
        if all(rows[i][c] * rows[i][j] < 0 and rows[c][i] * rows[c][j] < 0
               for j in (d, k)):
            return True
        if not (rows[c][i] > 0 and rows[i][k] > 0
                and rows[c][d] < 0 and rows[d][c] < 0
                and min(rows[c][k], rows[d][k]) < 0):
            continue
        if rows[i][d] > 0:
            return True
        if rows[d][i] <= 0:
            continue
        if rows[i][d] == 0 or rows[d][k] >= 0:
            return True
        if rows[i][c] <= 0 and rows[k][d] > 0 > rows[k][i] and rows[k][c] <= 0:
            return True
    return False


EXCEPTIONS = {
    1: {'--+--+++--0+', '--+--+++--+0', '--+-+0++---+', '--+-+0++-+-+'},
    2: {'--+-+0++-0-+', '--+-+0++-+-0'},
    3: set(),
}


def main():
    strict = {canonical(matrix(w)) for w in WITNESSES}
    signs = {1: '+', -1: '-', 0: '0'}
    for ties, representatives in boundary_faces(strict):
        negative_count = sum(has_negative_joining_exterior(matrix(face))
                             for face in representatives)
        assert negative_count == (21, 34, 21, 4)[ties]
        print(f'{ties} ties: negative joining exterior with a free row '
              f'{negative_count}/{len(representatives)}')
        if ties == 0:
            continue
        exceptions = {''.join(signs[v] for v in face) for face in representatives
                      if not has_common_rival(matrix(face))}
        assert exceptions == EXCEPTIONS[ties]
        print(f'{ties} ties: common-rival support test {len(representatives)-len(exceptions)}'
              f'/{len(representatives)}, exceptional forms {len(exceptions)}')


if __name__ == '__main__':
    main()
