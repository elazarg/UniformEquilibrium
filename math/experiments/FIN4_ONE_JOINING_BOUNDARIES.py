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


EXCEPTIONS = {
    1: {'--+--+++--0+', '--+--+++--+0', '--+-+0++---+', '--+-+0++-+-+'},
    2: {'--+-+0++-0-+', '--+-+0++-+-0'},
    3: set(),
}


def main():
    strict = {canonical(matrix(w)) for w in WITNESSES}
    signs = {1: '+', -1: '-', 0: '0'}
    for ties, representatives in boundary_faces(strict):
        if ties == 0:
            continue
        exceptions = {''.join(signs[v] for v in face) for face in representatives
                      if not has_common_rival(matrix(face))}
        assert exceptions == EXCEPTIONS[ties]
        print(f'{ties} ties: common-rival support test {len(representatives)-len(exceptions)}'
              f'/{len(representatives)}, exceptional forms {len(exceptions)}')


if __name__ == '__main__':
    main()
