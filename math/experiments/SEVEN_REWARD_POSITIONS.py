"""Count supports passing the pure-coalition, positive-participation and two-sure tests."""
from dataclasses import dataclass
from itertools import combinations, permutations

from FIN4_ONE_JOINING_BOUNDARIES import matrix
from FIN4_SINGLETON_SIGN_CLASSES import WITNESSES, boundary_faces, canonical

PLAYERS = range(4)
COALITIONS = tuple(s for s in range(16) if s.bit_count() >= 2)
POSITIONS = tuple((i, s) for i in PLAYERS for s in COALITIONS)
PAIR = 3  # first count with players 0 and 1 as the mutually negative pair


@dataclass(frozen=True)
class Edit:
    position: int
    edge: int
    spoiled: int
    positive_owners: int
    adverse: bool


def make_edit(index, i, s, sign):
    owner = 1 << i
    full = s | owner
    # Four 16-bit blocks record the coalitions where each owner's quit offer
    # has a strictly positive participating term somewhere on that support.
    eligible = 0
    if sign > 0 and s & owner:
        eligible = sum(1 << (16 * i + a) for a in COALITIONS if a & s == s)
    return Edit(1 << index, 1 << (16 * i + (s & ~owner)),
                s if sign < 0 else s ^ owner, eligible,
                bool(PAIR & owner and full & PAIR == PAIR
                     and (sign < 0) == bool(s & owner)))


def fixed_pair_supports(k):
    edits = [make_edit(index, i, s, sign)
             for index, (i, s) in enumerate(POSITIONS) for sign in (-1, 1)]
    required = [PAIR, *(15 ^ (1 << i) for i in PLAYERS), 15]
    choices = [[e for e in edits if e.spoiled == s] for s in required]
    # An owner outside a support supplies no restriction there.
    initial = sum(1 << (16 * i + a)
                  for i in PLAYERS for a in COALITIONS if not a & (1 << i))
    survivors = set()

    def trap(mask):
        return bool(mask & (mask >> 16) & (mask >> 32) & (mask >> 48))

    def assign(depth, positions, edges, positive, adverse):
        if depth < len(required):
            for e in choices[depth]:
                if not (edges & e.edge or positions & e.position):
                    assign(depth + 1, positions | e.position, edges | e.edge,
                           positive | e.positive_owners, adverse or e.adverse)
        elif k == 6:
            if adverse and trap(positive):
                survivors.add(positions)
        else:
            for e in edits:
                if not positions & e.position and (adverse or e.adverse):
                    if trap(positive | e.positive_owners):
                        survivors.add(positions | e.position)

    assign(0, 0, 0, initial, False)
    return survivors


def all_pair_count(k):
    fixed = fixed_pair_supports(k)
    union = set()
    for i, j in combinations(PLAYERS, 2):
        labels = [i, j, *(x for x in PLAYERS if x not in (i, j))]
        translation = []
        for owner, s in POSITIONS:
            mapped = sum(1 << labels[r] for r in PLAYERS if s & (1 << r))
            translation.append(1 << POSITIONS.index((labels[owner], mapped)))
        for support in fixed:
            mapped = 0
            while support:
                low = support & -support
                mapped |= translation[low.bit_length() - 1]
                support ^= low
            union.add(mapped)
    return len(fixed), len(union)


def check_outsider_roles():
    strict = {canonical(matrix(witness)) for witness in WITNESSES}
    counts = []
    for _, representatives in boundary_faces(strict):
        count = 0
        for signs in representatives:
            g = matrix(signs)
            pairs = [(u, v) for u, v in combinations(PLAYERS, 2)
                     if max(g[u][v], g[v][u]) <= 0]
            if len(pairs) != 1:
                continue
            u, v = pairs[0]
            if max(g[u][v], g[v][u]) == 0:
                continue
            outsiders = [i for i in PLAYERS if i not in (u, v)]
            assert any(g[u][b] > 0 and g[v][b] > 0 and g[b][a] > 0
                       and g[a][b] < 0 and min(g[u][a], g[v][a]) < 0
                       for a, b in permutations(outsiders))
            count += 1
        counts.append(count)
    assert counts == [8, 11, 4, 0]
    return counts


if __name__ == '__main__':
    print("Outsider role counts by number of ties:", check_outsider_roles(), flush=True)
    for k in (6, 7):
        print(k, all_pair_count(k), flush=True)
