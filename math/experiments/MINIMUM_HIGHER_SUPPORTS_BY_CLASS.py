"""Count supports passing the necessary first-edit tests in each singleton orbit."""
from collections import defaultdict
from itertools import combinations, product

from FIN4_ONE_JOINING_BOUNDARIES import matrix
from FIN4_SINGLETON_SIGN_CLASSES import WITNESSES, boundary_faces, canonical

PLAYERS = range(4)
HIGHER = tuple(s for s in range(1, 16) if s.bit_count() >= 2)
PAIRS = {(1 << i) | (1 << j): (i, j) for i, j in combinations(PLAYERS, 2)}
POSITIONS = {(i, s): 1 << n for n, (i, s) in enumerate(product(PLAYERS, HIGHER))}
FACES = [(sure.bit_count(), sure | quiet,
          tuple(s for s in range(1, 16) if (s & sure) == sure and not (s & quiet)))
         for sure in range(1, 16) for quiet in range(16) if not (sure & quiet)]


def largest_closed_sure_set(g, arrows):
    outgoing = {s: 1 << i for s, i in arrows.items()}
    for s, (i, j) in PAIRS.items():
        if s not in arrows:
            outgoing[s] = sum(1 << owner for owner, rival in ((i, j), (j, i))
                              if g[owner][rival] > 0)
    for i in PLAYERS:
        singleton = 1 << i
        outgoing[singleton] = sum(1 << j for j in PLAYERS
                                  if g[j][i] < 0 and arrows.get(singleton | (1 << j)) != j)
    return max((n for n, fixed, face in FACES
                if all(not (outgoing[s] & fixed) for s in face)), default=0)


def support_masks(arrows):
    choices = [(0, 0)]
    for s, i in arrows.items():
        # Lower the origin or raise the destination. Only the latter can
        # create a positive participating reward, and only when i joins.
        t = s ^ (1 << i)
        edits = [(POSITIONS[i, s], 0)]
        if t in HIGHER:
            edits.append((POSITIONS[i, t], t & (1 << i)))
        choices = [(mask | bit, covered | owner) for mask, covered in choices
                   for bit, owner in edits]
    return (mask for mask, covered in choices if covered == 15)


def matched_cycle_type(arrows, mask):
    premiums = {}
    for s, i in arrows.items():
        t = s ^ (1 << i)
        if s.bit_count() == 2:
            if s & (1 << i) or not (mask & POSITIONS[i, t]):
                return None
            premiums[t] = i
        if t == 15 and mask & POSITIONS[i, t]:
            return None
    losses = {owner: arrows[t] for t, owner in premiums.items()
              if t & (1 << arrows[t]) and mask & POSITIONS[arrows[t], t]}
    cycles = set()
    for owner in PLAYERS:
        path = []
        while owner in losses and owner not in path:
            path.append(owner)
            owner = losses[owner]
        if owner in path:
            cycles.add(frozenset(path[path.index(owner):]))
    return tuple(sorted(map(len, cycles)))


def count(g, cycle_counts=None):
    pairs = tuple(s for s, (i, j) in PAIRS.items() if max(g[i][j], g[j][i]) <= 0)
    protected = (*pairs, *(s for s in HIGHER if s.bit_count() >= 3))
    assert all(min(row) < 0 < max(row) for row in g)
    assert all(sum((pair & triple) == pair for pair in pairs) <= 2
               for triple in HIGHER if triple.bit_count() == 3)
    # Count before closed faces, after faces with >=2 sure, after all faces.
    signed = [0, 0, 0]
    unsigned = [set(), set(), set()]
    for owners in product(PLAYERS, repeat=len(protected)):
        arrows = dict(zip(protected, owners))
        if any(arrows.get(s ^ (1 << i)) == i for s, i in arrows.items()):
            continue
        if len({i for s, i in arrows.items() if not (s & (1 << i))}) < 4:
            continue
        sure = largest_closed_sure_set(g, arrows)
        for mask in support_masks(arrows):
            if cycle_counts is not None and sure == 0:
                signature = matched_cycle_type(arrows, mask)
                if signature is not None:
                    cycle_counts[signature].append(mask)
            for level, survives in enumerate((True, sure < 2, sure == 0)):
                if survives:
                    signed[level] += 1
                    unsigned[level].add(mask)
    return len(protected), signed, [len(group) for group in unsigned]


if __name__ == '__main__':
    for label, entries in enumerate(WITNESSES, 1):
        cycles = defaultdict(list) if label == 9 else None
        print(label, *count(matrix(entries), cycles))
        if cycles is not None:
            for signature, masks in sorted(cycles.items()):
                print('cycle lengths, signed, unsigned', signature, len(masks), len(set(masks)))
            print('distinct no-positive-grand supports',
                  len({mask for masks in cycles.values() for mask in masks}))
    strict = {canonical(matrix(entries)) for entries in WITNESSES}
    for ties, representatives in boundary_faces(strict):
        if ties:
            by_size = defaultdict(list)
            for entries in representatives:
                size, _, totals = count(matrix(entries))
                by_size[size].append(totals[-1])
            for size, counts in sorted(by_size.items()):
                print('ties, size, orbits, min, max', ties, size, len(counts),
                      min(counts), max(counts))
