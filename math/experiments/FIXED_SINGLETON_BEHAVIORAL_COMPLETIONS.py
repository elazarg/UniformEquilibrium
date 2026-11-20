"""Certify passive reward sign choices at every magnitude on 113 singleton strata."""
from itertools import combinations, permutations, product

from SIGN_SELECTED_AXES import I, WITNESSES, boundary_faces, canonical, matrix, negative_axes, refined_sets


TEAMS = [tuple(i for i in I if i != o) for o in I]


def determinant_terms(g, rows, cols):
    """Signs of the nonzero determinant monomials, or {0} when none occur."""
    terms = set()
    for p in permutations(range(len(cols))):
        term = (-1)**sum(a > b for a, b in combinations(p, 2))
        for i, j in zip(rows, p):
            term *= g[i][cols[j]]
        if term:
            terms.add(term)
    return terms or {0}


def adjugate(g, team):
    return [[{(-1)**(a+b)*s for s in determinant_terms(g, [k for k in team if k != i],
                                                         [k for k in team if k != j])}
             for a, i in enumerate(team)] for b, j in enumerate(team)]


def easy_triples(g, team):
    choices = []
    for signs in product((-1, 1), repeat=3):
        local = dict(zip(team, signs))
        if any(local[i] > 0 and all(g[i][j] >= 0 for j in team) for i in team):
            choices.append(local)  # This owner's active waiting numerator is strictly positive.
            continue
        for order in permutations(team):
            lead = [next((local[i]*g[i][j] for i in order if g[i][j]), 0) for j in team]
            if min(lead) >= 0:
                choices.append(local)  # Signed row weights in descending powers M²,M,1.
                break
    return choices


def pair_ok(g, pair, w, local):
    i, j = pair
    a, b = sorted(set(I)-set(pair))
    s = {a: local[b][a], b: local[a][b]}
    if min(s.values()) > 0 or max(w[h]*s[h] for h in s) < 0:
        return False
    for owner, rival in ((i,j), (j,i)):
        if g[owner][rival] == 0 and not any(s[h] < 0 and g[h][rival] <= 0 for h in s):
            return False
    if g[i][j] == g[j][i] == 0:
        return max(s.values()) < 0 or any(s[h] < 0 and max(g[h][i], g[h][j]) <= 0 for h in s)
    return True


def certificate(pattern):
    g = matrix(pattern)
    positive, _ = refined_sets(pattern)
    negative, weak = negative_axes(g, positive)
    adverse = [p for p in combinations(I, 2) if max(g[p[0]][p[1]], g[p[1]][p[0]]) <= 0]
    base = [easy_triples(g, team) for team in TEAMS]
    mixed = [o for o in I if not base[o]]
    axis = {}
    determinants = []
    for o in mixed:
        team = TEAMS[o]
        adj = adjugate(g, team)
        columns = [set.union(*(row[j] for row in adj))-{0} for j in range(3)]
        if not all(len(col) == 1 for col in columns):
            return False
        axis[o] = [next(iter(col)) for col in columns]
        signs = determinant_terms(g, team, team)
        determinants.append({1} if o in positive else {-1} if o in negative else signs)

    full_adj = adjugate(g, I)
    for ds in product(*determinants):
        choices = base.copy()
        for o, d in zip(mixed, ds):
            choices[o] = [dict(zip(TEAMS[o], [v if d > 0 else -v for v in axis[o]]))]
        need_neg = {o for o in mixed if max(choices[o][0].values()) < 0}
        if any(min(axis[o]) < 0 for o in need_neg):
            return False
        concentrate = [o for o, d in zip(mixed, ds) if o in need_neg - negative - weak and d < 0]
        if len(concentrate) > 1:
            if len(concentrate) != 2:
                return False
            a, b = set(I)-set(concentrate)
            if g[a][b]*g[b][a] >= 0:
                return False
        if len(concentrate) == 1:
            targets = concentrate
        elif concentrate:
            targets = [None]
        else:
            targets = list(I)
        for p in targets:
            for w in product((-1, 1), repeat=4):
                if any(w[i] < 0 for i in positive) or any(w[i] > 0 for i in need_neg|negative|weak):
                    continue
                if p is not None and any(full_adj[p][j] in ({1}, {-1}) and w[j] not in full_adj[p][j] for j in I):
                    continue
                if any(max(w[i]*g[i][j] for i in I) <= 0 for j in I):
                    continue
                if not any(all(max(local[o].values()) > 0 or w[o] < 0 for o in I) and
                           all(pair_ok(g, pair, w, local) for pair in adverse) for local in product(*choices)):
                    break
            else:
                break  # This target works for every remaining sign of w.
        else:
            return False
    return True


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError("Run without -O to enable the certificate checks")
    strict = [tuple((v > 0)-(v < 0) for v in row) for row in WITNESSES]
    missed = []
    for ties, faces in boundary_faces({canonical(matrix(g)) for g in strict}):
        patterns = strict if ties == 0 else faces
        missing = [i for i, p in enumerate(patterns) if not certificate(p)]
        print(f'{ties} ties: {len(patterns)-len(missing)}/{len(patterns)} covered by the sign test.')
        missed.append(missing)
    assert missed == [[13], [28], [23], []]  # The separate four-row construction treats these faces.
