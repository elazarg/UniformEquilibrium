"""Bounded same-table Nash--Bellman discovery; no root-count certification.

Reads the owned literal-table experiment, writes nothing. All root faces are
permitted. Numerical support enumeration is evidence, not an exhaustive
algebraic classification. Every accepted candidate is checked against all
eight literal Quit/Continue comparisons. Never is handled only by an actual
tail or a separately proved deleted-clock bound, never by this finite game.
"""

import importlib.util
import itertools
from pathlib import Path

import numpy as np


LOCATION = Path(__file__).with_name(
    'CODEX_NOETHER_SUPPORT__UNRESTRICTED_FOUR_PHASE_DISCOVERY.py')
SPEC = importlib.util.spec_from_file_location('literal_table', LOCATION)
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
TABLE = BASE.TABLE
BITS = BASE.BITS
SEED_PROFILE = np.array([
    [283943, 275040, 293677, 266055],
    [288138, 279248, 298184, 270014],
    [297843, 289542, 308761, 279333], [0, 0, 0, 0]], dtype=float)/10**6


def endpoints(q, v):
    delta = np.zeros(4); Q = np.zeros(4); H = np.zeros(4)
    D = np.zeros(4); J = np.zeros((4, 4)); JQ = J.copy()
    for i in range(4):
        masks = np.flatnonzero(~BITS[:, i])
        factors = np.where(BITS[masks], q, 1-q)
        factors[:, i] = 1
        prob = np.prod(factors, axis=1)
        reward_q = TABLE[masks | (1 << i), i]
        reward_c = TABLE[masks, i].copy(); reward_c[0] = v[i]
        diff = reward_q-reward_c
        delta[i] = prob @ diff
        Q[i] = prob @ reward_q
        H[i] = prob @ TABLE[masks, i]
        D[i] = prob[0]
        for j in range(4):
            if i == j:
                continue
            dp = np.prod(np.delete(factors, j, axis=1), axis=1)
            dp *= np.where(BITS[masks, j], 1., -1.)
            J[i, j] = dp @ diff
            JQ[i, j] = dp @ reward_q
    return delta, Q, H, D, J, JQ


def face_root(v, status, initial):
    active = np.flatnonzero(np.array(status) == 2)
    q = np.minimum(status, 1).astype(float)
    q[active] = np.asarray(initial)
    for _ in range(60):
        f, Q, H, D, J, JQ = endpoints(q, v)
        err = np.max(np.abs(f[active]), initial=0.)
        if err < 2e-12:
            if np.max((1-q)*f) > 1e-9 or np.min(q*f) < -1e-9:
                return None
            if len(active) and (np.min(q[active]) <= 1e-8 or np.max(q[active]) >= 1-1e-8):
                return None
            w = q*Q+(1-q)*(H+D*v)
            return q, w, f
        try:
            step = np.linalg.solve(J[np.ix_(active, active)], -f[active])
        except np.linalg.LinAlgError:
            return None
        scale = 1.
        for _line in range(30):
            y = q.copy(); y[active] += scale*step
            if np.all(y[active] > 0) and np.all(y[active] < 1):
                if np.max(np.abs(endpoints(y, v)[0][active])) < err:
                    break
            scale *= .5
        else:
            return None
        q = y
    return None


def candidate_roots(v, rich=False):
    found = []
    rng = np.random.default_rng(20260910)
    for status in itertools.product(range(3), repeat=4):
        n = status.count(2)
        seeds = [np.full(n, x) for x in (.08, .25, .5, .8)]
        if rich:
            seeds += [rng.uniform(.01, .99, n) for _ in range(12)]
        if n == 0:
            seeds = [[]]
        for seed in seeds:
            out = face_root(v, status, seed)
            if out is not None and not any(np.max(np.abs(out[0]-old[0])) < 1e-7 for old in found):
                found.append(out)
    return found


def main():
    v = BASE.full_rows(SEED_PROFILE.reshape(-1))[2]
    q = SEED_PROFILE[2]
    print('ACTUAL_INITIAL_VALUE', v)
    for k in range(5):
        found = candidate_roots(v, rich=True)
        print('VALUE', k, v, 'NUMERICAL_ROOT_COUNT', len(found))
        for x, w, delta in found:
            D = endpoints(x, v)[3]
            print('ROOT', x, 'PREDECESSOR', w, 'MAX_DELETED_SURVIVAL', max(D), 'DELTA', delta)
        out = face_root(v, (2, 2, 2, 2), q)
        if out is None:
            print('LOCAL_DENSE_CHART_STOPPED; no nonexistence inference')
            break
        q, v, _ = out


if __name__ == '__main__':
    main()
