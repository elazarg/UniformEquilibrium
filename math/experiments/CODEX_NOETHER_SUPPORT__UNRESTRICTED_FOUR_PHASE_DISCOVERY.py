"""Bounded numerical discovery on ONE original unequal-high quitting table.

All sixteen period-four Quit hazards are free in [0,1]. The minimized
objective is the COMPLETE terminal regret from phase zero, not one-stage
defect or an indifference residual. No numerical minimum is a lower bound.
The program prints results only and writes no data. Run with
PYTHONDONTWRITEBYTECODE=1 python experiments/<this filename>.
"""

import argparse
from fractions import Fraction
import importlib.util
from pathlib import Path
import sys
import time

import numpy as np


ROWS = {
    1: (1, 4, 0, 0), 2: (4, 1, 0, 0),
    4: (0, 0, 1, 4), 8: (0, 0, 4, 1),
    3: (2, 2, 1, 1), 5: (Fraction(8, 5), 1, 1, 0),
    9: (1, 0, 1, 2), 6: (0, 1, Fraction(8, 5), 1),
    10: (1, 2, 0, 1), 12: (1, 1, 2, 2),
    7: (1, 0, 0, 0), 11: (0, 1, 0, 0),
    13: (0, 0, 0, 1), 14: (0, 0, 1, 0),
    15: (-1, -1, -1, -1),
}
TABLE = np.array([(0, 0, 0, 0)] + [ROWS[k] for k in range(1, 16)], dtype=float)
BITS = ((np.arange(16)[:, None] >> np.arange(4)) & 1).astype(bool)
EYE = np.eye(16).reshape(4, 4, 16)


def stage(q, who=None):
    factors = np.where(BITS[None, :, :], q[:, None, :], 1-q[:, None, :])
    if who is not None:
        factors[:, :, who] = 1.
        masks = np.flatnonzero(~BITS[:, who])
    else:
        masks = np.arange(16)
    factors = factors[:, masks]
    probabilities = np.prod(factors, axis=2)
    jac = np.zeros((4, len(masks), 16))
    for j in range(4):
        if j == who:
            continue
        coeff = np.prod(np.delete(factors, j, axis=2), axis=2)
        coeff *= np.where(BITS[masks, j], 1., -1.)
        jac += coeff[:, :, None] * EYE[:, j, None, :]
    return masks, probabilities, jac


def affine_cycle(g, dg, c, dc):
    """Value from phase zero, with the actual zero-Never degenerate branch."""
    size = g.shape[1]
    numerator = np.zeros(size)
    dnum = np.zeros((size, 16))
    prefix = np.ones(size)
    dprefix = np.zeros((size, 16))
    for l in range(4):
        numerator += prefix*g[l]
        dnum += dprefix*g[l, :, None] + prefix[:, None]*dg[l]
        dprefix = dprefix*c[l, :, None] + prefix[:, None]*dc[l]
        prefix *= c[l]
    den = 1-prefix
    value = np.zeros(size)
    derivative = np.zeros((size, 16))
    positive = den > 0
    value[positive] = numerator[positive]/den[positive]
    derivative[positive] = (dnum[positive] + value[positive, None]*dprefix[positive])/den[positive, None]
    # At zero absorption the value above is literal, but the zero derivative
    # is only an optimizer convention: continuity/differentiability can fail.
    return value, derivative, prefix


def full_rows(x):
    q = np.asarray(x).reshape(4, 4)
    masks, p, dp = stage(q)
    reward = p @ TABLE
    dreward = np.einsum('lmv,mi->liv', dp, TABLE)
    c = np.repeat(p[:, :1], 4, axis=1)
    dc = np.repeat(dp[:, :1], 4, axis=1)
    payoff, dpayoff, joint = affine_cycle(reward, dreward, c, dc)
    Q = np.zeros((4, 4)); H = np.zeros((4, 4)); D = np.zeros((4, 4))
    dQ = np.zeros((4, 4, 16)); dH = dQ.copy(); dD = dQ.copy()
    for i in range(4):
        masks, p, dp = stage(q, i)
        Q[:, i] = p @ TABLE[masks | (1 << i), i]
        H[:, i] = p @ TABLE[masks, i]
        D[:, i] = p[:, 0]
        dQ[:, i] = np.einsum('lmv,m->lv', dp, TABLE[masks | (1 << i), i])
        dH[:, i] = np.einsum('lmv,m->lv', dp, TABLE[masks, i])
        dD[:, i] = dp[:, 0]
    never, dnever, deleted = affine_cycle(H, dH, D, dD)
    responses = []; gradients = []
    prefix = np.ones(4); dprefix = np.zeros((4, 16))
    ledger = np.zeros(4); dledger = np.zeros((4, 16))
    for l in range(4):
        responses.append(ledger + prefix*Q[l])
        gradients.append(dledger + dprefix*Q[l, :, None] + prefix[:, None]*dQ[l])
        ledger += prefix*H[l]
        dledger += dprefix*H[l, :, None] + prefix[:, None]*dH[l]
        dprefix = dprefix*D[l, :, None] + prefix[:, None]*dD[l]
        prefix *= D[l]
    responses.append(never); gradients.append(dnever)
    gains = np.asarray(responses)-payoff[None, :]
    jac = np.asarray(gradients)-dpayoff[None, :, :]
    return gains.reshape(-1), jac.reshape(-1, 16), payoff, deleted, joint[0]


def smooth(x, temperature):
    gains, jac, _, _, _ = full_rows(x)
    top = max(0., float(np.max(gains)))
    w = np.exp((gains-top)/temperature)
    zero_weight = np.exp(-top/temperature)
    den = np.sum(w)+zero_weight
    return top+temperature*np.log(den), w @ jac/den


def projected_bfgs(initial, temperature, steps):
    x = np.clip(np.array(initial, dtype=float), 0, 1)
    value, grad = smooth(x, temperature)
    inverse = np.eye(16)
    for _ in range(steps):
        pg = grad.copy()
        pg[(x == 0) & (grad > 0)] = 0
        pg[(x == 1) & (grad < 0)] = 0
        if np.max(np.abs(pg)) < 1e-9:
            break
        direction = -inverse @ pg
        direction[(x == 0) & (direction < 0)] = 0
        direction[(x == 1) & (direction > 0)] = 0
        if grad @ direction >= -1e-12*np.linalg.norm(pg)*np.linalg.norm(direction):
            direction = -pg
            inverse = np.eye(16)
        scale = 1.
        for _line in range(35):
            candidate = np.clip(x+scale*direction, 0, 1)
            displacement = candidate-x
            new_value, new_grad = smooth(candidate, temperature)
            if new_value <= value + 1e-4*(grad @ displacement):
                break
            scale *= .5
        else:
            break
        change = new_grad-grad
        curvature = change @ displacement
        if curvature > 1e-12*np.linalg.norm(change)*np.linalg.norm(displacement):
            rho = 1/curvature
            v = np.eye(16)-rho*np.outer(displacement, change)
            inverse = v @ inverse @ v.T + rho*np.outer(displacement, displacement)
        x, value, grad = candidate, new_value, new_grad
    return x


def exact_check(x):
    """Reuse the read-only repository Fraction checker on proper candidates."""
    location = Path(__file__).resolve().parents[2]/'Experiments/certsearch/block_pair'
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(location))
    spec = importlib.util.spec_from_file_location('periodic_probe_readonly', location/'block_pair_periodic_probe.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.TERMINAL = ROWS
    profile = tuple(tuple(Fraction(str(round(float(a), 12))) for a in row) for row in x.reshape(4, 4))
    assert all(0 <= a <= 1 for row in profile for a in row)
    module.assert_profile_payoff_equations(profile)
    values = module.profile_values(profile)
    gains = {key: value for key, value in module.full_stopping_gains(profile).items() if key[0] == 0}
    bound = max(Fraction(0), *gains.values())
    print('EXACT_RATIONAL_PROFILE', [[str(a) for a in row] for row in profile], flush=True)
    print('EXACT_INITIAL_REGRET', str(bound), float(bound), flush=True)
    print('EXACT_INITIAL_PAYOFF', [str(a) for a in values[0]], flush=True)
    print('EXACT_MAX_RESPONSE', max(gains, key=gains.get), flush=True)
    print('FLOAT_PHASE0_CROSSCHECK', float(np.max(full_rows(np.array(profile, dtype=float).reshape(-1))[0])), flush=True)
    return module, profile, bound


def literal_certificate():
    numerators = [[283943, 275040, 293677, 266055],
                  [288138, 279248, 298184, 270014],
                  [297843, 289542, 308761, 279333], [0, 0, 0, 0]]
    x = np.asarray(numerators, dtype=float).reshape(-1)/10**6
    module, profile, bound = exact_check(x)
    assert Fraction(1, 8000) < bound < Fraction(1, 7000)
    joint = Fraction(1)
    for row in profile:
        for q in row:
            joint *= 1-q
    assert 0 < joint < Fraction(1, 50)
    for i in range(4):
        deleted = Fraction(1)
        for row in profile:
            for j, q in enumerate(row):
                if j != i:
                    deleted *= 1-q
        assert 0 < deleted < Fraction(3, 50)
    values = module.profile_values(profile)
    assert all(1 < v < 2 for v in values[0])
    print('EXACT_CERTIFICATE_PASSED: 0 < E < 1/7000, C < 1/50, every deleted C < 3/50', flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--steps', type=int, default=180)
    parser.add_argument('--starts', type=int, default=6)
    parser.add_argument('--random-pass', action='store_true')
    parser.add_argument('--certificate-only', action='store_true')
    args = parser.parse_args()
    if args.certificate_only:
        literal_certificate()
        return
    rng = np.random.default_rng(20260908)
    test = rng.uniform(.05, .5, 16)
    g, J, _, _, _ = full_rows(test)
    for k in range(16):
        shifted = test.copy(); shifted[k] += 1e-6
        numerical = (full_rows(shifted)[0]-g)/1e-6
        assert np.max(np.abs(numerical-J[:, k])) < 2e-4
    assert max(full_rows(np.zeros(16))[0]) == 1
    sure = np.zeros(16); sure[0] = 1
    assert max(full_rows(sure)[0]) >= 1
    print('Derivative and boundary checks passed', flush=True)
    old = np.array([[.0984520158, 0, .2206967175, 0],
                    [0, .1820055015, .1882974049, 0],
                    [0, .2091849659, 0, .2319783206],
                    [.2645181956, 0, 0, .1169338769]]).reshape(-1)
    seeds = [old, np.full(16, .2), rng.uniform(0, .45, 16),
             rng.uniform(0, 1, 16), np.zeros(16), sure]
    temperatures = [.08, .025, .008, .0025, .0008, .00025, .00008, .000025, .000008]
    if args.random_pass:
        other_rng = np.random.default_rng(20260909)
        seeds = [other_rng.uniform(0, .4, 16) for _ in range(args.starts)]
        temperatures = temperatures[2:]
    best = (float('inf'), None)
    started = time.monotonic()
    for n, seed in enumerate(seeds[:args.starts]):
        x = seed
        for t in temperatures:
            x = projected_bfgs(x, t, args.steps)
            gains, _, payoff, deleted, joint = full_rows(x)
            error = max(0., float(np.max(gains)))
            if error < best[0]:
                best = error, x.copy()
            print('START', n, 'TEMP', t, 'E', error, 'C', joint, 'MAX_DELETED', max(deleted), 'TIME', round(time.monotonic()-started, 2), flush=True)
            if error < 1e-7:
                break
        print('PROFILE', n, x.reshape(4, 4).tolist(), flush=True)
        if best[0] < 1e-7:
            break
    print('BEST', best[0], best[1].reshape(4, 4).tolist(), flush=True)
    if max(full_rows(best[1])[3]) < 1:
        exact_check(best[1])


if __name__ == '__main__':
    main()
