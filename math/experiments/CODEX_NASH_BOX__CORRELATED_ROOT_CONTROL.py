"""Exact four-active correlated-root certificate and bounded discovery.

This controls relaxed joint laws, NOT an actual independent-game producer.
All full caps include every finite deadline and literal Never.  Discovery
is local floating-point optimization, not global minimization or existence.
"""

import argparse
from fractions import Fraction as F

import numpy as np

from CODEX_NASH_BOX__FINITE_CLOCK_JOINT_APPROXIMATION import reward_table


BITS = ((np.arange(16)[:, None] >> np.arange(4)) & 1).astype(float)
MASK_BITS = BITS.T
REMAINING = np.array([[a & ~b for b in range(16)] for a in range(16)])
TRANSFER = np.eye(16)[REMAINING]
ROOT_REWARD = reward_table().astype(float)
ROOT_QUIT = np.array([[ROOT_REWARD[i, b | (1 << i)] for b in range(16)]
                      for i in range(4)])
ROOT_CONT = np.array([[ROOT_REWARD[i, b & ~(1 << i)] for b in range(16)]
                      for i in range(4)])
ROOT_ALPHA = np.array([[int(not (b & ~(1 << i))) for b in range(16)]
                       for i in range(4)])


def entropy(p):
    p = np.asarray(p)
    return -(p * np.log(np.maximum(p, 1e-300))).sum(axis=-1)


def information(p, mask):
    marginal = p @ BITS
    joint = np.bincount(np.arange(16) & mask, weights=p, minlength=16)
    return sum(entropy([marginal[i], 1 - marginal[i]]) for i in range(4)
               if mask >> i & 1) - entropy(joint)


def root_data(v, cap):
    reward = reward_table().astype(float)
    prescribed = reward.copy()
    prescribed[:, 0] = v
    quit_now = np.array([[reward[i, b | (1 << i)] for b in range(16)]
                         for i in range(4)])
    continue_cap = np.array([
        [reward[i, b & ~(1 << i)] if b & ~(1 << i) else cap[i]
         for b in range(16)] for i in range(4)])
    return prescribed, quit_now, continue_cap


def update(v, cap, info, pi):
    prescribed, quit_now, continue_cap = root_data(v, cap)
    next_info = np.array([
        information(pi, a) + sum(pi[b] * info[a & ~b] for b in range(16))
        for a in range(16)])
    return prescribed @ pi, np.maximum(quit_now @ pi, continue_cap @ pi), next_info


def log_interval(x, terms=24):
    """Rational enclosure by log x = 2 atanh((x-1)/(x+1))."""
    x = F(x)
    assert x > 0
    shift = 0
    while x < 1:
        x *= 2
        shift -= 1
    while x > 2:
        x /= 2
        shift += 1

    def normalized(y):
        z = (y - 1) / (y + 1)
        value = 2 * sum((z ** (2 * k + 1)) / (2 * k + 1) for k in range(terms))
        error = 2 * abs(z) ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
        return value - error, value + error

    lo, hi = normalized(x)
    two_lo, two_hi = normalized(F(2))
    return (lo + shift * (two_lo if shift >= 0 else two_hi),
            hi + shift * (two_hi if shift >= 0 else two_lo))


def entropy_interval(p):
    lo = hi = F(0)
    for x in p:
        if x:
            a, b = log_interval(x)
            lo -= x * b
            hi -= x * a
    return lo, hi


def information_interval(p, mask):
    lo = hi = F(0)
    for i in range(4):
        if mask >> i & 1:
            q = sum(p[b] for b in range(16) if b >> i & 1)
            a, b = entropy_interval([q, 1 - q])
            lo += a
            hi += b
    joint = [sum(p[b] for b in range(16) if b & mask == a)
             for a in range(16) if a & mask == a]
    a, b = entropy_interval(joint)
    return lo - b, hi - a


def certificate():
    reward = reward_table().tolist()
    mu = [F(int(b in (3, 6, 12, 9, 15)), 5) for b in range(16)]
    pi = [F(0)] * 16
    pi[0] = F(1, 5)
    for b in (1, 2, 4, 8):
        pi[b] = F(1, 12)
    for b in (3, 6, 12, 9):
        pi[b] = F(7, 60)
    assert sum(mu) == sum(pi) == 1
    v = [sum(mu[b] * reward[i][b] for b in range(16)) for i in range(4)]
    cap = []
    for i in range(4):
        q = sum(mu[b] * reward[i][b | (1 << i)] for b in range(16))
        n = sum(mu[b] * reward[i][b & ~(1 << i)] for b in range(16))
        # All mu-supported coalitions contain >=2 players, so late=Never.
        cap.append(max(q, n))
    assert v == cap == [F(12, 5)] * 4
    u, new_cap = [], []
    for i in range(4):
        u.append(sum(pi[b] * (reward[i][b] if b else v[i]) for b in range(16)))
        q = sum(pi[b] * reward[i][b | (1 << i)] for b in range(16))
        c = sum(pi[b] * (reward[i][b & ~(1 << i)] if b & ~(1 << i) else cap[i])
                for b in range(16))
        assert q == F(1, 4)
        new_cap.append(max(q, c))
    assert u == new_cap == [F(187, 150)] * 4
    old_lo, old_hi = information_interval(mu, 15)
    new_lo, new_hi = information_interval(pi, 15)
    for b in range(16):
        lo, hi = information_interval(mu, 15 ^ b)
        new_lo += pi[b] * lo
        new_hi += pi[b] * hi
    assert old_lo > F(108, 100)
    assert new_hi < F(705, 1000)
    print("EXACT PASS: old full-coarse value/cap=12/5; new value/cap=187/150")
    print("EXACT PASS: old information>1.08; new information<0.705 (natural logs)")
    print("enclosures", (float(old_lo), float(old_hi)), (float(new_lo), float(new_hi)))


def state_consistency():
    """Independent complete-clock enumeration, not the root evaluator."""
    reward = reward_table().tolist()
    law = {(-1, -1, -1, -1): F(1)}
    v, cap = [F(0)] * 4, [F(1)] * 4
    info_lo, info_hi = [F(0)] * 16, [F(0)] * 16
    for t in range(3):
        counts = [1 + ((7 * b + 3 * t) % 17) for b in range(16)]
        pi = [F(c, sum(counts)) for c in counts]
        next_law = {}
        for clocks, mass in law.items():
            for b, weight in enumerate(pi):
                updated = tuple(0 if b >> i & 1 else
                                (-1 if clocks[i] == -1 else clocks[i] + 1)
                                for i in range(4))
                next_law[updated] = next_law.get(updated, F(0)) + mass * weight
        law = next_law
        old_v, old_cap = v, cap
        v = [sum(pi[b] * (reward[i][b] if b else old_v[i]) for b in range(16))
             for i in range(4)]
        cap = [max(sum(pi[b] * reward[i][b | (1 << i)] for b in range(16)),
                   sum(pi[b] * (reward[i][b & ~(1 << i)] if b & ~(1 << i)
                                else old_cap[i]) for b in range(16))) for i in range(4)]
        root_bounds = [information_interval(pi, a) for a in range(16)]
        info_lo = [root_bounds[a][0] + sum(pi[b] * info_lo[a & ~b] for b in range(16))
                   for a in range(16)]
        info_hi = [root_bounds[a][1] + sum(pi[b] * info_hi[a & ~b] for b in range(16))
                   for a in range(16)]

    def payoff(clocks, i):
        finite = [x for x in clocks if x >= 0]
        if not finite:
            return 0
        first = min(finite)
        return reward[i][sum(1 << j for j in range(4) if clocks[j] == first)]

    direct_v = [sum(weight * payoff(clocks, i) for clocks, weight in law.items())
                for i in range(4)]
    direct_cap = [max(sum(weight * payoff(clocks[:i] + (deadline,) + clocks[i + 1:], i)
                          for clocks, weight in law.items())
                      for deadline in (-1, 0, 1, 2, 3)) for i in range(4)]
    assert direct_v == v and direct_cap == cap

    def marginal_entropy(indices):
        marginal = {}
        for clocks, weight in law.items():
            key = tuple(clocks[i] for i in indices)
            marginal[key] = marginal.get(key, F(0)) + weight
        return entropy_interval(marginal.values())

    individual = [marginal_entropy([i]) for i in range(4)]
    for a in range(16):
        indices = [i for i in range(4) if a >> i & 1]
        joint_lo, joint_hi = marginal_entropy(indices)
        direct_lo = sum(individual[i][0] for i in indices) - joint_hi
        direct_hi = sum(individual[i][1] for i in indices) - joint_lo
        assert max(direct_lo, info_lo[a]) <= min(direct_hi, info_hi[a])
    print('EXACT STATE PASS: three roots, all values/caps, all16 subset information enclosures')


def simplex_project(p):
    ordered = np.sort(p, axis=1)[:, ::-1]
    cumulative = np.cumsum(ordered, axis=1) - 1
    index = (ordered - cumulative / np.arange(1, 17) > 0).sum(axis=1) - 1
    threshold = cumulative[np.arange(len(p)), index] / (index + 1)
    return np.maximum(p - threshold[:, None], 0)


def explore(steps, starts, iterations, seed, asymmetric):
    rng = np.random.default_rng(seed)
    mu = np.zeros(16)
    mu[[3, 6, 12, 9, 15]] = [.24, .24, .21, .21, .1] if asymmetric else .2
    v = reward_table() @ mu
    _, quit, never = root_data(np.zeros(4), np.ones(4))
    cap = np.maximum(quit @ mu, never @ mu)
    assert np.min(v - cap) >= -1e-12
    info = np.array([information(mu, a) for a in range(16)])
    sigma = np.zeros(16)
    sigma[[3, 6, 12, 9]] = .25
    for step in range(steps):
        prescribed, quit, cont = root_data(v, cap)
        guards = np.vstack((prescribed - quit, prescribed - cont))
        loss = info[15 ^ np.arange(16)]

        def objective(p):
            z = p @ BITS
            return entropy(np.stack((z, 1 - z), axis=-1)).sum(axis=1) - entropy(p) + p @ loss

        p = rng.dirichlet(np.ones(16) * .5, starts)
        p[0], p[1] = sigma, np.eye(16)[0]
        best_value, best_pi = float("inf"), None
        for penalty in (10, 100, 1000):
            first = np.zeros_like(p)
            second = np.zeros_like(p)
            for t in range(iterations):
                z = np.clip(p @ BITS, 1e-12, 1 - 1e-12)
                gradient = (np.log(np.maximum(p, 1e-12)) - np.log(z) @ BITS.T
                            - np.log(1 - z) @ (1 - BITS).T + loss
                            + 2 * penalty * np.minimum(p @ guards.T, 0) @ guards)
                first = .9 * first + .1 * gradient
                second = .999 * second + .001 * gradient ** 2
                direction = (first / (1 - .9 ** (t + 1))) / (np.sqrt(second / (1 - .999 ** (t + 1))) + 1e-8)
                p = simplex_project(p - .004 / (1 + t / 1000) * direction)
                if t % 100 == 0:
                    error = np.maximum(0, -np.min(p @ guards.T, axis=1))
                    weight = error / (error + .25)
                    repaired = (1 - weight[:, None]) * p + weight[:, None] * sigma
                    values = objective(repaired)
                    index = values.argmin()
                    if values[index] < best_value:
                        best_value, best_pi = values[index], repaired[index].copy()
        next_v, next_cap, next_info = update(v, cap, info, best_pi)
        print("LOCAL DISCOVERY", step, "information", info[-1], "to", next_info[-1],
              "payoff", next_v, "slack", next_v - next_cap, flush=True)
        print("root law", np.round(best_pi, 8), flush=True)
        if next_info[-1] >= info[-1] - 1e-6:
            break
        v, cap, info = next_v, next_cap, next_info


def word_evaluate(word, penalty, gradient=True):
    """Batched exact state recursion; word is stored LATE-to-EARLY.

    Start with literal all-Never, not a coarse seed. Only FINAL obedience
    is penalized; no root/conditional/intermediate obedience is imposed.
    The returned gradient is ordinary floating-point analytic backprop.
    """
    batch, depth, _ = word.shape
    v = np.zeros((batch, 4))
    cap = np.ones((batch, 4))
    info = np.zeros((batch, 16))
    history = []
    for t in range(depth):
        pi = word[:, t]
        z = np.clip(pi @ BITS, 1e-14, 1 - 1e-14)
        bit_log = (BITS[None] * np.log(z)[:, None]
                   + (1 - BITS)[None] * np.log(1 - z)[:, None])
        h_bits = entropy(np.stack((z, 1 - z), axis=-1))
        root_info = np.zeros((batch, 16))
        root_jac = np.zeros((batch, 16, 16))
        for a in range(16):
            if a.bit_count() <= 1:
                continue
            projection = np.arange(16) & a
            grouped = pi @ np.eye(16)[projection]
            root_info[:, a] = h_bits @ BITS[a] - entropy(grouped)
            root_jac[:, a] = (np.log(np.maximum(grouped[:, projection], 1e-14))
                              - bit_log @ BITS[a])
        alpha = pi @ ROOT_ALPHA.T
        q = pi @ ROOT_QUIT.T
        c = pi @ ROOT_CONT.T + alpha * cap
        quit_branch = q >= c
        if gradient:
            history.append((pi, v, cap, info, alpha, quit_branch, root_jac))
        v = pi @ ROOT_REWARD.T + pi[:, :1] * v
        cap = np.maximum(q, c)
        info = root_info + (pi[:, None, :] * info[:, REMAINING]).sum(axis=2)
    gain = np.maximum(cap - v, 0)
    objective = info[:, 15] + penalty * (gain * gain).sum(axis=1)
    if not gradient:
        return objective, info[:, 15], gain.max(axis=1), v, cap
    adv, adc = -2 * penalty * gain, 2 * penalty * gain
    adi = np.zeros((batch, 16))
    adi[:, 15] = 1
    derivative = np.empty_like(word)
    for t in range(depth - 1, -1, -1):
        pi, old_v, old_cap, old_info, alpha, quit_branch, root_jac = history[t]
        prescribed = np.broadcast_to(ROOT_REWARD, (batch, 4, 16)).copy()
        prescribed[:, :, 0] = old_v
        cap_jac = np.where(quit_branch[:, :, None], ROOT_QUIT[None],
                           ROOT_CONT[None] + old_cap[:, :, None] * ROOT_ALPHA[None])
        info_jac = root_jac + old_info[:, REMAINING]
        derivative[:, t] = (np.einsum('ni,nib->nb', adv, prescribed)
                             + np.einsum('ni,nib->nb', adc, cap_jac)
                             + np.einsum('na,nab->nb', adi, info_jac))
        adv = pi[:, :1] * adv
        adc = alpha * adc * ~quit_branch
        adi = np.einsum('na,nb,abs->ns', adi, pi, TRANSFER)
    return objective, derivative, info[:, 15], gain.max(axis=1), v, cap


def explore_word(depth, starts, iterations, seed):
    rng = np.random.default_rng(seed)
    word = rng.dirichlet(np.ones(16), (starts, depth))
    # Initial independent, asymmetric root laws. The optimizer may leave
    # independence, and may increase or decrease every payoff coordinate.
    hazards = rng.uniform(.01, .6, (starts // 2, depth, 4))
    word[:starts // 2] = np.prod(np.where(BITS[None, None], hazards[:, :, None],
                                         1 - hazards[:, :, None]), axis=3)
    direction = rng.normal(size=word[:1].shape)
    direction -= direction.mean(axis=2, keepdims=True)
    eps = 1e-7
    objective, derivative, *_ = word_evaluate(word[:1], 10)
    fd = (word_evaluate(word[:1] + eps * direction, 10, False)[0]
          - word_evaluate(word[:1] - eps * direction, 10, False)[0]) / (2 * eps)
    print('WORD tangent gradient discrepancy', abs(float(fd[0] - (derivative * direction).sum())))
    for penalty in (10, 100, 1000):
        first = np.zeros_like(word)
        second = np.zeros_like(word)
        for t in range(iterations):
            objective, derivative, *_ = word_evaluate(word, penalty)
            first = .9 * first + .1 * derivative
            second = .999 * second + .001 * derivative ** 2
            direction = (first / (1 - .9 ** (t + 1))) / (np.sqrt(second / (1 - .999 ** (t + 1))) + 1e-8)
            word = simplex_project((word - .002 / (1 + t / 2000) * direction).reshape(-1, 16)).reshape(word.shape)
        objective, inf, gap, v, cap = word_evaluate(word, penalty, False)
        index = objective.argmin()
        print('JOINT WORD LOCAL DISCOVERY', depth, penalty, 'information', inf[index],
              'full coarse violation', gap[index], 'payoff', v[index], flush=True)
    print('No global optimality, exact auxiliary obedience, or all-errors conclusion.')


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--explore", action="store_true")
    parser.add_argument("--word-depth", type=int, default=0)
    parser.add_argument("--check-state", action="store_true")
    parser.add_argument("--asymmetric", action="store_true")
    parser.add_argument("--steps", type=int, default=10)
    parser.add_argument("--starts", type=int, default=64)
    parser.add_argument("--iterations", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=442)
    args = parser.parse_args()
    certificate()
    if args.check_state:
        state_consistency()
    if args.explore:
        explore(args.steps, args.starts, args.iterations, args.seed, args.asymmetric)
    if args.word_depth:
        explore_word(args.word_depth, args.starts, args.iterations, args.seed)
