"""Discount-root search and optional exact finite-word check on literal K10.

Search roots satisfy all binary inequalities numerically; enumeration is not
complete. Default continuation is an actual stationary discounted component.
--literal-seed uses an actual half-13 finite clock profile. --terminal and
--cap-terminal deliberately replace ONLY the declared discounted terminal
vector by an UNREALIZED vector: finite search words are not called exact Nash.
--check-exact rounds the searched word and verifies full original caps and a
discounted approximate-Nash bound by integer arithmetic, with an actual half-13
physical tail. It never certifies an infinite return or an all-errors producer.
"""

import argparse
from fractions import Fraction
from itertools import combinations

import numpy as np


R = np.zeros((16, 4))
for mask in range(1, 16):
    coalition = [i for i in range(4) if mask >> i & 1]
    if len(coalition) == 1:
        owner = coalition[0]
        R[mask, owner] = 1
        R[mask, (owner + 2) % 4] = 4
    elif len(coalition) == 2:
        R[mask, :] = 1
        if (coalition[0] - coalition[1]) % 2 == 0:
            R[mask, coalition] = 0
        else:
            owner = next(i for i in coalition if (i + 1) % 4 in coalition)
            R[mask, owner] = -1
            R[mask, (owner + 1) % 4] = 2
    elif len(coalition) == 3:
        R[mask, :] = -1
        R[mask, next(i for i in range(4) if i not in coalition)] = 10
    else:
        R[mask, :] = 9


def data(q):
    quit = np.zeros(4)
    absorbed = np.zeros(4)
    survive = np.zeros(4)
    for i in range(4):
        opponents = [j for j in range(4) if j != i]
        for word in range(8):
            probability, mask = 1.0, 0
            for k, j in enumerate(opponents):
                if word >> k & 1:
                    probability *= q[j]
                    mask |= 1 << j
                else:
                    probability *= 1 - q[j]
            quit[i] += probability * R[mask | 1 << i, i]
            if mask:
                absorbed[i] += probability * R[mask, i]
            else:
                survive[i] = probability
    return quit, absorbed, survive


def roots(v, alpha):
    """Support <=3 is enumerated; full-support Newton is not complete."""
    w, result = alpha * v, []

    def add(q):
        if not np.all(np.isfinite(q)) or np.min(q) < -1e-7 or np.max(q) > 1 - 1e-8:
            return
        q = np.maximum(q, 0)
        quit, absorbed, survive = data(q)
        gain = quit - absorbed - survive * w
        if max(abs(gain[q > 1e-7]), default=0) > 1e-6:
            return
        if max(gain[q <= 1e-7], default=-1) > 1e-7:
            return
        if not any(np.max(abs(q - other)) < 1e-6 for other in result):
            result.append(q)

    if min(w) >= 1:
        add(np.zeros(4))
    for i, j in combinations(range(4), 2):
        if (j - i) % 2 == 0:
            if min(abs(5 - w[j]), abs(5 - w[i])) < 1e-12:
                continue
            q = np.zeros(4)
            q[i], q[j] = (1 - w[j]) / (5 - w[j]), (1 - w[i]) / (5 - w[i])
        else:
            if (j - i) % 4 != 1:
                i, j = j, i
            q = np.zeros(4)
            if min(abs(w[j] + 1), abs(2 - w[i])) < 1e-12:
                continue
            q[i], q[j] = (w[j] - 1) / (w[j] + 1), (1 - w[i]) / (2 - w[i])
        add(q)
    for k in range(4):
        w0, w1, w2 = np.roll(w, -k)[:3]
        nb, db = np.array([w0 - 1, 5 - w0]), np.array([w0 - 2, 4 - w0])
        na, da = np.array([w1 - 1, 2 - w1]), np.array([1 + w1, -2 - w1])
        mul = np.polynomial.polynomial.polymul
        add_poly = np.polynomial.polynomial.polyadd
        polynomial = add_poly(add_poly((1 - w2) * mul(da, db), (w2 - 5) * mul(na, db)),
                              add_poly((1 + w2) * mul(nb, da), (1 - w2) * mul(na, nb)))
        for c in np.polynomial.polynomial.polyroots(polynomial):
            if abs(c.imag) > 1e-7:
                continue
            c = c.real
            if abs(np.polyval(da[::-1], c) * np.polyval(db[::-1], c)) < 1e-12:
                continue
            a = np.polyval(na[::-1], c) / np.polyval(da[::-1], c)
            b = np.polyval(nb[::-1], c) / np.polyval(db[::-1], c)
            add(np.roll(np.array([a, b, c, 0.0]), k))
    def gains(q):
        quit, absorbed, survive = data(q)
        return quit - absorbed - survive * w

    for initial in ([] if result else [0.001, 0.01, 0.05, 0.15, 0.4]):
        q = np.full(4, initial)
        for _ in range(30):
            gain = gains(q)
            if np.max(abs(gain)) < 1e-10:
                add(q)
                break
            columns = []
            for i in range(4):
                perturbed = q.copy()
                perturbed[i] += 1e-6
                columns.append((gains(perturbed) - gain) / 1e-6)
            try:
                step = np.linalg.solve(np.array(columns).T, gain)
            except np.linalg.LinAlgError:
                break
            scale = 1.0
            while scale > 1e-5:
                new_q = q - scale * step
                if np.max(abs(new_q)) < 5 and np.max(abs(gains(new_q))) < np.max(abs(gain)):
                    q = new_q
                    break
                scale *= 0.5
            else:
                break
    return result


def seed(alpha):
    def equation(q):
        quit, absorbed, survive = data(np.full(4, q))
        return quit[0] * (1 - alpha * survive[0]) - absorbed[0]

    low, high = 1e-14, 0.2
    assert equation(low) > 0 > equation(high)
    for _ in range(70):
        mid = (low + high) / 2
        if equation(mid) > 0:
            low = mid
        else:
            high = mid
    q = (low + high) / 2
    quit, absorbed, survive = data(np.full(4, q))
    joint = (1 - q) ** 4
    original = (q * quit + (1 - q) * absorbed) / (1 - joint)
    cap = np.maximum(quit, absorbed / (1 - survive))
    return q, (quit, original, cap)


def prepend(state, q, alpha):
    discounted, original, cap = state
    quit, absorbed, survive = data(q)
    joint = np.prod(1 - q)
    immediate = q * quit + (1 - q) * absorbed
    return (immediate + alpha * joint * discounted, immediate + joint * original,
            np.maximum(quit, absorbed + survive * cap))


def integer_check(word, alpha, terminal):
    """All output inequalities here are integer comparisons, not float tests."""
    denominator = 10 ** 12
    d3, d4 = denominator ** 3, denominator ** 4
    discount = Fraction(str(alpha))
    an, ad = discount.numerator, discount.denominator
    terminal = [Fraction(str(x)) for x in terminal]
    assert all(abs(x) <= 10 for x in terminal)
    vd = 1
    for x in terminal:
        vd = np.lcm(vd, x.denominator).item()
    vi = [int(x * vd) for x in terminal]
    ui, bi, od = [1, 5, 1, 5], [2, 10, 2, 10], 4
    opponent_numerators = [1] * 4
    max_root_gap, max_active_residual = 0.0, 0.0
    for q in word:
        k = [int(round(float(x) * denominator)) for x in q]
        assert all(0 <= x < denominator for x in k)
        qnum, bnum, lnum = [], [], []
        for i in range(4):
            opp = [j for j in range(4) if j != i]
            qi = ai = li = 0
            for m in range(8):
                probability, mask = 1, 0
                for bit, j in enumerate(opp):
                    if m >> bit & 1:
                        probability *= k[j]
                        mask |= 1 << j
                    else:
                        probability *= denominator - k[j]
                qi += probability * int(R[mask | 1 << i, i])
                if mask:
                    ai += probability * int(R[mask, i])
                else:
                    li = probability
            qnum.append(qi)
            bnum.append(ai)
            lnum.append(li)
        joint = 1
        for x in k:
            joint *= denominator - x
        immediate = [k[i] * qnum[i] + (denominator - k[i]) * bnum[i]
                     for i in range(4)]
        new_vd = vd * ad * d4
        new_vi = [immediate[i] * ad * vd + an * joint * vi[i] for i in range(4)]
        for i in range(4):
            quit_endpoint = qnum[i] * denominator * ad * vd
            continue_endpoint = (bnum[i] * denominator * ad * vd
                                 + lnum[i] * denominator * an * vi[i])
            # Independent Bellman reconstruction, with the same denominator.
            direct = (k[i] * qnum[i] * ad * vd
                      + (denominator - k[i]) * (bnum[i] * ad * vd + lnum[i] * an * vi[i]))
            assert direct == new_vi[i]
            root_gap = max(quit_endpoint, continue_endpoint) - new_vi[i]
            assert root_gap >= 0
            assert root_gap * 10 ** 10 <= new_vd, 'root debt exceeds 1e-10'
            max_root_gap = max(max_root_gap, root_gap / new_vd)
            if k[i]:
                max_active_residual = max(max_active_residual,
                                          abs(quit_endpoint - continue_endpoint) / new_vd)
            opponent_numerators[i] *= lnum[i]
        ui = [immediate[i] * od + joint * ui[i] for i in range(4)]
        bi = [max(qnum[i] * denominator * od,
                  bnum[i] * denominator * od + lnum[i] * denominator * bi[i])
              for i in range(4)]
        od *= d4
        vi, vd = new_vi, new_vd
        assert all(abs(x) <= 10 * vd for x in vi)
    actual_gap = max(bi[i] - ui[i] for i in range(4))
    # A convenient strict rational upper bound, checked independently.
    bound = Fraction(int(np.ceil((actual_gap / od) * 10 ** 6)) + 1, 10 ** 6)
    assert actual_gap * bound.denominator < bound.numerator * od
    opp_den = d3 ** len(word)
    tail_exponent = 0
    while max(opponent_numerators) * 10 ** (tail_exponent + 1) < opp_den:
        tail_exponent += 1
    assert tail_exponent > 0
    # Discard at most the last decimal of the logarithmic enclosure.
    assert max(opponent_numerators) * 10 ** tail_exponent < opp_den
    print('INTEGER_CHECK PASS original_full_E <', str(bound),
          '; max_binary_root_debt ≈', max_root_gap,
          '; active_Q-C_residual ≈', max_active_residual,
          '; max_root_debt/(1-alpha) ≈', max_root_gap / (1 - alpha),
          '; exact_Bellman_residual = 0', flush=True)
    print('ALL deleted prefix survivals < 10^(-%d)' % tail_exponent,
          '; full original tail change <=40*10^(-%d)' % tail_exponent,
          '; discounted full regret <=1e-10/(1-alpha)+25*10^(-%d)' % tail_exponent,
          flush=True)


def run(alpha, steps, literal_seed=False, selector='debt', cap_terminal=False, terminal=None,
        check_exact=False):
    if literal_seed:
        original = np.array([0.25, 1.25, 0.25, 1.25])
        state = (original.copy(), original.copy(), np.array([0.5, 2.5, 0.5, 2.5]))
        q = 'literal_half_13'
        if cap_terminal:
            state = (state[2].copy(), state[1], state[2])
            q = 'UNREALIZED_cap_terminal_values'
    else:
        q, state = seed(alpha)
    if terminal is not None:
        state = (np.array(terminal), state[1], state[2])
        q = 'UNREALIZED_terminal_values'
    print('alpha', alpha, 'tail', q, 'tail_E', max(state[2] - state[1]))
    declared_terminal = state[0].copy()
    word = []
    for n in range(steps):
        choices = [(prepend(state, q, alpha), q) for q in roots(state[0], alpha)]
        if not choices:
            print('NO SAMPLED ROOT', n, state[0])
            return
        if selector == 'sum':
            state, q = max(choices, key=lambda choice: sum(choice[0][0]))
        else:
            state, q = min(choices, key=lambda choice: max(choice[0][2] - choice[0][1]))
        word.append(q.copy())
        if n in [0, 1, 2, 4, 9, 49, 99, 199, steps - 1]:
            print(n + 1, 'E', round(max(state[2] - state[1]), 10),
                  'q', np.round(q, 6), 'v', np.round(state[0], 6))
    if check_exact:
        assert literal_seed, 'integer physical tail is the actual half-13 profile'
        assert alpha < 1, 'discounted source bound uses 1-alpha>0'
        integer_check(word, alpha, declared_terminal)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--alpha', type=float, default=0.999)
    parser.add_argument('--steps', type=int, default=500)
    parser.add_argument('--literal-seed', action='store_true')
    parser.add_argument('--selector', choices=['debt', 'sum'], default='debt')
    parser.add_argument('--cap-terminal', action='store_true')
    parser.add_argument('--terminal', nargs=4, type=float)
    parser.add_argument('--check-exact', action='store_true')
    args = parser.parse_args()
    run(args.alpha, args.steps, args.literal_seed, args.selector, args.cap_terminal,
        args.terminal, args.check_exact)
