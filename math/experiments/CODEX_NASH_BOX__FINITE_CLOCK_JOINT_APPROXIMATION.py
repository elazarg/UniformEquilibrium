"""Joint finite-clock approximation on the K10 four-player table.

Exploratory optimization is floating point.  The final integer certificate
checker uses only Python integers and Fractions, including the omitted late
deadline and literal Never.  No auxiliary exact-Nash assertion is used.
"""

import argparse
from fractions import Fraction
import itertools
import time

import numpy as np


def reward_table(k=10):
    r = np.zeros((4, 16), dtype=int)
    for coalition in range(1, 16):
        members = [i for i in range(4) if coalition >> i & 1]
        if len(members) == 1:
            i = members[0]
            r[i, coalition] = 1
            r[(i + 2) % 4, coalition] = 4
        elif len(members) == 2:
            for i in range(4):
                r[i, coalition] = 0 if i in members else 1
            for i in members:
                if (i + 1) % 4 in members:
                    r[i, coalition] = -1
                    r[(i + 1) % 4, coalition] = 2
        elif len(members) == 3:
            for i in range(4):
                r[i, coalition] = -1 if i in members else k
        else:
            r[:, coalition] = k - 1
    return r


def exact_certificate(counts, denominator, k=10):
    """Return exact values/caps/gaps for independent complete clock laws.

    Columns 0,...,M-1 are finite dates; the last is literal Never.
    Payoffs of ANY later finite deadline equal the displayed late cap.
    """
    counts = [[int(x) for x in row] for row in counts]
    assert len(counts) == 4 and len(set(map(len, counts))) == 1
    assert all(min(row) >= 0 and sum(row) == denominator for row in counts)
    m = len(counts[0]) - 1
    r = reward_table(k).tolist()
    survival = [[sum(row[t:]) for t in range(m + 1)] for row in counts]
    values = [0] * 4
    for t in range(m):
        for mask in range(1, 16):
            probability_numerator = 1
            for j in range(4):
                probability_numerator *= counts[j][t] if mask >> j & 1 else survival[j][t + 1]
            for i in range(4):
                values[i] += probability_numerator * r[i][mask]
    all_caps = []
    for i in range(4):
        opponents = [j for j in range(4) if j != i]
        cumulative = 0
        caps = []
        for t in range(m):
            quit_now = 0
            for bits in itertools.product((0, 1), repeat=3):
                mask = sum(bit << j for bit, j in zip(bits, opponents))
                probability_numerator = 1
                for bit, j in zip(bits, opponents):
                    probability_numerator *= counts[j][t] if bit else survival[j][t + 1]
                quit_now += probability_numerator * r[i][mask | (1 << i)]
            caps.append(cumulative + quit_now)
            for bits in itertools.product((0, 1), repeat=3):
                mask = sum(bit << j for bit, j in zip(bits, opponents))
                if not mask:
                    continue
                probability_numerator = 1
                for bit, j in zip(bits, opponents):
                    probability_numerator *= counts[j][t] if bit else survival[j][t + 1]
                cumulative += probability_numerator * r[i][mask]
        never = cumulative
        late = never + r[i][1 << i] * np.prod([counts[j][-1] for j in opponents], dtype=object)
        caps.extend((int(late), never))
        all_caps.append(caps)
    d4 = denominator ** 4
    result = {
        "values": [Fraction(v, d4) for v in values],
        "caps": [Fraction(max(c), denominator ** 3) for c in all_caps],
        "maximizers": [[j if j < m else ("Late" if j == m else "Never")
                        for j, v in enumerate(c) if v == max(c)] for c in all_caps],
        "gaps": [Fraction(max(all_caps[i]) * denominator - values[i], d4) for i in range(4)],
        "joint_never": Fraction(int(np.prod([row[-1] for row in counts], dtype=object)), d4),
    }
    return result


class ClockProblem:
    def __init__(self, m, k=10):
        self.m, self.a = m, m + 1
        index = np.indices((self.a,) * 4)
        minimum = index.min(axis=0)
        mask = sum((index[i] == minimum) * (1 << i) for i in range(4))
        mask[minimum == m] = 0
        self.u = reward_table(k)[:, mask].astype(float)

    @staticmethod
    def contract(tensor, p, free):
        letters = "abcd"
        eq = letters + "," + ",".join(letters[j] for j in range(4) if j != free) + "->" + letters[free]
        return np.einsum(eq, tensor, *[p[j] for j in range(4) if j != free], optimize=True)

    def conditional_values(self, p, recipient, controlled):
        return self.contract(self.u[recipient], p, controlled)

    def evaluate_probabilities(self, p, temperature, gradient=True):
        q = np.array([self.conditional_values(p, i, i) for i in range(4)])
        value = (p * q).sum(axis=1)
        late = np.array([q[i, -1] + np.prod([p[j, -1] for j in range(4) if j != i]) for i in range(4)])
        gains = np.concatenate((q - value[:, None], (late - value)[:, None]), axis=1)
        flat = np.concatenate(([0.], gains.ravel()))
        if temperature:
            weights = np.exp((flat - flat.max()) / temperature)
            weights /= weights.sum()
            objective = flat.max() + temperature * np.log(np.exp((flat - flat.max()) / temperature).sum())
        else:
            weights = 2 * np.maximum(flat, 0)
            objective = np.maximum(flat, 0) @ np.maximum(flat, 0)
        result = (objective, flat.max(), p, value, np.argmax(gains, axis=1))
        if not gradient:
            return result
        w = weights[1:].reshape((4, self.a + 1))
        totals = w.sum(axis=1)
        gp = np.zeros_like(p)
        for i in range(4):
            gp[i] -= totals[i] * q[i]
            alternative = w[i, :self.a].copy()
            alternative[-1] += w[i, -1]
            signed = p.copy()
            signed[i] = alternative - totals[i] * p[i]
            for j in range(4):
                if j == i:
                    continue
                gp[j] += self.conditional_values(signed, i, j)
                gp[j, -1] += w[i, -1] * np.prod([p[h, -1] for h in range(4) if h != i and h != j])
        return result + (gp,)

    def evaluate(self, logits, temperature, gradient=True):
        p = np.exp(logits - logits.max(axis=1)[:, None])
        p /= p.sum(axis=1)[:, None]
        result = self.evaluate_probabilities(p, temperature, gradient)
        if not gradient:
            return result
        gp = result[-1]
        return result[:-1] + (p * (gp - (gp * p).sum(axis=1)[:, None]),)


class LinearClockProblem(ClockProblem):
    """The same objective/gradient with memory linear in the calendar length."""

    def __init__(self, m, k=10):
        self.m, self.a = m, m + 1
        self.r = reward_table(k)
        self.bits = np.array(list(itertools.product((0, 1), repeat=3)), dtype=bool)
        self.opponents = [[j for j in range(4) if j != i] for i in range(4)]
        self.masks = [np.array([sum(int(bit) << j for bit, j in zip(bits, self.opponents[i]))
                               for bits in self.bits]) for i in range(4)]

    def conditional_values(self, p, recipient, controlled):
        survival = np.cumsum(p[:, ::-1], axis=1)[:, ::-1]
        others = self.opponents[controlled]
        factor = np.where(self.bits[:, :, None], p[others, :self.m][None, :, :],
                          survival[others, 1:][None, :, :])
        weights = factor.prod(axis=1)
        masks = self.masks[controlled]
        earlier = self.r[recipient, masks] @ weights
        immediate = self.r[recipient, masks | (1 << controlled)] @ weights
        prefix = np.concatenate(([0.], np.cumsum(earlier)))
        return np.concatenate((prefix[:-1] + immediate, prefix[-1:]))


SEED_EIGHT = np.array([
    [.066055407, .000000001, 0, 0, 0, .152937373, .224369886, .275942256, .280695075],
    [0, 0, 0, .068110043, .022726812, .278437977, .325186588, .305538579, .000000001],
    [.055072938, .035617889, .068274964, .224147113, .261994645, .037443946, 0, 0, .317448505],
    [.197586518, .227524724, .166377126, .039711540, .000000001, .000041109, .016818901, 0, .351940081],
])

SEED_TWELVE = np.array([
    [0, 0, 0, 24682486, 56004485, 40545380, 76849810, 159598653, 210392427, 0, 189643070, 184503760, 57779929],
    [45779179, 16483313, 32206787, 90087924, 157497111, 179284788, 89791153, 53953258, 10687468, 22, 261566993, 62661929, 75],
    [189184616, 224977118, 135204795, 48546075, 25766221, 1, 0, 0, 12, 151183387, 0, 8, 225137767],
    [67125644, 4, 0, 0, 0, 0, 896, 65153159, 26680768, 407398247, 0, 1, 433641281],
]) / 10 ** 9

# A compact independently checkable outcome of the joint search, not an
# all-errors family or a claim that the nonconvex optimization is global.
CERTIFICATE_TWELVE = [
    [0, 0, 0, 215, 554, 383, 909, 1680, 2111, 0, 2040, 1842, 266],
    [416, 188, 312, 857, 1599, 1842, 947, 526, 114, 0, 2966, 233, 0],
    [1772, 2209, 1538, 470, 263, 0, 0, 0, 0, 1538, 0, 0, 2210],
    [686, 59, 0, 0, 0, 0, 125, 511, 89, 4554, 0, 0, 3976],
]


def simplex_project(p):
    result = np.empty_like(p)
    for i, row in enumerate(p):
        sorted_row = np.sort(row)[::-1]
        threshold = (np.cumsum(sorted_row) - 1) / np.arange(1, len(row) + 1)
        active = np.nonzero(sorted_row > threshold)[0][-1]
        result[i] = np.maximum(row - threshold[active], 0)
    return result


def projected_refine(problem, p, iterations, best, temperature=0):
    """Nonconvex exploratory descent; not a global-minimum certificate."""
    previous_p = previous_g = None
    step = .01
    for iteration in range(iterations):
        out = problem.evaluate_probabilities(p, temperature)
        value, gap, grad = out[0], out[1], out[-1]
        if gap < best[0]:
            best = gap, p.copy()
        if previous_p is not None:
            delta_p, delta_g = p - previous_p, grad - previous_g
            curvature = np.sum(delta_p * delta_g)
            if curvature > 1e-24:
                step = np.clip(np.sum(delta_p * delta_p) / curvature, 1e-5, 10)
        previous_p, previous_g = p.copy(), grad.copy()
        for backtrack in range(30):
            trial = simplex_project(p - step * grad)
            predicted = np.sum(grad * (trial - p))
            candidate = problem.evaluate_probabilities(trial, temperature, False)
            if candidate[0] <= value + .0001 * predicted + 1e-18:
                p = trial
                break
            step *= .5
        if iteration % 1000 == 0:
            print("projected", iteration, "loss", value, "gap", gap, "step", step, flush=True)
    return best, p


def rounded_counts(p, denominator):
    p = p / p.sum(axis=1)[:, None]
    scaled = p * denominator
    counts = np.floor(scaled).astype(np.int64)
    for i in range(4):
        residual = denominator - int(counts[i].sum())
        order = np.argsort(-(scaled[i] - counts[i]))
        counts[i, order[:residual]] += 1
    return counts.tolist()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dates", type=int, default=12)
    parser.add_argument("--steps", type=int, default=1000)
    parser.add_argument("--seeds", type=int, default=2)
    parser.add_argument("--denominator", type=int, default=10 ** 9)
    parser.add_argument("--projected", action="store_true")
    parser.add_argument("--certificate-only", action="store_true")
    parser.add_argument("--linear", action="store_true")
    args = parser.parse_args()
    if args.certificate_only:
        result = exact_certificate(CERTIFICATE_TWELVE, 10000)
        for key, value in result.items():
            print(key, value)
        assert max(result["gaps"]) < Fraction(1, 150)
        print("PASS: complete terminal regret < 1/150")
        return
    problem = (LinearClockProblem if args.linear else ClockProblem)(args.dates)
    rng = np.random.default_rng(90473)
    best = (float("inf"), None)
    start = time.time()
    for seed in range(args.seeds):
        if seed == 0 and args.dates >= 8:
            initial = SEED_TWELVE if args.dates >= 12 else SEED_EIGHT
            width = initial.shape[1] - 1
            p = np.full((4, args.dates + 1), .0005)
            p[:, :width] += initial[:, :width]
            p[:, -1] += initial[:, -1]
            p /= p.sum(axis=1)[:, None]
            logits = np.log(p)
        else:
            logits = rng.normal(0, 1, (4, args.dates + 1))
            logits[:, -1] += 1
        if args.projected:
            p = np.exp(logits - logits.max(axis=1)[:, None])
            p /= p.sum(axis=1)[:, None]
            for temperature in [.002, .0005, .0001, .00002]:
                best, p = projected_refine(problem, p, args.steps, best, temperature)
            continue
        for temperature in [.06, .02, .008, .003, .001, .0003, .0001]:
            mom = np.zeros_like(logits)
            second = np.zeros_like(logits)
            for iteration in range(1, args.steps + 1):
                output = problem.evaluate(logits, temperature)
                grad = output[-1]
                mom = .9 * mom + .1 * grad
                second = .999 * second + .001 * grad * grad
                learning_rate = min(.035, .01 * np.sqrt(temperature / .01))
                logits -= learning_rate * (mom / (1 - .9 ** iteration)) / (np.sqrt(second / (1 - .999 ** iteration)) + 1e-10)
                if output[1] < best[0]:
                    best = output[1], output[2].copy()
            output = problem.evaluate(logits, temperature, False)
            print("seed", seed, "temperature", temperature, "gap", output[1], "values", output[3], "caps", output[4], flush=True)
    counts = rounded_counts(best[1], args.denominator)
    print("BEST", best[0], "seconds", time.time() - start)
    print("COUNTS", counts)
    result = exact_certificate(counts, args.denominator)
    for key, value in result.items():
        print(key, value)
    print("EXACT_MAX_GAP", max(result["gaps"]), float(max(result["gaps"])))


if __name__ == "__main__":
    main()
