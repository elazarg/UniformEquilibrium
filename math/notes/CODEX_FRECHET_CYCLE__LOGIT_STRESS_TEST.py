"""Numerical discovery only: finite-menu whole-law logit fixed points.

Run from math/: python notes/CODEX_FRECHET_CYCLE__LOGIT_STRESS_TEST.py
The printed residuals and caps are floating-point diagnostics, not proofs.
"""

import argparse
import itertools

import numpy as np


def reward_table(which):
    table = np.zeros((16, 4))
    exact_rows = {
        1: (1, 7, 7), 2: (7, 0, 7), 4: (7, 7, 0),
        3: (6, 8, 7), 5: (9, 7, 5), 6: (7, 5, 8), 7: (7, 6, 6),
    }
    for mask in range(1, 16):
        active = mask & 7
        if which == "exact":
            table[mask, :3] = exact_rows.get(active, (0, 0, 0))
            table[mask, 3] = -1 if mask & 8 and active else (
                1 if not mask & 8 and mask & 6 else 0)
        else:
            table[mask, 0] = 1 + bool(mask & 4) if mask & 1 else 3 * bool(mask & 4)
            for i in (1, 2):
                pred = bool(mask & (1 << (i - 1)))
                table[mask, i] = pred if mask & (1 << i) else 3 * pred - 1
            table[mask, 3] = 0 if mask & 8 else 1
    return table


def pure_values(p, table):
    """All N finite-date values and Never, evaluated without clock truncation."""
    dates = p.shape[1] - 1
    after = np.cumsum(p[:, ::-1], axis=1)[:, ::-1][:, 1:]
    values = np.zeros_like(p)
    for who in range(4):
        opponents = [j for j in range(4) if j != who]
        absorb = np.zeros(dates)
        quit_value = np.zeros(dates)
        for bits in itertools.product((0, 1), repeat=3):
            mass = np.ones(dates)
            mask = 0
            for other, bit in zip(opponents, bits):
                mass *= p[other, :dates] if bit else after[other]
                mask |= bit << other
            absorb += mass * table[mask, who]
            quit_value += mass * table[mask | (1 << who), who]
        prefix = np.r_[0, np.cumsum(absorb)]
        values[who, :dates] = prefix[:-1] + quit_value
        values[who, dates] = prefix[-1]
    return values


def probabilities(log_odds, dates):
    logits = np.c_[np.asarray(log_odds).reshape(4, dates), np.zeros(4)]
    exps = np.exp(logits - np.max(logits, axis=1, keepdims=True))
    return exps / np.sum(exps, axis=1, keepdims=True)


def newton(residual, initial):
    point = initial.copy()
    for step in range(80):
        value = residual(point)
        if np.max(np.abs(value)) < 1e-9:
            return point, True
        jacobian = np.zeros((len(point), len(point)))
        for column in range(len(point)):
            changed = point.copy()
            delta = 1e-5 * max(1, abs(point[column]))
            changed[column] += delta
            jacobian[:, column] = (residual(changed) - value) / delta
        try:
            direction = np.linalg.solve(jacobian, -value)
        except np.linalg.LinAlgError:
            direction = np.linalg.lstsq(jacobian, -value, rcond=None)[0]
        scale = 1.
        old_norm = np.linalg.norm(value)
        for _ in range(30):
            candidate = point + scale * direction
            if np.linalg.norm(residual(candidate)) < old_norm:
                point = candidate
                break
            scale /= 2
        else:
            return point, False
    return point, False


def solve_branch(table, dates, temperatures, seed=None):
    x = np.zeros(4 * dates) if seed is None else seed
    for temperature in temperatures:
        def residual(log_odds):
            p = probabilities(log_odds, dates)
            values = pure_values(p, table)
            return (log_odds.reshape(4, dates) -
                    (values[:, :dates] - values[:, -1, None]) / temperature).ravel()

        solution, success = newton(residual, x)
        err = float(np.max(np.abs(residual(solution))))
        p = probabilities(solution, dates)
        values = pure_values(p, table)
        payoff = np.sum(p * values, axis=1)
        menu_debt = np.max(values, axis=1) - payoff
        late = values[:, -1] + np.array([
            np.prod(np.delete(p[:, -1], who)) * table[1 << who, who]
            for who in range(4)])
        full_debt = np.maximum(np.max(values, axis=1), late) - payoff
        print({"N": dates, "temperature": temperature,
               "residual": err, "success": success,
               "menu": float(max(menu_debt)), "full": float(max(full_debt)),
               "never": p[:, -1].round(8).tolist(),
               "last": p[:, -2].round(8).tolist(),
               "early_mass": np.sum(p[:, :-2], axis=1).round(8).tolist()}, flush=True)
        if err > 1e-5:
            return
        x = solution


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--table", choices=("hilbert", "exact"), default="hilbert")
    parser.add_argument("--dates", nargs="+", type=int, default=[1, 2, 4, 8, 16, 32])
    args = parser.parse_args()
    temperatures = [10, 5, 2, 1, .5, .3, .2, .15, .1, .07, .05, .03, .02, .01]
    for dates in args.dates:
        solve_branch(reward_table(args.table), dates, temperatures)


if __name__ == "__main__":
    main()
