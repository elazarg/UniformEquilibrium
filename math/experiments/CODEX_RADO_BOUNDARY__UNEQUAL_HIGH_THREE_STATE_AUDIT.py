"""Independent exact value/derivative/finite-law checks of one frozen cycle.

This is a review regression, not a substitute for the interval existence
proof. It writes nothing and never uses another agent's feedback.
"""

from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import importlib.util
import sys

sys.dont_write_bytecode = True
MATH = Path(__file__).resolve().parents[1]
path = MATH / "experiments/CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_THREE_STATE_CERTIFICATE.py"
spec = importlib.util.spec_from_file_location("frozen_cycle_certificate", path)
candidate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(candidate)
sys.path.insert(0, str(MATH.parent / "Experiments/fin4_exact_search"))
from fin4_exact_search.engine import RewardTable, terminal_semantics
from fin4_exact_search.direct_oracle import hazards_to_law

POSITIONS = ((0, 0), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2),
             (2, 0), (2, 1), (2, 3))
ROWS = {
    0: (0, 0, 0, 0), 1: (1, 4, 0, 0), 2: (4, 1, 0, 0),
    3: (2, 2, 1, 1), 4: (0, 0, 1, 4), 5: (Q(8, 5), 1, 1, 0),
    6: (0, 1, Q(8, 5), 1), 7: (1, 0, 0, 0), 8: (0, 0, 4, 1),
    9: (1, 0, 1, 2), 10: (1, 2, 0, 1), 11: (0, 1, 0, 0),
    12: (1, 1, 2, 2), 13: (0, 0, 0, 1), 14: (0, 0, 1, 0),
    15: (-1, -1, -1, -1),
}


def prod(xs):
    answer = Q(1)
    for x in xs:
        answer *= x
    return answer


def phase_rows(x):
    rows = [[Q(0)] * 4 for _ in range(3)]
    for value, (phase, owner) in zip(x, POSITIONS):
        rows[phase][owner] = value
    return rows


def stage(row, rewards):
    reward = [Q(0)] * 4
    for actions in product((0, 1), repeat=4):
        weight = prod(row[i] if actions[i] else 1-row[i] for i in range(4))
        mask = sum(actions[i] * 2**i for i in range(4))
        reward = [v + weight*r for v, r in zip(reward, rewards[mask])]
    return reward, prod(1-p for p in row)


def reconstruct(x, rewards=ROWS):
    rows = phase_rows(x)
    data = [stage(row, rewards) for row in rows]
    den = 1-prod(c for _, c in data)
    numerators = []
    for phase in range(3):
        accumulated = [Q(0)] * 4
        # Compose the actual one-stage affine laws in reverse chronology.
        for offset in (2, 1, 0):
            gains, continuation = data[(phase+offset) % 3]
            accumulated = [g + continuation*v for g, v in zip(gains, accumulated)]
        numerators.append(accumulated)
    endpoints = []
    cleared = []
    for phase, row in enumerate(rows):
        qr, hr, dr = [], [], []
        for owner in range(4):
            quit_row = list(row); quit_row[owner] = Q(1)
            wait_row = list(row); wait_row[owner] = Q(0)
            quit_value = stage(quit_row, rewards)[0][owner]
            wait_value, wait_survival = stage(wait_row, rewards)
            qr.append(quit_value); hr.append(wait_value[owner]); dr.append(wait_survival)
        endpoints.append((qr, hr, dr))
        cleared.append([den*(qr[i]-hr[i])-dr[i]*numerators[(phase+1) % 3][i]
                        for i in range(4)])
    return cleared, den, numerators, endpoints, data


def main():
    assert candidate.ROWS == ROWS and candidate.ACTIVE == POSITIONS
    center = candidate.CENTER
    points = [center, (Q(0),)*9, (Q(1),)*9, (Q(1, 5),)*9,
              tuple(Q(i+1, 12) for i in range(9)),
              tuple(Q(i % 2) for i in range(9))]
    for point in points:
        f, den, w, _, _ = reconstruct(point)
        _, author_f, author_den, author_w, _ = candidate.evaluate(
            [candidate.Ival(x) for x in point])
        assert author_den.value.to_fraction() == den
        for t in range(3):
            for i in range(4):
                assert author_f[t][i].value.to_fraction() == f[t][i]
                assert author_w[t][i].value.to_fraction() == w[t][i]

    # Each cleared F is degree at most two in each individual hazard:
    # D,W,Q,H,d are separately multiaffine. Central differences are exact.
    author_active = candidate.evaluate([candidate.Ival(x) for x in center])[0]
    h = Q(1, 10**6)
    for j in range(9):
        left = list(center); right = list(center)
        left[j] -= h; right[j] += h
        fl = reconstruct(left)[0]; fr = reconstruct(right)[0]
        for k, (t, i) in enumerate(POSITIONS):
            exact_derivative = (fr[t][i]-fl[t][i])/(2*h)
            assert exact_derivative == author_active[k].derivative[j].to_fraction()

    base_f, den, w, endpoints, data = reconstruct(center)
    for quiet_phase, owner in ((0, 1), (1, 3), (2, 2)):
        changed = dict(ROWS)
        grand = list(changed[15]); grand[owner] += 1; changed[15] = tuple(grand)
        changed_f = reconstruct(center, changed)[0]
        for t in range(3):
            for i in range(4):
                expected = Q(0)
                if (t, i) == (quiet_phase, owner):
                    expected = den*prod(phase_rows(center)[t][j]
                                        for j in range(4) if j != owner)
                assert changed_f[t][i]-base_f[t][i] == expected

    values = [[entry/den for entry in row] for row in w]
    normalized = RewardTable(tuple(tuple(Q(x)/4 for x in ROWS[s])
                                   for s in range(1, 16)))
    for horizon in (2, 3, 5, 8):
        rows = phase_rows(center)
        laws = tuple(hazards_to_law(tuple(rows[t % 3][i] for t in range(horizon)))
                     for i in range(4))
        u, cap, _, _ = terminal_semantics(normalized, laws)
        joint_survival = prod(law.never for law in laws)
        for i in range(4):
            assert 4*u[i] == values[0][i]-joint_survival*values[horizon % 3][i]
            # The rational center is only an approximate root, so this is
            # a small-residual regression, NOT exact finite-cap equality.
            assert abs(4*cap[i]-values[0][i]) < Q(1, 10**10)

    print("PASS: literal table/phase order, 72 endpoint numerators and values")
    print("PASS: all 81 center Jacobian entries by exact central differences")
    print("PASS: all 36 quiet-grand-coordinate mutation comparisons")
    print("PASS: 16 exact finite-censor payoff identities; full finite caps checked")
    print("Center checks do not replace the exact interval root-existence proof.")


if __name__ == "__main__":
    main()
