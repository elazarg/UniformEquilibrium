"""homotopy_germ_endgame.py -- a numerical Puiseux "endgame" for quitting-game
analytic germs, by homotopy continuation in the discount.

CONTEXT.  `UniformEquilibrium/Quitting/Boundary/Analytic/Germ.lean` proves
(symbolically, in Lean) that every quitting weight admits a real-analytic
vanishing-discount branch of discounted stationary Bellman equilibria: along
the germ, write t for the local parameter, `beta = 1 - t` for the discount
factor, `y_i(t)` for player i's root quit probability (analytic at t = 0,
nonnegative near 0) with leading order `m_i`, leading coefficient `a_i`
(`y_i(t) ~ a_i t^{m_i}`), and `abar = a / sum(a)` for the normalized exit
direction, which the germ machinery proves converges.  Session VI's cross-lane
note (Sec. 86.2) records
an exit-direction LP screen derived from endpoint complementarity: with
`M_{ij} := r_i({j})` (the singleton-quit payoff matrix) and
`rho := lim t^q / sum(y)` a germ-invariant scale ratio (q the ramification
index), feasibility requires `(1+rho) * r_i({i}) <= (M abar)_i` for every i.
FTV passes at `abar` uniform, `rho = 0`; the two-coordinate disjunction
witness of `QuittingDisjunctionCounterexample.lean` sits exactly on the
boundary of that feasible set.

THIS SCRIPT is the numerical, homotopy-continuation counterpart of that
symbolic machinery: the Cauchy/Puiseux endgame's winding number is exactly the
germ's ramification index q.  For three candidate weights it (1) CONTINUATION:
tracks a discounted stationary equilibrium (y(t), W(t)) along a decreasing
sequence t_k = 2^-k by damped Newton per fixed complementarity support
pattern, warm-started from the previous t_k and re-detecting the active
pattern by exhaustive search whenever the warm-started pattern's iterate
leaves [0, 1] or breaks a complementarity sign; (2) ENDGAME: fits leading
orders m_i and coefficients a_i from a log-log regression over the path's
tail, extracts abar and rho, and classifies rho's scale regime; (3) LP SCREEN:
evaluates the Sec 86.2 inequality at the fitted (rho_hat, abar_hat) and
reports the per-coordinate slack.

NONCLAIMS.  This is float arithmetic with least-squares fits: discovery-grade
numerics, not a validated-numerics certificate and not a Lean claim.  It
probes, and does not re-derive, the germ theory already landed symbolically in
`QuittingAnalyticGerm.lean`.  A weight whose path cannot be tracked cleanly (a
pattern switch, a Newton failure) is reported honestly as a finding, not
suppressed.

HARD RULES respected: standard library only, deterministic (no `random`),
single new file, runtime well under two minutes, JSON summary printed to
stdout, `assert`s used only for integrity (the two ground-truth checks the
governing task explicitly calls for, plus internal consistency checks) with
generous tolerances chosen from the theory, not tuned to force a pass.
"""

import itertools
import json
import math

# ---------------------------------------------------------------------------
# 1. Reward tables (weights)
# ---------------------------------------------------------------------------


def _table(n, rows):
    """Complete a reward table dict[frozenset[int], tuple[float, ...]] over
    every nonempty subset of range(n), validating no entry is missing."""
    table = {}
    for r in range(1, n + 1):
        for combo in itertools.combinations(range(n), r):
            key = frozenset(combo)
            if key not in rows:
                raise ValueError(f"missing entry for subset {sorted(key)}")
            values = rows[key]
            if len(values) != n:
                raise ValueError(f"entry for {sorted(key)} has wrong arity")
            table[key] = tuple(float(v) for v in values)
    return table


ETA = 0.1  # the "stated eta" for the Gamma_eta weight; eta=0 is FTV/3 itself.

WEIGHTS = {
    "disjunction_witness_n2": {
        "n": 2,
        "table": _table(
            2,
            {
                frozenset({0}): (1.0, -1.0),
                frozenset({1}): (1.0, -1.0),
                frozenset({0, 1}): (0.0, 1.0),
            },
        ),
        "note": (
            "QuittingDisjunctionCounterexample.lean's weight: "
            "r({1})=(1,-1), r({2})=(1,-1), r({1,2})=(0,1); "
            "false=player0 (index 0), true=player1 (index 1)."
        ),
    },
    "gamma_eta_n3": {
        "n": 3,
        "table": _table(
            3,
            {
                frozenset({0}): (1 / 3, 1, 0),
                frozenset({1}): (0, 1 / 3, 1),
                frozenset({2}): (1, 0, 1 / 3),
                frozenset({0, 1}): ((1 + ETA) / 3, 0, 1 / 3),
                frozenset({0, 2}): (0, 1 / 3, (1 + ETA) / 3),
                frozenset({1, 2}): (1 / 3, (1 + ETA) / 3, 0),
                frozenset({0, 1, 2}): (0, 0, 0),
            },
        ),
        "note": (
            f"Ashkenazi-Golan-Krasikov-Rainer-Solan's Gamma_eta (Fig 1, p.741) "
            f"at eta={ETA}, via Question147's r_i({{i}})=1/3 table "
            "(FiniteCyclesAreRefutedTheCarrierIsAMassPath.md)."
        ),
    },
    "ftv_div3_n3": {
        "n": 3,
        "table": _table(
            3,
            {
                frozenset({0}): (1 / 3, 1, 0),
                frozenset({1}): (0, 1 / 3, 1),
                frozenset({2}): (1, 0, 1 / 3),
                frozenset({0, 1}): (1 / 3, 0, 1 / 3),
                frozenset({0, 2}): (0, 1 / 3, 1 / 3),
                frozenset({1, 2}): (1 / 3, 1 / 3, 0),
                frozenset({0, 1, 2}): (0, 0, 0),
            },
        ),
        "note": (
            "Flesch-Thuijsman-Vrieze (1997) cubic game divided by 3 "
            "= Gamma_eta at eta=0; has the exact period-3 cyclic equilibrium "
            "with values (1/3, 2/3, 1/3); expected exit direction uniform, "
            "rho=0 (Sec 86.2)."
        ),
    },
}

# ---------------------------------------------------------------------------
# 2. Stage-game payoffs (Question147 / QuittingRootSuccessorCertificate
#    vocabulary): Sigma_i = quit payoff, A_i + c_{-i}*W_i = continue payoff.
#    All three are exactly multilinear in each y_j, j != i -- and constant in
#    y_i itself, which is what makes the exact (epsilon-free) analytic
#    Jacobian below possible.
# ---------------------------------------------------------------------------


def _prob_subset(y, others, chosen):
    p = 1.0
    for j in others:
        p *= y[j] if j in chosen else (1.0 - y[j])
    return p


def sigma_i(i, y, table, n):
    """Payoff to player i if forced to quit for sure, others per y."""
    others = [j for j in range(n) if j != i]
    total = 0.0
    for r in range(len(others) + 1):
        for combo in itertools.combinations(others, r):
            chosen = frozenset(combo)
            p = _prob_subset(y, others, chosen)
            total += p * table[frozenset(chosen | {i})][i]
    return total


def A_i(i, y, table, n):
    """Payoff to player i from continuing when some nonempty set of others
    quits (the deleted-continue reward term); excludes the all-continue
    branch, which contributes through c_minus_i * W_i instead."""
    others = [j for j in range(n) if j != i]
    total = 0.0
    for r in range(1, len(others) + 1):
        for combo in itertools.combinations(others, r):
            chosen = frozenset(combo)
            p = _prob_subset(y, others, chosen)
            total += p * table[chosen][i]
    return total


def c_minus_i(i, y, n):
    p = 1.0
    for j in range(n):
        if j != i:
            p *= 1.0 - y[j]
    return p


def gamma_i(i, y, W, table, n):
    return A_i(i, y, table, n) + c_minus_i(i, y, n) * W[i]


# ---------------------------------------------------------------------------
# 3. Support patterns and the per-pattern Newton system.
#
#    pattern[i] in {0, 1, 2} = {continue (y_i=0), quit (y_i=1), interior}.
#    For an interior coordinate i, the discounted indifference condition
#    Sigma_i(y) = Gamma_i(y,W) with W_i = beta*Sigma_i(y) (Bellman value at
#    indifference) reduces to the single scalar equation
#        Sigma_i(y) * (1 - beta*c_{-i}(y)) - A_i(y) = 0,
#    independent of y_i itself.  Interior y_i's are the unknowns; this is an
#    m x m system (m = number of interior coordinates, m <= n <= 3).
# ---------------------------------------------------------------------------


def assemble_y(pattern, x):
    y = []
    xi = 0
    for code in pattern:
        if code == 0:
            y.append(0.0)
        elif code == 1:
            y.append(1.0)
        else:
            y.append(x[xi])
            xi += 1
    return y


def _eval_triple(i, y, table, n):
    return sigma_i(i, y, table, n), A_i(i, y, table, n), c_minus_i(i, y, n)


def residual_and_jacobian(pattern, x, beta, table, n):
    """Exact (epsilon-free) residual and Jacobian, exploiting multilinearity:
    for a multilinear f, df/dy_j = f|_{y_j=1} - f|_{y_j=0}, independent of
    y_j's actual value."""
    y = assemble_y(pattern, x)
    idxs = [k for k, c in enumerate(pattern) if c == 2]
    m = len(idxs)
    F = [0.0] * m
    J = [[0.0] * m for _ in range(m)]
    for row, i in enumerate(idxs):
        s, a, c = _eval_triple(i, y, table, n)
        F[row] = s * (1.0 - beta * c) - a
        for col, j in enumerate(idxs):
            y1 = list(y)
            y1[j] = 1.0
            y0 = list(y)
            y0[j] = 0.0
            s1, a1, c1 = _eval_triple(i, y1, table, n)
            s0, a0, c0 = _eval_triple(i, y0, table, n)
            ds, da, dc = s1 - s0, a1 - a0, c1 - c0
            J[row][col] = ds * (1.0 - beta * c) + s * (-beta * dc) - da
    return F, J


def solve_linear(J, b):
    """Gaussian elimination with partial pivoting, dimension <= 3."""
    m = len(b)
    if m == 0:
        return []
    A = [list(J[k]) + [b[k]] for k in range(m)]
    for col in range(m):
        piv = max(range(col, m), key=lambda r: abs(A[r][col]))
        if abs(A[piv][col]) < 1e-14:
            return None
        A[col], A[piv] = A[piv], A[col]
        pivval = A[col][col]
        for c in range(col, m + 1):
            A[col][c] /= pivval
        for r in range(m):
            if r != col:
                factor = A[r][col]
                if factor != 0.0:
                    for c in range(col, m + 1):
                        A[r][c] -= factor * A[col][c]
    return [A[r][m] for r in range(m)]


def newton_solve(pattern, x0, beta, table, n, tol=1e-11, max_iter=100):
    m = len(x0)
    if m == 0:
        return [], True, 0
    x = list(x0)
    for it in range(max_iter):
        F0, J = residual_and_jacobian(pattern, x, beta, table, n)
        norm = max(abs(v) for v in F0)
        if norm < tol:
            return x, True, it
        delta = solve_linear(J, [-v for v in F0])
        if delta is None:
            return x, False, it
        damping = 1.0
        improved = False
        for _ in range(30):
            xt = [x[j] + damping * delta[j] for j in range(m)]
            xt = [min(max(v, -0.05), 1.05) for v in xt]
            Ft, _ = residual_and_jacobian(pattern, xt, beta, table, n)
            newnorm = max(abs(v) for v in Ft)
            if newnorm < norm or newnorm < tol:
                x = xt
                improved = True
                break
            damping *= 0.5
        if not improved:
            return x, False, it
    F0, _ = residual_and_jacobian(pattern, x, beta, table, n)
    return x, max(abs(v) for v in F0) < 1e-8, max_iter


def compute_W(pattern, y, beta, table, n):
    """W_i = beta*Sigma_i(y) for a quit coordinate; W_i = beta*A_i/(1-beta*c)
    for a continue OR interior coordinate (the two formulas coincide exactly
    at a converged interior solution)."""
    W = [0.0] * n
    for i in range(n):
        if pattern[i] == 1:
            W[i] = beta * sigma_i(i, y, table, n)
        else:
            c = c_minus_i(i, y, n)
            denom = 1.0 - beta * c
            if abs(denom) < 1e-13:
                return None
            W[i] = beta * A_i(i, y, table, n) / denom
    return W


def validate(pattern, y, W, table, n, box_tol=1e-6, margin_tol=1e-6):
    if W is None or any(not math.isfinite(v) for v in W):
        return False, float("inf")
    violation = 0.0
    for i in range(n):
        if y[i] < -box_tol or y[i] > 1 + box_tol:
            violation += abs(min(0.0, y[i])) + abs(max(0.0, y[i] - 1.0))
        diff = sigma_i(i, y, table, n) - gamma_i(i, y, W, table, n)
        if pattern[i] == 1:  # quit: need Sigma_i >= Gamma_i
            violation += max(0.0, -diff)
        elif pattern[i] == 0:  # continue: need Gamma_i >= Sigma_i
            violation += max(0.0, diff)
        else:  # interior: need Sigma_i == Gamma_i
            violation += abs(diff)
    return violation < margin_tol, violation


RESTART_GRIDS = {
    0: [[]],
    1: [[0.5], [0.1], [0.9], [0.25], [0.75]],
    2: [[0.5, 0.5], [0.1, 0.1], [0.9, 0.9], [0.25, 0.75], [0.75, 0.25], [0.1, 0.9], [0.9, 0.1]],
    3: [
        [0.5, 0.5, 0.5], [0.1, 0.1, 0.1], [0.9, 0.9, 0.9],
        [0.25, 0.5, 0.75], [0.75, 0.5, 0.25], [0.1, 0.5, 0.9],
        [0.9, 0.5, 0.1], [0.3, 0.6, 0.2],
    ],
}


def solve_pattern(pattern, beta, table, n, warm_x=None):
    idxs = [i for i, c in enumerate(pattern) if c == 2]
    m = len(idxs)
    x0_list = []
    if warm_x is not None and len(warm_x) == m:
        x0_list.append(list(warm_x))
    x0_list.extend(RESTART_GRIDS[m])
    best = None
    for x0 in x0_list:
        x, _ok_newton, _iters = newton_solve(pattern, x0, beta, table, n)
        y = assemble_y(pattern, x)
        W = compute_W(pattern, y, beta, table, n)
        ok, violation = validate(pattern, y, W, table, n)
        cand = {"pattern": pattern, "x": x, "y": y, "W": W, "ok": ok, "violation": violation}
        if best is None or violation < best["violation"]:
            best = cand
        if ok:
            break
    return best


def pattern_str(pattern):
    return "".join({0: "C", 1: "Q", 2: "I"}[c] for c in pattern)


# ---------------------------------------------------------------------------
# 4. Continuation: track the path t_k = 2^-k, k = 4..24 (beta = 1 - t_k).
# ---------------------------------------------------------------------------


def run_continuation(n, table):
    patterns = list(itertools.product([0, 1, 2], repeat=n))
    ks = list(range(4, 25))
    path = []
    prev_pattern = None
    warm_x_by_pattern = {}
    switches = []
    failures = []
    for k in ks:
        t = 2.0 ** (-k)
        beta = 1.0 - t
        candidates = []
        for pattern in patterns:
            warm = warm_x_by_pattern.get(pattern)
            cand = solve_pattern(pattern, beta, table, n, warm_x=warm)
            candidates.append(cand)
            warm_x_by_pattern[pattern] = cand["x"]
        best_violation = min(c["violation"] for c in candidates)
        tied = [c for c in candidates if c["violation"] <= best_violation + 1e-9]
        chosen = None
        if prev_pattern is not None:
            for c in tied:
                if c["pattern"] == prev_pattern:
                    chosen = c
                    break
        if chosen is None:
            chosen = tied[0]  # deterministic: itertools.product's canonical order
        if not chosen["ok"]:
            failures.append(
                {"k": k, "t": t, "pattern": pattern_str(chosen["pattern"]),
                 "violation": chosen["violation"]}
            )
        if prev_pattern is not None and chosen["pattern"] != prev_pattern:
            switches.append(
                {"k": k, "t": t, "from": pattern_str(prev_pattern),
                 "to": pattern_str(chosen["pattern"])}
            )
        prev_pattern = chosen["pattern"]
        path.append(
            {
                "k": k, "t": t, "beta": beta,
                "pattern": pattern_str(chosen["pattern"]),
                "y": chosen["y"], "W": chosen["W"],
                "valid": chosen["ok"], "violation": chosen["violation"],
            }
        )
    return path, switches, failures


# ---------------------------------------------------------------------------
# 5. Endgame: fit leading orders, exit direction, and the scale ratio rho.
# ---------------------------------------------------------------------------


def least_squares_line(pts):
    nn = len(pts)
    sx = sum(p[0] for p in pts)
    sy = sum(p[1] for p in pts)
    sxx = sum(p[0] * p[0] for p in pts)
    sxy = sum(p[0] * p[1] for p in pts)
    denom = nn * sxx - sx * sx
    slope = 0.0 if abs(denom) < 1e-14 else (nn * sxy - sx * sy) / denom
    intercept = (sy - slope * sx) / nn
    return slope, intercept


def best_rational(x, max_den=6):
    best = None
    for den in range(1, max_den + 1):
        num = round(x * den)
        err = abs(x - num / den)
        if best is None or err < best[2] - 1e-12:
            best = (num, den, err)
    return {"num": best[0], "den": best[1], "err": best[2]}


def compute_q_est(fits, err_tol=0.03):
    dens = [
        f["rational_fit"]["den"]
        for f in fits
        if f["rational_fit"] is not None and f["rational_fit"]["err"] < err_tol
    ]
    q = 1
    for d in dens:
        q = q * d // math.gcd(q, d)
    return q


def fit_endgame(path, n, tail_count=10):
    valid_path = [p for p in path if p["valid"]]
    used_tail = valid_path[-tail_count:] if len(valid_path) >= 4 else path[-tail_count:]
    flagged_insufficient_valid = len(valid_path) < 4

    logt = [math.log(p["t"]) for p in used_tail]
    fits = []
    for i in range(n):
        pts = [(lt, math.log(p["y"][i])) for lt, p in zip(logt, used_tail) if p["y"][i] > 1e-13]
        if len(pts) >= 2:
            slope, intercept = least_squares_line(pts)
            fits.append(
                {
                    "m_i": slope, "a_i": math.exp(intercept),
                    "rational_fit": best_rational(slope),
                    "n_points": len(pts), "identically_zero": False,
                }
            )
        else:
            fits.append(
                {"m_i": None, "a_i": 0.0, "rational_fit": None,
                 "n_points": len(pts), "identically_zero": True}
            )

    q_est = compute_q_est(fits)

    last = used_tail[-1]
    ysum = sum(last["y"])
    a_hat = [yi / ysum for yi in last["y"]] if ysum > 0 else [1.0 / n] * n

    rho_series = [
        (p["t"], (p["t"] ** q_est) / sum(p["y"]) if sum(p["y"]) > 0 else None)
        for p in used_tail
    ]
    pts_rho = [(math.log(t), math.log(r)) for t, r in rho_series if r is not None and r > 0]
    rho_slope = None
    if len(pts_rho) >= 2:
        rho_slope, _ = least_squares_line(pts_rho)
    rho_hat = rho_series[-1][1] if rho_series and rho_series[-1][1] is not None else 0.0

    if rho_slope is None:
        regime = "undetermined"
    elif rho_slope > 0.05:
        regime = "vanishing (rho -> 0)"
    elif rho_slope < -0.05:
        regime = "diverging (rho -> infinity)"
    else:
        regime = "constant (rho -> const)"

    return {
        "tail_points_used": len(used_tail),
        "flagged_insufficient_valid_tail": flagged_insufficient_valid,
        "fits": fits,
        "q_est": q_est,
        "exit_direction_a_hat": a_hat,
        "rho_hat": rho_hat,
        "rho_log_log_slope": rho_slope,
        "regime": regime,
        "rho_series_tail": rho_series,
    }


def lp_screen(table, n, a_hat, rho_hat):
    M = [[table[frozenset({j})][i] for j in range(n)] for i in range(n)]
    Ma = [sum(M[i][j] * a_hat[j] for j in range(n)) for i in range(n)]
    slacks = [Ma[i] - (1.0 + rho_hat) * M[i][i] for i in range(n)]
    return M, Ma, slacks


# ---------------------------------------------------------------------------
# 6. Run all three weights, assemble the JSON summary, print it, then run the
#    two theory-grounded integrity checks (asserts, with generous tolerance).
# ---------------------------------------------------------------------------


def main():
    summary = {"eta": ETA, "t_k": "2^-k, k=4..24 (beta = 1 - t_k)", "weights": {}}

    for name, spec in WEIGHTS.items():
        n, table = spec["n"], spec["table"]
        path, switches, failures = run_continuation(n, table)
        endgame = fit_endgame(path, n)
        M, Ma, slacks = lp_screen(table, n, endgame["exit_direction_a_hat"], endgame["rho_hat"])

        summary["weights"][name] = {
            "n": n,
            "note": spec["note"],
            "singleton_matrix_M": M,
            "path": path,
            "path_diagnostics": {
                "pattern_switches": switches,
                "n_switches": len(switches),
                "convergence_failures": failures,
                "n_failures": len(failures),
            },
            "endgame": endgame,
            "lp_screen": {
                "M_abar_hat": Ma,
                "slacks": slacks,
                "feasible": all(s > -1e-6 for s in slacks),
            },
        }

    print(json.dumps(summary, indent=2))

    # -- Integrity checks (ground truth from theory; generous tolerance) --

    ftv = summary["weights"]["ftv_div3_n3"]
    ftv_a_hat = ftv["endgame"]["exit_direction_a_hat"]
    ftv_uniform_gap = max(abs(v - 1.0 / 3.0) for v in ftv_a_hat)
    assert ftv_uniform_gap < 0.15, (
        f"FTV/3 exit direction not close to uniform: a_hat={ftv_a_hat}, "
        f"gap={ftv_uniform_gap} (Sec 86.2 predicts abar uniform)"
    )
    ftv_min_slack = min(ftv["lp_screen"]["slacks"])
    assert ftv_min_slack > -1e-3, (
        f"FTV/3 LP screen should pass with slack, got min slack "
        f"{ftv_min_slack}: {ftv['lp_screen']['slacks']}"
    )

    dw = summary["weights"]["disjunction_witness_n2"]
    dw_min_abs_slack = min(abs(s) for s in dw["lp_screen"]["slacks"])
    assert dw_min_abs_slack < 0.15, (
        f"disjunction witness should sit near the LP-screen boundary "
        f"(Sec 86.2), got slacks {dw['lp_screen']['slacks']}"
    )

    print(
        "\n# Integrity checks passed: "
        f"FTV/3 abar uniform (gap={ftv_uniform_gap:.4g}) and LP-feasible "
        f"(min slack={ftv_min_slack:.4g}); "
        f"disjunction witness near boundary (min |slack|={dw_min_abs_slack:.4g})."
    )


if __name__ == "__main__":
    main()
