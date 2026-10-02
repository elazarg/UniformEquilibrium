"""Exact-repair driver for one_round_probe: find + repair + verify in Fractions."""
import json
from fractions import Fraction as Q
import one_round_probe as M

def attempt(seed):
    score, v = M.search(seed, 4000)
    if score > 1e-4:
        return None, f"seed {seed}: float search stalled at {score:.2e}"
    w, _ = M.rationalize_and_check(v)
    O = M.O
    # C6 repair: interior x_O, solve b_O
    if not (0 < w["x"][O] < 1):
        return None, f"seed {seed}: x_O not interior"
    _, _, rho_del, W_V, M_V = M.row_quantities(w["reward"], w["x"])
    if rho_del[O] == 0:
        return None, f"seed {seed}: rho_del[O]=0"
    w["b"][O] = (M_V[O] - W_V[O]) / rho_del[O]
    if abs(w["b"][O]) > 1:
        return None, f"seed {seed}: |b_O|>1 after C6 repair"
    if w["u"][O] > w["b"][O]:
        w["u"][O] = w["b"][O]
    # C3 defines Dstar
    w["Dstar"] = sum(w["b"][i] - w["u"][i] for i in range(4))
    if w["Dstar"] <= Q(1, 1000):
        return None, f"seed {seed}: Dstar too small after repair"
    # C4 closed by shifting U_pi[0]
    U, B = M.two_cut(w["reward"], w["x"], w["u"], w["b"], w["rho_a"],
                     w["rho_a_del"], w["U_pi"], w["W_pi"], w["M_pi"])
    G = sum(B[i] - U[i] for i in range(4)) - w["Dstar"]
    w["U_pi"][0] = w["U_pi"][0] + G
    viols = M.violations(w)
    if viols:
        msg = "; ".join(f"{n}={float(a):.2e}" for n, a in viols[:6])
        return None, f"seed {seed}: residuals {msg}"
    return w, f"seed {seed}: EXACT"

for seed in range(1, 13):
    w, msg = attempt(seed)
    print(msg)
    if w is not None:
        def enc(z):
            return str(z)
        out = {
            "reward": {str(m): [enc(z) for z in w["reward"][m]]
                       for m in M.MASKS},
            "x": [enc(z) for z in w["x"]],
            "u": [enc(z) for z in w["u"]],
            "b": [enc(z) for z in w["b"]],
            "rho_a": enc(w["rho_a"]),
            "rho_a_del": [enc(z) for z in w["rho_a_del"]],
            "U_pi": [enc(z) for z in w["U_pi"]],
            "W_pi": [enc(z) for z in w["W_pi"]],
            "M_pi": [enc(z) for z in w["M_pi"]],
            "Dstar": enc(w["Dstar"]), "lam": enc(w["lam"]),
            "labels": {"j": M.J, "o": M.O, "p": M.P},
        }
        with open("one_round_probe_point.json", "w") as f:
            json.dump(out, f, indent=1)
        print("EXACT FEASIBLE POINT verified in Fractions; "
              "saved to one_round_probe_point.json")
        print(f"  Dstar = {w['Dstar']} = {float(w['Dstar']):.4f}")
        print(f"  lam   = {w['lam']} = {float(w['lam']):.4f}")
        print(f"  x     = {[float(z) for z in w['x']]}")
        print(f"  b-u   = {[float(w['b'][i]-w['u'][i]) for i in range(4)]}")
        break
