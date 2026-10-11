"""Diagnostic only: enumerate generic 3-player Boolean faces of ratio tables."""
import itertools
import numpy as np


def face_nash(g, owner):
    js = [j for j in range(4) if j != owner]

    def gain(j, q):
        others = [k for k in js if k != j]
        out = 0.0
        for bits in itertools.product([0, 1], repeat=2):
            mask, mass = 1 << owner, 1.0
            for k, bit in zip(others, bits):
                mass *= q[k] if bit else 1 - q[k]
                if bit:
                    mask |= 1 << k
            out += mass * g[j, mask]
        return out

    out = []

    def append(q):
        vals = [gain(j, q) for j in js]
        for k, j in enumerate(js):
            if not -1e-7 <= q[j] <= 1 + 1e-7:
                return
            if 1e-7 < q[j] < 1 - 1e-7:
                valid = abs(vals[k]) < 1e-6
            else:
                valid = vals[k] <= 1e-6 if q[j] < 0.5 else vals[k] >= -1e-6
            if not valid:
                return
        alpha, gb = np.prod([1 - q[j] for j in js]), 0.0
        for bits in itertools.product([0, 1], repeat=3):
            mask, mass = 0, 1.0
            for j, bit in zip(js, bits):
                mass *= q[j] if bit else 1 - q[j]
                if bit:
                    mask |= 1 << j
            gb += mass * g[owner, mask]
        out.append((float(alpha + gb), q.copy().tolist()))

    for states in itertools.product([0, 1, 2], repeat=3):
        mix = [j for j, state in zip(js, states) if state == 2]
        q = np.zeros(4)
        q[owner] = 1
        for j, state in zip(js, states):
            q[j] = min(state, 1)
        if not mix:
            append(q)
        elif len(mix) == 1:
            if abs(gain(mix[0], q)) < 1e-8:
                return None  # Degenerate continuum: not claimed enumerated.
        elif len(mix) == 2:
            a, b = mix
            q[b] = 0
            lo = gain(a, q)
            q[b] = 1
            hi = gain(a, q)
            if abs(hi - lo) < 1e-8:
                continue
            qb = -lo / (hi - lo)
            q[a] = 0
            lo = gain(b, q)
            q[a] = 1
            hi = gain(b, q)
            if abs(hi - lo) < 1e-8:
                continue
            q[a], q[b] = -lo / (hi - lo), qb
            append(q)
        else:
            x, y, z = mix

            def coeff(j, k, ell):
                q[k] = q[ell] = 0
                a = gain(j, q)
                q[k] = 1
                b = gain(j, q) - a
                q[k], q[ell] = 0, 1
                c = gain(j, q) - a
                q[k] = 1
                d = gain(j, q) - a - b - c
                return a, b, c, d

            a, b, c, d = coeff(x, y, z)
            e, h, k, ell = coeff(y, x, z)
            m, o, p, r = coeff(z, x, y)
            yy, dy = [-a, -c], [b, d]
            xx, dx = [-e, -k], [h, ell]
            mul = np.polynomial.polynomial.polymul
            add = np.polynomial.polynomial.polyadd
            poly = add(add(m * mul(dx, dy), o * mul(xx, dy)),
                       add(p * mul(yy, dx), r * mul(xx, yy)))
            while len(poly) > 1 and abs(poly[-1]) < 1e-8:
                poly = poly[:-1]
            for zz in np.polynomial.polynomial.polyroots(poly):
                if abs(zz.imag) > 1e-7:
                    continue
                zz = zz.real
                if abs(b + d * zz) < 1e-8 or abs(h + ell * zz) < 1e-8:
                    continue
                q[x], q[y], q[z] = ((-e-k*zz)/(h+ell*zz),
                                    (-a-c*zz)/(b+d*zz), zz)
                append(q)
    return out


if __name__ == "__main__":
    rng = np.random.default_rng(23841)
    mate = [1, 0, 3, 2]
    best_score = float("inf")
    for run in range(30000):
        g = np.zeros((4, 16))
        for i in range(4):
            for j in range(4):
                if j != i:
                    g[i, 1 << j] = 3 if j == mate[i] else -1
            for mask in range(1, 16):
                if mask & (1 << i) == 0 and mask.bit_count() >= 2:
                    g[i, mask] = rng.choice([-1, .1, .3, 1, 2, 4, 8, 16])
        all_ne = [face_nash(g, i) for i in range(4)]
        if any(z is None or not z for z in all_ne):
            continue
        scores = [max(value for value, q in z) for z in all_ne]
        score = max(scores)
        if score < best_score:
            best_score = score
        if score < -1e-5:
            print("FOUND", run, "scores", scores, flush=True)
            print("g", g.tolist(), flush=True)
            print("faces", all_ne, flush=True)
            break
    else:
        print("NONE; best diagnostic score", best_score)
