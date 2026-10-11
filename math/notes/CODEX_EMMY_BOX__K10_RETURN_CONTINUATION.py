"""Numerical diagnostic only: selected twisted-return calendar, not a UE proof."""
import argparse
import numpy as np


def mul(a, b):
    return np.array([a[0]*b[0], a[0]*b[1]+a[1]*b[0], a[1]*b[1]])


def prefix(tag, old, K):
    kind, i = tag
    x, y, z, w = [old[(i+j) % 4] for j in range(4)]
    if kind == 'P':
        a = (y-1)/(y+1)
        b = (1-x)/(2-x)
        v = [1-2*b, 1+a, 4*a-3*a*b+(1-a)*(1-b)*z,
             4*b-3*a*b+(1-a)*(1-b)*w]
        hazards = [a, b]
        gaps = [v[2]-(1-a+b-2*a*b), v[3]-(1-2*a-b+a*b)]
    else:
        na, da = [y-1, 2-y], [1+y, -2-y]
        nb, db = [x-1, 5-x], [x-2, 4-x]
        terms = [mul(da, db), mul(na, db), mul(nb, da), mul(na, nb)]
        p = sum(f*t for f, t in zip([1-z, z-5, 1+z, 1-z], terms))
        disc = p[1]*p[1]-4*p[0]*p[2]
        if disc < 0:
            raise ValueError('negative discriminant')
        c = (-p[1]+np.sqrt(disc))/(2*p[2])
        a = (na[0]+na[1]*c)/(da[0]+da[1]*c)
        b = (nb[0]+nb[1]*c)/(db[0]+db[1]*c)
        v = [1-2*b-c+b*c, 1+a-2*c-a*c, 1-a+b-2*a*b,
             4*b-3*a*b+a*c-3*b*c+(K+1)*a*b*c+(1-a)*(1-b)*(1-c)*w]
        inactive = 1-2*a-b+c+a*b-a*c-2*b*c+(K+2)*a*b*c
        hazards, gaps = [a, b, c], [v[3]-inactive]
    out = np.zeros(4)
    for j, value in enumerate(v):
        out[(i+j) % 4] = value
    return out, hazards, gaps


def run(word, u, K, detail=False):
    v = np.array(u)
    diagnostics = []
    for k, tag in enumerate(word):
        v, hazards, gaps = prefix(tag, v, K)
        if detail:
            diagnostics.append((k, tag, hazards, gaps))
    return np.roll(v, -1)-u, diagnostics


def solve(word, u, K):
    def fun(v):
        try:
            return run(word, v, K)[0]
        except (ValueError, FloatingPointError):
            return np.full(4, 1e5)
    u = np.array(u)
    for _ in range(80):
        f = fun(u)
        error = np.max(np.abs(f))
        if error < 1e-10:
            return u
        h = 1e-6
        jac = np.column_stack([(fun(u+h*np.eye(4)[j])-fun(u-h*np.eye(4)[j]))/(2*h)
                               for j in range(4)])
        try:
            increment = np.linalg.solve(jac, -f)
        except np.linalg.LinAlgError:
            break
        fraction = 1.
        while fraction > 1e-7:
            candidate = u+fraction*increment
            if np.max(np.abs(fun(candidate))) < error:
                u = candidate
                break
            fraction /= 2
        else:
            break
    raise RuntimeError(f'root failure {error}')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--step', type=float, default=.02)
    parser.add_argument('--stop', type=float, default=10)
    args = parser.parse_args()
    h = [2,3,2,3,2,3,3,2,3,2,3,2,3]
    word = []
    for k, length in enumerate(h):
        word += [('P', (3+k) % 4)]*length+[('T', (3+k) % 4)]*2
    u = np.array([1.08629059985249, 2.23838565117317, .727718995681476, .855085839403447])
    K = 1.
    changes = []
    last_print = 0
    while K <= args.stop+1e-10:
        for attempt in range(10):
            try:
                u = solve(word, u, K)
            except RuntimeError as err:
                print('FAIL', K, str(err), 'u', u.tolist(), 'changes', changes, flush=True)
                previous = K-args.step
                h = 1e-6
                jac = np.column_stack([
                    (run(word, u+h*np.eye(4)[j], previous)[0]
                     -run(word, u-h*np.eye(4)[j], previous)[0])/(2*h)
                    for j in range(4)])
                print('PREVIOUS_JACOBIAN_SINGULAR_VALUES', previous,
                      np.linalg.svd(jac)[1].tolist(), flush=True)
                finer = previous+args.step/10
                try:
                    refined = solve(word, u, finer)
                    print('FINER_ROOT', finer, refined.tolist(), flush=True)
                except RuntimeError as fine_error:
                    print('FINER_FAIL', finer, str(fine_error), flush=True)
                return
            _, data = run(word, u, K, True)
            bad = [d for d in data if min(d[2]) < -1e-8 or max(d[2]) > 1+1e-8 or min(d[3]) < -1e-8]
            if not bad:
                break
            k, tag, hs, gs = bad[0]
            if tag[0] == 'T' and hs[2] < 0 and min(hs[:2]) >= 0:
                word[k] = ('P', tag[1])
            elif tag[0] == 'P' and gs[0] < 0 and min(hs) >= 0:
                word[k] = ('T', tag[1])
            else:
                print('UNHANDLED', K, bad[:4], 'u', u.tolist(), 'changes', changes, flush=True)
                return
            changes.append((K, k, tag, word[k]))
            print('CHANGE', changes[-1], hs, gs, flush=True)
        else:
            print('CYCLE', K, changes[-10:], flush=True)
            return
        if K-last_print >= .49 or K >= args.stop-1e-10:
            print('LEGAL', K, 'u', u.tolist(), 'minq', min(min(d[2]) for d in data),
                  'mingap', min(min(d[3]) for d in data), 'changes', len(changes), flush=True)
            last_print = K
        K = min(K+args.step, args.stop) if K < args.stop else args.stop+1
    print('WORD', word, flush=True)


if __name__ == '__main__':
    main()
