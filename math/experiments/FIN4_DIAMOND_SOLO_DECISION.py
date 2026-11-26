"""Decide vanishing regret plus collision probability on a signed rational diamond.

Give a JSON object with 4-by-4 matrices "gamma" and "joining" in X,Y,U,V order,
using numbers or fraction strings. Own levels are assumed strictly positive.
A success returns chronological owners and exact mass forms on an eigenvector.
All mass forms in a later period are multiplied by 1/lambda.
"""
import argparse
from fractions import Fraction as Q
from math import gcd
import json
import sys


def matrix(rows):
    if not isinstance(rows, list) or len(rows) != 4:
        raise ValueError("expected a 4-by-4 matrix")
    if any(not isinstance(row, list) or len(row) != 4 for row in rows):
        raise ValueError("expected four entries per row")
    if any(type(x) not in (int, str, Q) for row in rows for x in row):
        raise ValueError("expected integers, decimals or fraction strings")
    return [[Q(x) for x in row] for row in rows]


# A row (c,d) encodes the linear form c*T_U+d*T_V on end-of-period masses.
def combine(left, a, right, b):
    return (a*left[0] + b*right[0], a*left[1] + b*right[1])


def scale(row, a):
    return (a*row[0], a*row[1])


def apply(row, mat):
    return combine(mat[0], row[0], mat[1], row[1])


def sign(x):
    return (x > 0) - (x < 0)


def radical_sign(x, y, discriminant):
    """Sign of x+y*sqrt(discriminant), including exact cancellation."""
    if not x or not y or sign(x) == sign(y):
        return sign(x) or sign(y)
    return sign(x) * sign(x*x - y*y*discriminant)


def check_word(word, coefficients, score, alpha, beta, gamma, joining):
    """Return (feasible witness, realizes strict branch itinerary)."""
    product = [(Q(1), Q(0)), (Q(0), Q(1))]
    future = [None] * len(word)
    leaf = [None] * len(word)
    for j in reversed(range(len(word))):
        m = word[j]
        future[j] = apply(score, product)
        leaf[j] = apply(coefficients[m], product)
        product[m] = combine(product[m], 1, leaf[j], 1)

    (a, b), (c, d) = product
    if len(set(word)) == 1:
        m = word[0]
        lam = str(product[m][m])
        ray = ["1", "0"] if m == 0 else ["0", "1"]

        def ray_sign(row):
            return sign(row[m])
    else:
        trace = a + d
        disc = (a-d)**2 + 4*b*c
        lam = f"({trace} + sqrt({disc}))/2"
        ray = [str(b), f"lambda - ({a})"]

        def ray_sign(row):
            x, y = row
            return radical_sign(2*x*b + y*(d-a), y, disc)

    itinerary = all(ray_sign(row) == (1 if m == 0 else -1)
                    for row, m in zip(future, word))
    if not itinerary:
        return None, False

    phases = []
    for j, m in enumerate(word):
        previous = leaf[j-1] if j else apply(leaf[-1], product)
        phases.extend([(0, scale(previous, beta[word[j-1]])),
                       (1, scale(leaf[j], alpha[m])), (2+m, leaf[j])])

    # W_i initially denotes (lambda-1) times the complete payoff tail from
    # phase zero. Multiplication by lambda of a row is row*product on this ray.
    tails = []
    for recipient in range(4):
        total = (0, 0)
        for owner, mass in phases:
            total = combine(total, 1, mass, gamma[recipient][owner])
        tails.append(apply(total, product))
    for owner, mass in phases:
        denominator_mass = combine(apply(mass, product), 1, mass, -1)
        for i in range(4):
            cap_gap = combine(tails[i], 1, denominator_mass, -joining[i][owner])
            if i == owner:
                if ray_sign(tails[i]) != 0:
                    raise ArithmeticError("owner balance failed")
            elif ray_sign(cap_gap) < 0:
                return None, True
            tails[i] = combine(tails[i], 1, denominator_mass, -gamma[i][owner])

    return {"verdict": "exact_solo", "lambda": lam, "end_ray": ray,
            "owners": "".join("XYUV"[o] for o, _ in phases),
            "phase_mass_forms": [[str(x), str(y)] for _, (x,y) in phases]}, True


def window_bound(coefficients, score, margin):
    (au, cu), (cv, av) = coefficients
    theta = -score[1]/score[0]
    low = min(cu, theta/(1+av+cv*theta))
    high = max((1+au)*theta+cu, 1/cv)
    q = max((1+au)*high/((1+au)*high+cu), (1+av)/(1+av+cv*low))
    # Natural log(high/low) <= ceiling(log2(high/low)).
    ratio = high/low
    log_upper = ratio.numerator.bit_length() - ratio.denominator.bit_length() + 1
    bound = abs(score[0]-score[1]) * log_upper / 4
    # q^K <= exp(-K(1-q)). Use log2 again to pick K in one rational step.
    relative = bound/(2*margin)
    bits = max(0, relative.numerator.bit_length() - relative.denominator.bit_length() + 1)
    return int(bits // (1-q)) + 1


def decide(gamma, joining):
    gamma, joining = matrix(gamma), matrix(joining)
    expected = ((0,-1,1,1), (1,0,-1,-1), (-1,1,0,-1), (-1,1,-1,0))
    for i in range(4):
        for j in range(4):
            if sign(gamma[i][j]) != expected[i][j]:
                raise ValueError("singleton matrix outside signed-diamond scope")
            if i != j and not 0 < joining[i][j]/gamma[i][j] < 1:
                raise ValueError("all off-diagonal joining ratios must be interior")
    twins = (2, 3)
    alpha = [gamma[0][m]/(-gamma[0][1]) for m in twins]
    beta = [-gamma[1][m]/gamma[1][0] for m in twins]
    coefficients = [[(gamma[m][1]*alpha[l] + gamma[m][0]*beta[l] + gamma[m][j])
                     / (-gamma[m][0]*beta[m-2]) for l,j in enumerate(twins)] for m in twins]
    minimum = min(map(min, coefficients))
    if minimum <= 0:
        raise ValueError("all four leaf balance coefficients must be positive")
    ratio = gamma[3][0]/gamma[2][0]
    score = [(gamma[3][1]-ratio*gamma[2][1])*alpha[l]
             + gamma[3][j]-ratio*gamma[2][j] for l,j in enumerate(twins)]
    margin = minimum * min(joining[3][2]-gamma[3][2], ratio*(joining[2][3]-gamma[2][3]))

    def check(word):
        return check_word(word, coefficients, score, alpha, beta, gamma, joining)

    for m in (0,1):
        witness, _ = check((m,))
        if witness:
            return witness
    if score[0] < 0 < score[1]:
        maximum = 1 + window_bound(coefficients, score, margin)
        for period in range(2, maximum+1):
            for v in range(1, period):
                if gcd(period, v) != 1:
                    continue
                word = [(j+1)*v//period - j*v//period for j in reversed(range(period))]
                witness, strict_itinerary = check(word)
                if witness:
                    return witness
                # Every strict itinerary on the circle has the same V frequency.
                # At one reduced frequency the mechanical word is unique up to rotation.
                if strict_itinerary:
                    return {"verdict": "positive_regret_plus_collision_floor"}
    return {"verdict": "positive_regret_plus_collision_floor"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", nargs="?", type=argparse.FileType(), default=sys.stdin)
    args = parser.parse_args()
    try:
        with args.table as stream:
            table = json.load(stream, parse_float=str)
        print(json.dumps(decide(table["gamma"], table["joining"])))
    except (KeyError, ValueError, ZeroDivisionError, OSError, TypeError) as exc:
        parser.exit(2, f"{parser.prog}: {exc}\n")
