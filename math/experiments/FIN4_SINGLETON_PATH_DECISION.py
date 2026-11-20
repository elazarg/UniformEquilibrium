"""Decide continuous singleton paths for a hollow rational matrix (requires z3-solver)."""
import argparse
from fractions import Fraction
from itertools import permutations, product
import json
import sys

import z3

from FIN4_SINGLETON_SIGN_CLASSES import det


def read_matrix(stream):
    rows = json.load(stream, parse_float=str)
    if not isinstance(rows, list) or len(rows) != 4:
        raise ValueError("expected a 4-by-4 JSON array")
    matrix = []
    for i, row in enumerate(rows):
        if not isinstance(row, list) or len(row) != 4:
            raise ValueError(f"row {i} must contain four entries")
        if any(type(entry) not in (int, str) for entry in row):
            raise ValueError(f"row {i} has a non-rational entry")
        values = [Fraction(entry) for entry in row]
        if values[i] != 0:
            raise ValueError(f"diagonal entry {i} must be zero")
        matrix.append(values)
    return matrix


def get_model(solver):
    status = solver.check()
    if status == z3.sat:
        return solver.model()
    if status != z3.unsat:
        raise RuntimeError(f"solver returned {status}: {solver.reason_unknown()}")
    return None


def exact_value(model, variable):
    value = model.eval(variable, model_completion=True)
    if z3.is_rational_value(value):
        return str(value.as_fraction())
    if z3.is_algebraic_value(value):
        return {"polynomial_ascending": [c.as_long() for c in value.poly()],
                "real_root_index_1based": value.index()}
    raise RuntimeError(f"unexpected nonalgebraic solver value: {value}")


def decide(matrix):
    gamma = [[z3.RealVal(str(entry)) for entry in row] for row in matrix]
    players = range(4)
    p = z3.Reals("p0 p1 p2 p3")
    solver = z3.SolverFor("QF_LRA")
    solver.add(sum(p) == 1)
    for i in players:
        slack = sum(gamma[i][j] * p[j] for j in players)
        solver.add(p[i] >= 0, slack >= 0, z3.Or(p[i] == 0, slack == 0))
    model = get_model(solver)
    if model is not None:
        return {"verdict": "constant_path", "p": [exact_value(model, v) for v in p]}

    for length in (3, 4):
        for order in permutations(players, length):
            if order[0] != min(order):
                continue
            arcs = zip(order, order[1:] + order[:1])
            if any(not (matrix[j][i] >= 0 >= matrix[i][j] and matrix[j][i] > matrix[i][j])
                   for i, j in arcs):
                continue
            rho = z3.Real("rho")
            d = [z3.Real(f"d{j}") for j in range(length)]
            solver = z3.SolverFor("QF_NRA")
            solver.add(rho > 0, rho < 1, sum(d) == 1 - rho, *[mass > 0 for mass in d])
            # W is (1 - rho) times the actual opening tail of this phase.
            w = [sum(mass * gamma[i][j] for mass, j in zip(d, order)) for i in players]
            for mass, j in zip(d, order):
                solver.add(w[j] == 0, *[value >= 0 for value in w])
                w = [value - (1 - rho) * mass * gamma[i][j] for i, value in enumerate(w)]
            model = get_model(solver)
            if model is not None:
                return {"verdict": "cyclic_path", "order": order, "rho": exact_value(model, rho),
                        "d": [exact_value(model, mass) for mass in d]}
    return {"verdict": "no_continuous_path"}


def minimum_map_degree(matrix):
    """Local degree of x -> min(x, Gx), assuming its only zero is the origin."""
    identity = [[int(i == j) for j in range(4)] for i in range(4)]
    degree = 0
    for selected in product((False, True), repeat=4):
        linear = [matrix[i] if use_g else identity[i] for i, use_g in enumerate(selected)]
        determinant = det(linear)
        if determinant == 0:
            continue
        for i, use_g in enumerate(selected):
            other = identity[i] if use_g else matrix[i]
            difference = [b - a for a, b in zip(linear[i], other)]
            # The target (1,t,t²,t³) for small positive t misses every wall.
            # Cramer's rule gives det(linear) times each comparison coefficient.
            for j in range(4):
                replaced = linear.copy()
                replaced[j] = difference
                numerator = det(replaced)
                if numerator:
                    break
            else:
                raise ArithmeticError("identical selector rows on a hollow matrix")
            if numerator * determinant < 0:
                break
        else:
            degree += 1 if determinant > 0 else -1
    return degree


def decide_behavioral(matrix):
    """Existence of a completion forcing both behaviors, for some positive own level."""
    result = decide(matrix)
    possible = False
    if result["verdict"] == "no_continuous_path":
        degree = minimum_map_degree(matrix)
        result["minimum_map_degree"] = degree
        possible = degree == 1
    result["some_completion_requires_nonstationarity_and_collisions"] = possible
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("matrix", nargs="?", type=argparse.FileType("r"), default=sys.stdin,
                        help="4-by-4 JSON matrix (default: standard input)")
    parser.add_argument("--behavioral", action="store_true",
                        help="test for a completion requiring both behaviors, assuming at least one positive own reward")
    args = parser.parse_args()
    try:
        with args.matrix as stream:
            matrix = read_matrix(stream)
        print(json.dumps(decide_behavioral(matrix) if args.behavioral else decide(matrix)))
    except (ValueError, ZeroDivisionError, OSError, RuntimeError, z3.Z3Exception) as error:
        parser.exit(2, f"{parser.prog}: {error}\n")
