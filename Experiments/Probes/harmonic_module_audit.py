"""Probe: module-invariance audit of the processed endpoint-harmonic jet span.

The processed harmonic-jet span is tested as a submodule for the endpoint
transition algebra, asking whether an induced module filtration supplies a
canonical rebasing-stable progress rank. This script performs that audit on
the repository's own landed examples
with exact rational arithmetic.

Translation of the Lean objects (read-only extraction; nothing is imported):

* `StochasticGame.finkStateKernel z` (FinkLimit.lean:427) is the row-stochastic
  matrix `K_z[s][t] = P(s -> t)` obtained by pushing the decoded stationary
  Fink profile through `G.transition`.
* `finkContinuationResidual W z s who` (Fink.lean:612) is
  `(K_z W(.,who))(s) - W(s,who)`, so
  `AnalyticBellmanGerm.endpointHarmonicSubmodule`
  (AnalyticBellmanHierarchy.lean:456), which is the kernel of that residual, is
  exactly `Fix(K_end) (x) R^iota` inside the payoff space `R^(S x iota)`.
  Transition operators therefore act as `M (x) id` on the player index.
* `EndpointHarmonicJetSpan` (AnalyticBellmanHierarchy.lean:473) carries only
  `carrier <= endpointHarmonicSubmodule`, so a "processed span" is an arbitrary
  subspace of that kernel, enlarged one jet at a time by `extend`, and
  `EndpointHarmonicJetSpan.rank` is the plain codimension of the carrier.
* The two concrete generator shapes actually adjoined by the hierarchy are a
  full leading jet `jet.factor 0` and
  `playerNeutralPotentialJetLeadingPayoff who jet
     = finkPlayerPotential who (jet.factor 0)`
  (AnalyticPlayerNeutralHarmonicJet.lean:44, FinkObstruction.lean:210), i.e. the
  elementary tensor `e_who (x) phi` with `phi` a harmonic scalar potential.

Candidate algebras, following E18's generator list (`WildIdeas` §5):

* `endpoint`    : alg(K_end).
* `supported`   : alg(K_a : a a pure joint action in the endpoint support).
* `deviation`   : `supported` plus the endpoint unilateral pure-deviation
                  kernels `finkPureDeviationStateKernel` (FinkLimit.lean:434).
* `germ`        : alg(K_t : t on the analytic germ curve) together with K_end.
* `germ_payoff` : `germ` plus the endpoint stage-payoff multiplication
                  operators `diag(finkStageEU z (.) who)`.

This is a standalone probe, outside the registered Base suite. Run it with
`python Experiments/Probes/harmonic_module_audit.py`.
"""

from __future__ import annotations

import itertools
import json
import math
from fractions import Fraction
from typing import Iterable, Sequence

Matrix = tuple[tuple[Fraction, ...], ...]
Vector = tuple[Fraction, ...]


# --------------------------------------------------------------------------
# exact linear algebra
# --------------------------------------------------------------------------


def matrix(rows: Iterable[Iterable[int | Fraction]]) -> Matrix:
    return tuple(tuple(Fraction(value) for value in row) for row in rows)


def identity(n: int) -> Matrix:
    return matrix([[int(i == j) for j in range(n)] for i in range(n)])


def zero_matrix(n: int) -> Matrix:
    return matrix([[0 for _ in range(n)] for _ in range(n)])


def multiply(left: Matrix, right: Matrix) -> Matrix:
    n = len(left)
    return tuple(
        tuple(
            sum((left[i][k] * right[k][j] for k in range(n)), Fraction(0))
            for j in range(n)
        )
        for i in range(n)
    )


def apply(m: Matrix, v: Vector) -> Vector:
    return tuple(
        sum((m[i][k] * v[k] for k in range(len(v))), Fraction(0))
        for i in range(len(m))
    )


def flatten(value: Matrix) -> Vector:
    return tuple(entry for row in value for entry in row)


def echelon(rows: Sequence[Sequence[Fraction]]) -> list[Vector]:
    """Reduced row echelon basis of the row space, zero rows dropped."""
    work = [list(row) for row in rows]
    if not work:
        return []
    column_count = len(work[0])
    pivot_row = 0
    for column in range(column_count):
        pivot = next(
            (r for r in range(pivot_row, len(work)) if work[r][column] != 0), None
        )
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        scale = work[pivot_row][column]
        work[pivot_row] = [entry / scale for entry in work[pivot_row]]
        for r in range(len(work)):
            if r == pivot_row or work[r][column] == 0:
                continue
            factor = work[r][column]
            work[r] = [a - factor * b for a, b in zip(work[r], work[pivot_row])]
        pivot_row += 1
        if pivot_row == len(work):
            break
    return [tuple(row) for row in work[:pivot_row] if any(e != 0 for e in row)]


def rank(rows: Sequence[Sequence[Fraction]]) -> int:
    return len(echelon(rows))


def in_span(basis: Sequence[Sequence[Fraction]], vector: Sequence[Fraction]) -> bool:
    return rank(list(basis) + [list(vector)]) == rank(basis)


def kernel(rows: Sequence[Sequence[Fraction]], width: int) -> list[Vector]:
    """Basis of `{x : rows . x = 0}`."""
    reduced = echelon(rows)
    pivots = [next(j for j in range(width) if row[j] != 0) for row in reduced]
    free = [j for j in range(width) if j not in pivots]
    basis: list[Vector] = []
    for f in free:
        solution = [Fraction(0)] * width
        solution[f] = Fraction(1)
        for row, pivot in zip(reversed(reduced), reversed(pivots)):
            solution[pivot] = -sum(
                (row[j] * solution[j] for j in range(width) if j != pivot),
                Fraction(0),
            )
        basis.append(tuple(solution))
    return basis


def annihilator(basis: Sequence[Vector], width: int) -> list[Vector]:
    return kernel([list(b) for b in basis], width)


def intersect(left: Sequence[Vector], right: Sequence[Vector], width: int) -> list[Vector]:
    rows = [list(v) for v in annihilator(left, width)]
    rows += [list(v) for v in annihilator(right, width)]
    if not rows:
        return [tuple(row) for row in identity(width)]
    return kernel(rows, width)


def coordinates(basis: Sequence[Vector], vector: Sequence[Fraction]) -> list[Fraction]:
    """Unique coefficients expressing `vector` in the independent `basis`."""
    height = len(basis)
    width = len(vector)
    augmented = [
        [basis[i][j] for i in range(height)] + [vector[j]] for j in range(width)
    ]
    reduced = echelon(augmented)
    result = [Fraction(0)] * height
    for row in reduced:
        pivot = next(j for j in range(height + 1) if row[j] != 0)
        assert pivot < height, "vector is not in the span of the basis"
        result[pivot] = row[height]
    return result


# --------------------------------------------------------------------------
# algebras
# --------------------------------------------------------------------------


def generated_algebra(generators: Sequence[Matrix]) -> list[Matrix]:
    """Basis of the unital algebra generated by `generators` (E18's routine)."""
    n = len(generators[0])
    basis: list[Matrix] = []
    rows: list[Vector] = []

    def add(value: Matrix) -> bool:
        if rank(rows + [list(flatten(value))]) > len(rows):
            basis.append(value)
            rows.append(flatten(value))
            return True
        return False

    add(identity(n))
    for generator in generators:
        add(generator)
    changed = True
    while changed:
        changed = False
        for value in list(basis):
            for generator in generators:
                changed = add(multiply(value, generator)) or changed
    return basis


def commutant_basis(generators: Sequence[Matrix]) -> list[Matrix]:
    n = len(generators[0])
    equations: list[list[Fraction]] = []
    for generator in generators:
        for i in range(n):
            for j in range(n):
                equation = [Fraction(0)] * (n * n)
                for k in range(n):
                    equation[i * n + k] += generator[k][j]
                    equation[k * n + j] -= generator[i][k]
                equations.append(equation)
    return [
        tuple(tuple(v[i * n + j] for j in range(n)) for i in range(n))
        for v in kernel(equations, n * n)
    ]


def jacobson_radical(basis: Sequence[Matrix]) -> list[Matrix]:
    """Dickson's trace-form radical, valid in characteristic zero:
    `rad(A) = {x : tr(L_{xy}) = 0 for all y in A}` with `L` left multiplication
    inside `A`."""
    rows = [flatten(b) for b in basis]
    size = len(basis)
    n = len(basis[0])

    def regular_trace(x: Matrix) -> Fraction:
        return sum(
            (coordinates(rows, flatten(multiply(x, b)))[index]
             for index, b in enumerate(basis)),
            Fraction(0),
        )

    gram = [
        [regular_trace(multiply(basis[i], basis[j])) for j in range(size)]
        for i in range(size)
    ]
    result: list[Matrix] = []
    for combination in kernel(gram, size):
        acc = zero_matrix(n)
        for coefficient, b in zip(combination, basis):
            acc = tuple(
                tuple(acc[i][j] + coefficient * b[i][j] for j in range(n))
                for i in range(n)
            )
        result.append(acc)
    return result


def center(basis: Sequence[Matrix]) -> list[Matrix]:
    """Basis of the centre `Z(A) = {z in A : zb = bz for all b in A}`."""
    n = len(basis[0])
    size = len(basis)
    equations: list[list[Fraction]] = []
    for b in basis:
        for i in range(n):
            for j in range(n):
                equations.append(
                    [
                        sum(
                            (
                                basis[k][i][t] * b[t][j] - b[i][t] * basis[k][t][j]
                                for t in range(n)
                            ),
                            Fraction(0),
                        )
                        for k in range(size)
                    ]
                )
    result: list[Matrix] = []
    for combination in kernel(equations, size):
        acc = zero_matrix(n)
        for coefficient, b in zip(combination, basis):
            acc = tuple(
                tuple(acc[i][j] + coefficient * b[i][j] for j in range(n))
                for i in range(n)
            )
        result.append(acc)
    return result


def characteristic_polynomial(m: Matrix) -> list[Fraction]:
    """Faddeev-LeVerrier coefficients of `det(x I - m)`, constant term first."""
    n = len(m)
    coefficients = [Fraction(1)]
    current = identity(n)
    for k in range(1, n + 1):
        if k > 1:
            current = multiply(m, current)
            current = tuple(
                tuple(
                    current[i][j] + coefficients[-1] * (Fraction(1) if i == j else Fraction(0))
                    for j in range(n)
                )
                for i in range(n)
            )
        product = multiply(m, current)
        trace = sum((product[i][i] for i in range(n)), Fraction(0))
        coefficients.append(-trace / k)
    return list(reversed(coefficients))


def divisors(value: int) -> list[int]:
    return [d for d in range(1, value + 1) if value % d == 0]


def rational_roots(coefficients: Sequence[Fraction]) -> list[Fraction]:
    """Distinct rational roots of a polynomial given constant term first."""
    scale = 1
    for c in coefficients:
        scale = scale * c.denominator // math.gcd(scale, c.denominator)
    integral = [int(c * scale) for c in coefficients]
    while integral and integral[0] == 0:
        integral.pop(0)
    if not integral:
        return [Fraction(0)]
    constant, leading = abs(integral[0]), abs(integral[-1])
    if constant == 0 or leading == 0:
        return [Fraction(0)]
    roots: list[Fraction] = []
    for p in divisors(constant):
        for q in divisors(leading):
            for candidate in (Fraction(p, q), Fraction(-p, q)):
                value = sum(
                    (Fraction(c) * candidate ** k for k, c in enumerate(integral)),
                    Fraction(0),
                )
                if value == 0 and candidate not in roots:
                    roots.append(candidate)
    if len(integral) < len(coefficients) and Fraction(0) not in roots:
        roots.append(Fraction(0))
    return roots


def generalized_eigenspaces(m: Matrix) -> tuple[list[list[Vector]], bool]:
    """Rational generalized eigenspaces of `m` and whether they exhaust the
    ambient space."""
    n = len(m)
    spaces: list[list[Vector]] = []
    total = 0
    for root in rational_roots(characteristic_polynomial(m)):
        shifted = tuple(
            tuple(
                m[i][j] - (root if i == j else Fraction(0)) for j in range(n)
            )
            for i in range(n)
        )
        power = identity(n)
        for _ in range(n):
            power = multiply(shifted, power)
        space = kernel([list(row) for row in power], n)
        if space:
            spaces.append(space)
            total += len(space)
    return spaces, total == n


# --------------------------------------------------------------------------
# payoff space: operators act as M (x) id on the player index
# --------------------------------------------------------------------------


def lift(m: Matrix, players: int) -> Matrix:
    """`(L v)(s, who) = sum_t m[s][t] v(t, who)`, index `(s, who) -> s*players+who`."""
    n = len(m)
    dim = n * players
    rows = []
    for s in range(n):
        for who in range(players):
            row = [Fraction(0)] * dim
            for t in range(n):
                row[t * players + who] = m[s][t]
            rows.append(tuple(row))
    return tuple(rows)


def is_invariant(operators: Sequence[Matrix], basis: Sequence[Vector]) -> bool:
    if not basis:
        return True
    rows = [list(v) for v in basis]
    reference = rank(rows)
    for operator in operators:
        for v in basis:
            if rank(rows + [list(apply(operator, v))]) > reference:
                return False
    return True


def acts_by_scalar(operator: Matrix, basis: Sequence[Vector]) -> bool:
    """Does `operator` restrict to a scalar multiple of the identity on the
    span of `basis`?  This is the vacuity test for the module hypothesis."""
    if not basis:
        return True
    scalar = None
    for v in basis:
        image = apply(operator, v)
        index = next(i for i, entry in enumerate(v) if entry != 0)
        candidate = image[index] / v[index]
        if scalar is None:
            scalar = candidate
        if any(image[i] != scalar * v[i] for i in range(len(v))):
            return False
    return True


def radical_layers(radical: Sequence[Matrix], basis: Sequence[Vector]) -> list[int]:
    """Dimensions of the Loewy layers `rad^k V / rad^(k+1) V`."""
    current = echelon([list(v) for v in basis])
    dims = [len(current)]
    while current:
        images = [list(apply(r, v)) for r in radical for v in current]
        current = echelon(images) if images else []
        dims.append(len(current))
        if len(dims) > 2 and dims[-1] == dims[-2]:
            raise AssertionError("the radical action failed to be nilpotent")
    return [dims[k] - dims[k + 1] for k in range(len(dims) - 1)]


def channel_dimensions(
    algebra: Sequence[Matrix], subspace: Sequence[Vector], players: int
) -> list[int]:
    """Dimensions of the finest decomposition of `subspace` cut out by the
    generalized eigenspaces of the centre of `algebra` -- the block (isotypic)
    channels of E19.  Basis-independent: the centre is intrinsic."""
    if not subspace:
        return []
    width = len(subspace[0])
    blocks = [list(echelon([list(v) for v in subspace]))]
    for z in center(algebra):
        spaces, complete = generalized_eigenspaces(lift(z, players))
        if not complete or len(spaces) < 2:
            continue
        refined: list[list[Vector]] = []
        for block in blocks:
            for space in spaces:
                piece = intersect(block, space, width)
                if piece:
                    refined.append(list(piece))
        blocks = refined
    return sorted(len(block) for block in blocks)


# --------------------------------------------------------------------------
# the landed examples
# --------------------------------------------------------------------------

HALF = Fraction(1, 2)


def swap_kernel() -> Matrix:
    return matrix([[0, 1], [1, 0]])


def absorbing_split(escape: Fraction, first: Fraction) -> Matrix:
    """Three-state kernel: state 0 leaks with probability `escape`, splitting
    `first`/`1-first` between the absorbing states 1 and 2."""
    return matrix(
        [
            [1 - escape, escape * first, escape * (1 - first)],
            [0, 1, 0],
            [0, 0, 1],
        ]
    )


def diagonal(entries: Sequence[Fraction]) -> Matrix:
    n = len(entries)
    return matrix(
        [[entries[i] if i == j else Fraction(0) for j in range(n)] for i in range(n)]
    )


def pure_externality_cycle() -> dict:
    """`PureExternalityCycle.lean`.  Transitions ignore every action and flip
    the state, so every pure-action kernel is the two-cycle.  The prescribed
    profile is `constProfile false`, whose endpoint stage payoffs are
    `stagePayoffOf s who false = (1 if who = s else -1)`."""
    swap = swap_kernel()
    return {
        "name": "pure_externality_cycle",
        "states": 2,
        "players": 2,
        "endpoint": swap,
        "supported": [swap],
        "deviation": [swap],
        "germ": [swap],
        "payoff_diagonals": [
            diagonal([Fraction(1), Fraction(-1)]),
            diagonal([Fraction(-1), Fraction(1)]),
        ],
        "landed_payoff_vector": None,
    }


def big_match() -> dict:
    """`BigMatch.lean`.  States (live, zero, one).  The stationary Fink
    equilibrium at `1 - beta = lam` stops with probability `lam / (1 + lam)`
    and plays Right with probability `1/2`, so the endpoint kernel is the
    identity, the endpoint support is {Continue} x {Left, Right} and the
    maximizer's Stop deviation is the absorbing split."""
    endpoint = absorbing_split(Fraction(0), HALF)
    stop = absorbing_split(Fraction(1), HALF)
    germ = [absorbing_split(Fraction(lam, 1 + lam), HALF) for lam in (1, 2, 3)]
    stage = [Fraction(1, 2), Fraction(0), Fraction(1)]
    return {
        "name": "big_match",
        "states": 3,
        "players": 2,
        "endpoint": endpoint,
        "supported": [endpoint],
        "deviation": [endpoint, stop],
        "germ": [endpoint] + germ,
        "payoff_diagonals": [
            diagonal(stage),
            diagonal([-value for value in stage]),
        ],
        "landed_payoff_vector": None,
    }


def fink_counterexample(name: str) -> dict:
    """`FinkTangentCounterexample.lean` / `FinkSelectionCounterexample.lean`.
    States (live, high, low); player 1 mixes 1/2-1/2 and player 2 plays the rare
    action `Q` with probability `(1 - beta) / beta`, which vanishes at the
    endpoint.  Both files share `weight` and `transition`, so they have the same
    endpoint transition data; only player 2's stage payoff differs, and it is
    zero at the endpoint in both."""
    endpoint = absorbing_split(Fraction(0), HALF)
    rare = absorbing_split(Fraction(1), HALF)
    germ = [absorbing_split(Fraction(1, k), HALF) for k in (2, 3, 4)]
    landed = tuple(
        Fraction(x) for x in (0, 0, 1, 0, -1, 0)
    )  # `value` at (live, high, low) x (player 1, player 2)
    return {
        "name": name,
        "states": 3,
        "players": 2,
        "endpoint": endpoint,
        "supported": [endpoint],
        "deviation": [endpoint, rare],
        "germ": [endpoint] + germ,
        "payoff_diagonals": [
            diagonal([Fraction(0), Fraction(1), Fraction(-1)]),
            zero_matrix(3),
        ],
        "landed_payoff_vector": landed,
    }


ALGEBRA_ORDER = ["endpoint", "supported", "deviation", "germ", "germ_payoff"]


def algebras_of(example: dict) -> dict[str, list[Matrix]]:
    supported = list(example["supported"])
    return {
        "endpoint": generated_algebra([example["endpoint"]]),
        "supported": generated_algebra(supported),
        "deviation": generated_algebra(supported + list(example["deviation"])),
        "germ": generated_algebra(supported + list(example["germ"])),
        "germ_payoff": generated_algebra(
            supported + list(example["germ"]) + list(example["payoff_diagonals"])
        ),
    }


def fixed_space(kernel_matrix: Matrix) -> list[Vector]:
    n = len(kernel_matrix)
    rows = [
        [kernel_matrix[i][j] - (Fraction(1) if i == j else Fraction(0))
         for j in range(n)]
        for i in range(n)
    ]
    return kernel(rows, n)


def harmonic_basis(example: dict) -> list[Vector]:
    """Kernel of `endpointContinuationResidualLinearMap`, computed directly on
    the payoff space rather than assumed to factor."""
    players = example["players"]
    lifted = lift(example["endpoint"], players)
    dim = len(lifted)
    residual = [
        [lifted[i][j] - (Fraction(1) if i == j else Fraction(0)) for j in range(dim)]
        for i in range(dim)
    ]
    return kernel(residual, dim)


def tensor_with_players(states: Sequence[Vector], players: int) -> list[Vector]:
    result = []
    for phi in states:
        for who in range(players):
            vector = [Fraction(0)] * (len(phi) * players)
            for s, value in enumerate(phi):
                vector[s * players + who] = value
            result.append(tuple(vector))
    return result


def small_lines(basis: Sequence[Vector]) -> list[Vector]:
    """Every line spanned by a `{-1, 0, 1}`-combination of a subspace basis."""
    lines: list[Vector] = []
    seen: set[Vector] = set()
    for coefficients in itertools.product((-1, 0, 1), repeat=len(basis)):
        vector = tuple(
            sum(
                (Fraction(c) * b[i] for c, b in zip(coefficients, basis)),
                Fraction(0),
            )
            for i in range(len(basis[0]))
        )
        if all(entry == 0 for entry in vector):
            continue
        lead = next(entry for entry in vector if entry != 0)
        normalized = tuple(entry / lead for entry in vector)
        if normalized in seen:
            continue
        seen.add(normalized)
        lines.append(normalized)
    return lines


def audit(example: dict) -> dict:
    players = example["players"]
    algebras = algebras_of(example)
    harmonic = harmonic_basis(example)
    fixed = fixed_space(example["endpoint"])
    tensor = tensor_with_players(fixed, players)

    # structure claim: endpointHarmonicSubmodule = Fix(K_end) (x) R^iota
    assert len(harmonic) == len(tensor)
    assert all(in_span(harmonic, t) for t in tensor)

    lines = small_lines(harmonic)
    report: dict = {
        "name": example["name"],
        "states": example["states"],
        "players": example["players"],
        "endpoint_fixed_dimension": len(fixed),
        "harmonic_submodule_dimension": len(harmonic),
        "harmonic_equals_fix_tensor_players": True,
        "algebras": {},
    }

    for key in ALGEBRA_ORDER:
        basis = algebras[key]
        lifted = [lift(m, players) for m in basis]
        radical = jacobson_radical(basis)
        lifted_radical = [lift(m, players) for m in radical]
        commutant = commutant_basis(basis)
        lifted_commutant = [lift(m, players) for m in commutant]

        harmonic_invariant = is_invariant(lifted, harmonic)
        invariant_lines = sum(1 for line in lines if is_invariant(lifted, [line]))
        commutant_lines = sum(
            1 for line in lines if is_invariant(lifted_commutant, [line])
        )

        entry: dict = {
            "algebra_dimension": len(basis),
            "radical_dimension": len(radical),
            "semisimple_quotient_dimension": len(basis) - len(radical),
            "commutant_dimension": len(commutant),
            "harmonic_submodule_is_invariant": harmonic_invariant,
            "harmonic_submodule_is_commutant_invariant": is_invariant(
                lifted_commutant, harmonic
            ),
            "processed_lines_tested": len(lines),
            "processed_lines_invariant": invariant_lines,
            "every_processed_span_is_a_submodule": invariant_lines == len(lines),
            "processed_lines_commutant_invariant": commutant_lines,
        }
        if harmonic_invariant:
            entry["acts_by_scalars_on_harmonic_submodule"] = all(
                acts_by_scalar(operator, harmonic) for operator in lifted
            )
            entry["harmonic_loewy_layers"] = radical_layers(
                lifted_radical, harmonic
            )
            entry["harmonic_channel_dimensions"] = channel_dimensions(
                basis, harmonic, players
            )
            entry["module_length_equals_dimension"] = (
                sum(entry["harmonic_loewy_layers"]) == len(harmonic)
                and len(entry["harmonic_loewy_layers"]) == 1
            )

        # the `finkPlayerPotential who phi` generator shape
        coordinate = [
            is_invariant(lifted, [vector])
            for vector in tensor_with_players(fixed, players)
        ]
        entry["coordinate_jet_lines_invariant"] = [
            sum(1 for x in coordinate if x),
            len(coordinate),
        ]
        if example["landed_payoff_vector"] is not None:
            landed = example["landed_payoff_vector"]
            entry["landed_value_vector_is_harmonic"] = in_span(harmonic, landed)
            entry["landed_value_vector_line_invariant"] = is_invariant(
                lifted, [landed]
            )
        report["algebras"][key] = entry
    return report


# --------------------------------------------------------------------------
# the minimal counterexample census
# --------------------------------------------------------------------------


def deterministic_kernel(f: Sequence[int]) -> Matrix:
    n = len(f)
    return matrix([[int(f[i] == j) for j in range(n)] for i in range(n)])


def mixture(left: Matrix, right: Matrix, weight: Fraction) -> Matrix:
    n = len(left)
    return tuple(
        tuple(weight * left[i][j] + (1 - weight) * right[i][j] for j in range(n))
        for i in range(n)
    )


def census(n: int) -> dict:
    """Every one-player game with `n` states, two deterministic actions and an
    endpoint profile mixing both actions 1/2-1/2 at every state: is `Fix(K_end)`
    invariant under the endpoint-supported pure-action kernels?"""
    failures = []
    total = 0
    for f in itertools.product(range(n), repeat=n):
        for g in itertools.product(range(n), repeat=n):
            total += 1
            ka = deterministic_kernel(f)
            kb = deterministic_kernel(g)
            endpoint = mixture(ka, kb, HALF)
            if not is_invariant([ka, kb], fixed_space(endpoint)):
                failures.append((f, g, len(fixed_space(endpoint))))
    return {
        "states": n,
        "games_tested": total,
        "failures": len(failures),
        "smallest_failure": (
            {
                "action_A_targets": list(failures[0][0]),
                "action_B_targets": list(failures[0][1]),
                "endpoint_fixed_dimension": failures[0][2],
            }
            if failures
            else None
        ),
    }


def stochastic_census_two_states() -> dict:
    """A finer two-state sweep with genuinely mixed kernels and unequal mixing
    weights, to rule out that the two-state success is an artefact of
    determinism."""
    grid = [Fraction(0), HALF, Fraction(1)]
    kernels = [
        matrix([[1 - a, a], [1 - b, b]]) for a in grid for b in grid
    ]
    failures = 0
    total = 0
    for ka in kernels:
        for kb in kernels:
            for weight in (Fraction(1, 3), HALF, Fraction(2, 3)):
                total += 1
                endpoint = mixture(ka, kb, weight)
                if not is_invariant([ka, kb], fixed_space(endpoint)):
                    failures += 1
    return {"states": 2, "systems_tested": total, "failures": failures}


# --------------------------------------------------------------------------
# rebasing stability
# --------------------------------------------------------------------------


def duplicate_state(m: Matrix, index: int) -> Matrix:
    """Public-state refinement: split `index` into two copies and halve the
    incoming mass.  The refinement is lumpable back onto `m`."""
    n = len(m)
    order = list(range(n)) + [index]
    return tuple(
        tuple(m[i][j] / 2 if j == index else m[i][j] for j in order)
        for i in order
    )


def restart_presentation(m: Matrix, entry: int) -> Matrix:
    """Stopped-history rebasing: prepend a fresh entry state feeding `entry`."""
    n = len(m)
    rows = [tuple([Fraction(0)] + [Fraction(int(j == entry)) for j in range(n)])]
    rows += [tuple([Fraction(0)] + list(m[i])) for i in range(n)]
    return tuple(rows)


def rebasing_report(
    name: str, endpoint: Matrix, generators: Sequence[Matrix], players: int
) -> dict:
    def summary(k: Matrix, gens: Sequence[Matrix]) -> dict:
        basis = generated_algebra(list(gens))
        radical = jacobson_radical(basis)
        harmonic = tensor_with_players(fixed_space(k), players)
        lifted = [lift(m, players) for m in basis]
        invariant = is_invariant(lifted, harmonic)
        entry = {
            "state_dimension": len(k),
            "harmonic_rank": len(harmonic),
            "algebra_dimension": len(basis),
            "radical_dimension": len(radical),
            "harmonic_submodule_is_invariant": invariant,
            "harmonic_loewy_layers": None,
            "harmonic_channel_dimensions": None,
            "loewy_length": None,
        }
        if invariant:
            layers = radical_layers([lift(m, players) for m in radical], harmonic)
            entry["harmonic_loewy_layers"] = layers
            entry["harmonic_channel_dimensions"] = channel_dimensions(
                basis, harmonic, players
            )
            entry["loewy_length"] = len(layers)
        return entry

    base = summary(endpoint, generators)
    variants = {
        "state_refinement": summary(
            duplicate_state(endpoint, 0),
            [duplicate_state(g, 0) for g in generators],
        ),
        "restart": summary(
            restart_presentation(endpoint, 0),
            [restart_presentation(g, 0) for g in generators],
        ),
        "two_step_shift": summary(
            multiply(endpoint, endpoint),
            [multiply(g, g) for g in generators],
        ),
    }
    return {
        "name": name,
        "base": base,
        "variants": variants,
        "harmonic_rank_stable": {
            key: value["harmonic_rank"] == base["harmonic_rank"]
            for key, value in variants.items()
        },
        "module_structure_survives": {
            key: value["harmonic_submodule_is_invariant"]
            for key, value in variants.items()
        },
        "channel_dimensions_stable": {
            key: value["harmonic_channel_dimensions"]
            == base["harmonic_channel_dimensions"]
            for key, value in variants.items()
        },
        "loewy_length_stable": {
            key: value["loewy_length"] == base["loewy_length"]
            for key, value in variants.items()
        },
    }


# --------------------------------------------------------------------------


def run() -> dict:
    # calibration of the radical routine against E18's archetypes
    cyclic = matrix([[int(j == (i + 1) % 4) for j in range(4)] for i in range(4)])
    nilpotent = matrix([[int(j == i + 1) for j in range(4)] for i in range(4)])
    assert len(jacobson_radical(generated_algebra([cyclic]))) == 0
    assert len(jacobson_radical(generated_algebra([nilpotent]))) == 3
    assert radical_layers(
        jacobson_radical(generated_algebra([nilpotent])),
        [tuple(row) for row in identity(4)],
    ) == [1, 1, 1, 1]

    examples = [
        pure_externality_cycle(),
        big_match(),
        fink_counterexample("fink_tangent_counterexample"),
        fink_counterexample("fink_selection_counterexample"),
    ]
    reports = [audit(example) for example in examples]
    by_name = {report["name"]: report for report in reports}

    for report in reports:
        endpoint_entry = report["algebras"]["endpoint"]
        # (1) alg(K_end) acts on the harmonic submodule through the trivial
        #     character, so every processed span is a submodule vacuously and
        #     the filtration has a single layer of full dimension.
        assert endpoint_entry["acts_by_scalars_on_harmonic_submodule"]
        assert endpoint_entry["harmonic_submodule_is_invariant"]
        assert endpoint_entry["every_processed_span_is_a_submodule"]
        assert endpoint_entry["harmonic_loewy_layers"] == [
            report["harmonic_submodule_dimension"]
        ]
        assert endpoint_entry["harmonic_channel_dimensions"] == [
            report["harmonic_submodule_dimension"]
        ]
        # (2) the endpoint-supported pure-action algebra is no larger than
        #     alg(K_end) in any landed example, so the audit stays vacuous.
        assert (
            report["algebras"]["supported"]["algebra_dimension"]
            == endpoint_entry["algebra_dimension"]
        )
        assert report["algebras"]["supported"][
            "acts_by_scalars_on_harmonic_submodule"
        ]
        # (3) the whole harmonic submodule survives the deviation and germ
        #     algebras in every landed example.
        assert report["algebras"]["deviation"]["harmonic_submodule_is_invariant"]
        assert report["algebras"]["germ"]["harmonic_submodule_is_invariant"]

    # the sharp negative on the absorbing examples: the germ / deviation algebra
    # is a two-dimensional semisimple algebra generated by an idempotent, and
    # most one-dimensional processed spans are not submodules.
    for name in ("big_match", "fink_tangent_counterexample"):
        germ = by_name[name]["algebras"]["germ"]
        assert germ["algebra_dimension"] == 2
        assert germ["radical_dimension"] == 0
        assert germ["algebra_dimension"] == by_name[name]["algebras"]["deviation"][
            "algebra_dimension"
        ]
        assert not germ["every_processed_span_is_a_submodule"]
        assert germ["harmonic_channel_dimensions"] == [2, 4]
        assert germ["harmonic_loewy_layers"] == [6]

    # payoff multiplication destroys even the whole harmonic submodule wherever
    # the endpoint kernel has a proper fixed space.
    cycle = by_name["pure_externality_cycle"]
    assert cycle["endpoint_fixed_dimension"] == 1
    assert cycle["harmonic_submodule_dimension"] == 2
    assert cycle["algebras"]["germ"]["harmonic_submodule_is_invariant"]
    assert cycle["algebras"]["germ"]["every_processed_span_is_a_submodule"]
    assert not cycle["algebras"]["germ_payoff"]["harmonic_submodule_is_invariant"]

    # the commutant is the non-vacuous direction whenever K_end is the identity.
    for name in ("big_match", "fink_tangent_counterexample"):
        endpoint_entry = by_name[name]["algebras"]["endpoint"]
        assert endpoint_entry["commutant_dimension"] == 9
        assert endpoint_entry["processed_lines_commutant_invariant"] == 0

    # the two Fink counterexample games have identical endpoint module data.
    assert (
        by_name["fink_tangent_counterexample"]["algebras"]
        == by_name["fink_selection_counterexample"]["algebras"]
    )

    # robustness: the repository pins the Big Match stop probability
    # `p = (1 - beta) / (2 - beta)` (BigMatchFink.lean:227) but not the
    # minimizer's Right probability `q`.  The endpoint module data does not
    # depend on `q`, because the escape kernel is idempotent for every `q`.
    escape_robustness = []
    for q in (Fraction(1, 3), HALF, Fraction(2, 3)):
        escape = absorbing_split(Fraction(1), q)
        assert multiply(escape, escape) == escape
        basis = generated_algebra([identity(3), escape])
        harmonic = tensor_with_players(
            fixed_space(absorbing_split(Fraction(0), q)), 2
        )
        escape_robustness.append(
            {
                "right_probability": str(q),
                "escape_kernel_is_idempotent": True,
                "algebra_dimension": len(basis),
                "harmonic_channel_dimensions": channel_dimensions(basis, harmonic, 2),
            }
        )
    assert all(
        entry["harmonic_channel_dimensions"] == [2, 4] for entry in escape_robustness
    )

    censuses = [census(2), census(3)]
    fine = stochastic_census_two_states()
    assert censuses[0]["failures"] == 0
    assert fine["failures"] == 0
    assert censuses[1]["failures"] > 0

    rebasing = [
        rebasing_report(
            "absorbing_germ_algebra",
            absorbing_split(Fraction(0), HALF),
            [absorbing_split(HALF, HALF)],
            2,
        ),
        rebasing_report(
            "pure_externality_cycle",
            swap_kernel(),
            [swap_kernel()],
            2,
        ),
    ]
    absorbing, cyclic_rebasing = rebasing
    # A lumpable public-state refinement preserves both the plain harmonic rank
    # and the channel dimensions -- the module data adds nothing there.
    assert absorbing["harmonic_rank_stable"]["state_refinement"]
    assert absorbing["module_structure_survives"]["state_refinement"]
    assert absorbing["channel_dimensions_stable"]["state_refinement"]
    # The decisive rebasing failure: prepending a deterministic public entry
    # step keeps the plain harmonic rank but destroys the module structure --
    # the refined invariant is strictly LESS stable than the existing rank.
    assert absorbing["harmonic_rank_stable"]["restart"]
    assert not absorbing["module_structure_survives"]["restart"]
    # A two-step (shifted) presentation breaks the harmonic rank itself in the
    # cyclic example, and the channel dimensions with it.
    assert not cyclic_rebasing["harmonic_rank_stable"]["two_step_shift"]
    assert not cyclic_rebasing["channel_dimensions_stable"]["two_step_shift"]
    # Wherever the module structure does survive, its dimensions track the
    # plain harmonic rank exactly: no independent information.
    for report in rebasing:
        for key, survives in report["module_structure_survives"].items():
            if survives:
                assert (
                    report["harmonic_rank_stable"][key]
                    == report["channel_dimensions_stable"][key]
                ), "channel dimensions were expected to track the plain rank"

    return {
        "probe": "harmonic_module_audit",
        "status": "passed",
        "examples": reports,
        "supported_action_census": censuses,
        "two_state_stochastic_sweep": fine,
        "escape_split_robustness": escape_robustness,
        "rebasing": rebasing,
        "conclusion": (
            "The processed harmonic-jet span is always a submodule for the "
            "endpoint transition algebra, but only vacuously: the endpoint "
            "harmonic submodule is exactly Fix(K_end) tensor R^players, and "
            "every polynomial in K_end acts on it as the identity, so the "
            "algebra acts through the trivial character, every subspace is a "
            "submodule, the associated graded is a direct sum of trivial "
            "modules, and the module length equals the plain dimension already "
            "used by EndpointHarmonicJetSpan.rank.  Every strict enlargement of "
            "the algebra - one endpoint unilateral deviation kernel, the "
            "analytic germ family, or a stage-payoff multiplier - breaks "
            "submodule-ness for most processed spans, and where invariance "
            "survives the channel dimensions track the plain harmonic rank "
            "exactly under rebasing.  No new canonical progress rank exists in "
            "either direction."
        ),
        "limitation": (
            "Only stationary endpoint kernels and the germ curve are modelled; "
            "higher-order jets, positivity and owner custody are ignored, and "
            "processed spans are represented by the arbitrary subspaces that "
            "the Lean EndpointHarmonicJetSpan type actually permits."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True, default=str))
