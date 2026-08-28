"""Exact, resumable Fin4 terminal-exploitability search primitives.

Only :class:`fractions.Fraction` arithmetic can accept a certificate.  Search
ordering, seeded candidates, and remote work allocation are untrusted producer
conveniences.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
import gzip
import json
import math
from pathlib import Path
import time
from typing import Any, Iterable, Iterator, Mapping, Optional, Sequence


PLAYERS = tuple(range(4))
COALITIONS = tuple(range(1, 16))
PROFILE_KIND = "fin4-rational-finite-clock-profile-v1"
LOWER_KIND = "fin4-escape-aware-single-shell-lower-flat-v2"
CHECKPOINT_KIND = "fin4-exact-scale-checkpoint-v2"
REGION_KIND = "fin4-exact-search-region-v1"


def Q(value: Any) -> Fraction:
    """Parse an exact rational from the accepted JSON encodings."""
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str):
        return Fraction(value)
    if isinstance(value, (list, tuple)) and len(value) == 2:
        return Fraction(int(value[0]), int(value[1]))
    if isinstance(value, dict) and set(value) == {"num", "den"}:
        return Fraction(int(value["num"]), int(value["den"]))
    raise TypeError(f"cannot parse rational {value!r}")


def qjson(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def canonical_json(data: Any) -> str:
    return json.dumps(data, sort_keys=True, separators=(",", ":"))


def json_hash(data: Any) -> str:
    return sha256(canonical_json(data).encode("utf-8")).hexdigest()


def read_json(path: Path) -> Any:
    if path.suffix == ".gz":
        with gzip.open(path, "rt", encoding="utf-8") as stream:
            return json.load(stream)
    return json.loads(path.read_text(encoding="utf-8"))


def write_json_atomic(path: Path, data: Any) -> None:
    """Write deterministic JSON through a sibling temporary file.

    Compressed output fixes the gzip timestamp and filename fields as well as
    the JSON encoding, so its byte hash is stable across machines and reruns.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    if path.suffix == ".gz":
        payload = (canonical_json(data) + "\n").encode("utf-8")
        with temporary.open("wb") as raw:
            with gzip.GzipFile(
                filename="", fileobj=raw, mode="wb", mtime=0
            ) as stream:
                stream.write(payload)
    else:
        temporary.write_text(
            json.dumps(data, sort_keys=True, indent=2) + "\n",
            encoding="utf-8",
        )
    temporary.replace(path)


@dataclass(frozen=True)
class RewardTable:
    """The sixty rational Fin4 reward coordinates."""

    values: tuple[tuple[Fraction, Fraction, Fraction, Fraction], ...]

    def __post_init__(self) -> None:
        if len(self.values) != 15:
            raise ValueError("a Fin4 table needs exactly 15 nonempty coalitions")
        for row in self.values:
            if len(row) != 4:
                raise ValueError("every coalition needs exactly four payoffs")

    def __call__(self, coalition: int, player: int) -> Fraction:
        if coalition not in COALITIONS or player not in PLAYERS:
            raise IndexError((coalition, player))
        return self.values[coalition - 1][player]

    @property
    def normalized(self) -> bool:
        return all(abs(value) <= 1 for row in self.values for value in row)

    def validate_normalized(self) -> None:
        if not self.normalized:
            raise ValueError("the exact normalized search requires |reward| <= 1")

    def to_json(self) -> dict[str, Any]:
        return {
            "players": 4,
            "rewards": {
                str(mask): [qjson(self(mask, player)) for player in PLAYERS]
                for mask in COALITIONS
            },
        }

    @property
    def digest(self) -> str:
        return json_hash(self.to_json())

    @staticmethod
    def from_json(data: Mapping[str, Any]) -> "RewardTable":
        if "players" in data and int(data["players"]) != 4:
            raise ValueError("only Fin4 tables are accepted")
        raw = data.get("rewards", data)
        rows = []
        for mask in COALITIONS:
            key: Any = str(mask) if str(mask) in raw else mask
            if key not in raw:
                raise ValueError(f"missing coalition {mask}")
            row = tuple(Q(value) for value in raw[key])
            if len(row) != 4:
                raise ValueError(f"coalition {mask} does not have four payoffs")
            rows.append(row)
        table = RewardTable(tuple(rows))  # type: ignore[arg-type]
        table.validate_normalized()
        return table

    @staticmethod
    def zero() -> "RewardTable":
        return RewardTable(tuple((Fraction(0),) * 4 for _ in COALITIONS))


def load_reward_table(path: Path) -> RewardTable:
    return RewardTable.from_json(read_json(path))


Atom = Optional[int]  # None is Never.


@dataclass(frozen=True)
class RationalLaw:
    clock_bound: int
    finite: tuple[Fraction, ...]
    never: Fraction

    def __post_init__(self) -> None:
        if self.clock_bound <= 0:
            raise ValueError("clock_bound must be positive")
        if len(self.finite) != self.clock_bound:
            raise ValueError("wrong finite support length")
        if self.never < 0 or any(value < 0 for value in self.finite):
            raise ValueError("negative stopping-law mass")
        if sum(self.finite, self.never) != 1:
            raise ValueError("stopping-law masses must sum exactly to one")

    @staticmethod
    def pure(clock_bound: int, atom: Atom) -> "RationalLaw":
        if atom is not None and not (0 <= atom < clock_bound):
            raise ValueError("pure finite atom lies outside the clock")
        finite = [Fraction(0)] * clock_bound
        never = Fraction(0)
        if atom is None:
            never = Fraction(1)
        else:
            finite[atom] = Fraction(1)
        return RationalLaw(clock_bound, tuple(finite), never)

    def to_json(self) -> dict[str, Any]:
        return {
            "finite": [qjson(value) for value in self.finite],
            "never": qjson(self.never),
        }

    @staticmethod
    def from_json(clock_bound: int, data: Mapping[str, Any]) -> "RationalLaw":
        return RationalLaw(
            clock_bound,
            tuple(Q(value) for value in data["finite"]),
            Q(data["never"]),
        )


def _survival_arrays(laws: Sequence[RationalLaw]) -> list[list[Fraction]]:
    """Return P(T_i > t), including Never, for each represented finite t."""
    clock = laws[0].clock_bound
    result: list[list[Fraction]] = []
    for law in laws:
        survival = [Fraction(0)] * clock
        tail = law.never
        for time_index in range(clock - 1, -1, -1):
            survival[time_index] = tail
            tail += law.finite[time_index]
        result.append(survival)
    return result


def terminal_semantics(
    reward: RewardTable,
    laws: Sequence[RationalLaw],
) -> tuple[
    tuple[Fraction, ...],
    tuple[Fraction, ...],
    tuple[Fraction, ...],
    Fraction,
]:
    """Evaluate payoff and unrestricted caps in time linear in the clock.

    Pure deviation values use prefix sums of opponent absorption rewards.  The
    menu contains all represented dates, one after-support date, and Never.
    """
    if len(laws) != 4:
        raise ValueError("Fin4 needs four marginal laws")
    clock = laws[0].clock_bound
    if any(law.clock_bound != clock for law in laws):
        raise ValueError("all four laws must use the same clock")
    survival = _survival_arrays(laws)

    payoffs = [Fraction(0) for _ in PLAYERS]
    for time_index in range(clock):
        for mask in COALITIONS:
            probability = Fraction(1)
            for player in PLAYERS:
                if mask & (1 << player):
                    probability *= laws[player].finite[time_index]
                else:
                    probability *= survival[player][time_index]
                if probability == 0:
                    break
            if probability:
                for observer in PLAYERS:
                    payoffs[observer] += probability * reward(mask, observer)

    caps: list[Fraction] = []
    debts: list[Fraction] = []
    for player in PLAYERS:
        opponents = tuple(other for other in PLAYERS if other != player)
        prefix = Fraction(0)
        candidates: list[Fraction] = []
        for time_index in range(clock):
            tie_value = Fraction(0)
            early_value = Fraction(0)
            for submask in range(1 << len(opponents)):
                probability = Fraction(1)
                mask = 1 << player
                for offset, opponent in enumerate(opponents):
                    if submask & (1 << offset):
                        mask |= 1 << opponent
                        probability *= laws[opponent].finite[time_index]
                    else:
                        probability *= survival[opponent][time_index]
                tie_value += probability * reward(mask, player)
                if submask:
                    opponent_mask = mask & ~(1 << player)
                    early_value += probability * reward(opponent_mask, player)
            candidates.append(prefix + tie_value)
            prefix += early_value

        all_opponents_never = math.prod(laws[other].never for other in opponents)
        late_quit = prefix + all_opponents_never * reward(1 << player, player)
        candidates.extend((late_quit, prefix))  # after support, then Never
        cap = max(candidates)
        debt = max(Fraction(0), cap - payoffs[player])
        caps.append(cap)
        debts.append(debt)
    return tuple(payoffs), tuple(caps), tuple(debts), max(debts)


@dataclass(frozen=True)
class ProfileCertificate:
    reward: RewardTable
    clock_bound: int
    laws: tuple[RationalLaw, RationalLaw, RationalLaw, RationalLaw]
    epsilon: Fraction
    payoff: tuple[Fraction, Fraction, Fraction, Fraction]
    cap: tuple[Fraction, Fraction, Fraction, Fraction]
    debt: tuple[Fraction, Fraction, Fraction, Fraction]
    exploitability: Fraction

    @staticmethod
    def build(
        reward: RewardTable,
        laws: Sequence[RationalLaw],
        epsilon: Fraction,
    ) -> "ProfileCertificate":
        payoff, cap, debt, exploitability = terminal_semantics(reward, laws)
        return ProfileCertificate(
            reward,
            laws[0].clock_bound,
            tuple(laws),  # type: ignore[arg-type]
            epsilon,
            payoff,  # type: ignore[arg-type]
            cap,  # type: ignore[arg-type]
            debt,  # type: ignore[arg-type]
            exploitability,
        )

    def verify(self) -> None:
        self.reward.validate_normalized()
        if self.epsilon <= 0:
            raise ValueError("epsilon must be positive")
        if len(self.laws) != 4:
            raise ValueError("four marginal laws are required")
        if any(law.clock_bound != self.clock_bound for law in self.laws):
            raise ValueError("profile clocks disagree")
        calculated = terminal_semantics(self.reward, self.laws)
        stored = (self.payoff, self.cap, self.debt, self.exploitability)
        if calculated != stored:
            raise ValueError("stored terminal semantics do not recompute exactly")
        if self.exploitability >= self.epsilon:
            raise ValueError("profile does not meet its strict exploitability target")

    def to_json(self) -> dict[str, Any]:
        return {
            "kind": PROFILE_KIND,
            "reward": self.reward.to_json(),
            "clock_bound": self.clock_bound,
            "laws": [law.to_json() for law in self.laws],
            "epsilon": qjson(self.epsilon),
            "payoff": [qjson(value) for value in self.payoff],
            "cap": [qjson(value) for value in self.cap],
            "debt": [qjson(value) for value in self.debt],
            "exploitability": qjson(self.exploitability),
        }

    @staticmethod
    def from_json(data: Mapping[str, Any]) -> "ProfileCertificate":
        if data.get("kind") != PROFILE_KIND:
            raise ValueError("wrong profile certificate kind")
        reward = RewardTable.from_json(data["reward"])
        clock = int(data["clock_bound"])
        laws = tuple(RationalLaw.from_json(clock, item) for item in data["laws"])
        if len(laws) != 4:
            raise ValueError("four marginal laws are required")
        return ProfileCertificate(
            reward,
            clock,
            laws,  # type: ignore[arg-type]
            Q(data["epsilon"]),
            tuple(Q(value) for value in data["payoff"]),  # type: ignore[arg-type]
            tuple(Q(value) for value in data["cap"]),  # type: ignore[arg-type]
            tuple(Q(value) for value in data["debt"]),  # type: ignore[arg-type]
            Q(data["exploitability"]),
        )


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("empty interval")

    @staticmethod
    def point(value: Fraction) -> "Interval":
        return Interval(value, value)

    @property
    def width(self) -> Fraction:
        return self.hi - self.lo

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __mul__(self, other: "Interval") -> "Interval":
        values = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(min(values), max(values))

    def maximum(self, other: "Interval") -> "Interval":
        return Interval(max(self.lo, other.lo), max(self.hi, other.hi))

    def to_json(self) -> list[str]:
        return [qjson(self.lo), qjson(self.hi)]

    @staticmethod
    def from_json(data: Sequence[Any]) -> "Interval":
        return Interval(Q(data[0]), Q(data[1]))


class ExprFactory:
    """Hash-consed sparse expression DAG with iterative interval evaluation."""

    def __init__(self) -> None:
        self.nodes: list[tuple[Any, ...]] = []
        self.index: dict[tuple[Any, ...], int] = {}

    def _intern(self, node: tuple[Any, ...]) -> int:
        old = self.index.get(node)
        if old is not None:
            return old
        index = len(self.nodes)
        self.nodes.append(node)
        self.index[node] = index
        return index

    def const(self, value: Fraction | int) -> int:
        return self._intern(("c", Q(value)))

    def var(self, variable: int) -> int:
        return self._intern(("v", variable))

    def neg(self, first: int) -> int:
        node = self.nodes[first]
        if node[0] == "c":
            return self.const(-node[1])
        return self._intern(("n", first))

    def add(self, first: int, second: int) -> int:
        zero = self.const(0)
        if first == zero:
            return second
        if second == zero:
            return first
        left, right = self.nodes[first], self.nodes[second]
        if left[0] == right[0] == "c":
            return self.const(left[1] + right[1])
        if second < first:
            first, second = second, first
        return self._intern(("a", first, second))

    def sub(self, first: int, second: int) -> int:
        return self.add(first, self.neg(second))

    def mul(self, first: int, second: int) -> int:
        zero, one = self.const(0), self.const(1)
        if first == zero or second == zero:
            return zero
        if first == one:
            return second
        if second == one:
            return first
        left, right = self.nodes[first], self.nodes[second]
        if left[0] == right[0] == "c":
            return self.const(left[1] * right[1])
        if second < first:
            first, second = second, first
        return self._intern(("m", first, second))

    def maximum(self, first: int, second: int) -> int:
        if first == second:
            return first
        if second < first:
            first, second = second, first
        return self._intern(("x", first, second))

    def sum(self, terms: Iterable[int]) -> int:
        values = list(terms)
        if not values:
            return self.const(0)
        while len(values) > 1:
            next_values = []
            for offset in range(0, len(values), 2):
                if offset + 1 == len(values):
                    next_values.append(values[offset])
                else:
                    next_values.append(self.add(values[offset], values[offset + 1]))
            values = next_values
        return values[0]

    def prod(self, factors: Iterable[int]) -> int:
        values = list(factors)
        if not values:
            return self.const(1)
        while len(values) > 1:
            next_values = []
            for offset in range(0, len(values), 2):
                if offset + 1 == len(values):
                    next_values.append(values[offset])
                else:
                    next_values.append(self.mul(values[offset], values[offset + 1]))
            values = next_values
        return values[0]

    def max_all(self, terms: Iterable[int]) -> int:
        values = list(terms)
        if not values:
            raise ValueError("maximum needs a nonempty family")
        while len(values) > 1:
            next_values = []
            for offset in range(0, len(values), 2):
                if offset + 1 == len(values):
                    next_values.append(values[offset])
                else:
                    next_values.append(
                        self.maximum(values[offset], values[offset + 1])
                    )
            values = next_values
        return values[0]

    def eval_interval(
        self,
        root: int,
        root_box: Sequence[Interval],
        bounds: Mapping[int, Interval],
        cache: dict[int, Interval],
    ) -> Interval:
        """Evaluate only the root's sparse dependency closure, iteratively."""
        if root in cache:
            return cache[root]
        stack: list[tuple[int, bool]] = [(root, False)]
        while stack:
            index, expanded = stack.pop()
            if index in cache:
                continue
            node = self.nodes[index]
            op = node[0]
            if op == "c":
                cache[index] = Interval.point(node[1])
            elif op == "v":
                variable = node[1]
                cache[index] = bounds.get(variable, root_box[variable])
            elif not expanded:
                stack.append((index, True))
                if op == "n":
                    stack.append((node[1], False))
                else:
                    stack.append((node[1], False))
                    stack.append((node[2], False))
            elif op == "n":
                cache[index] = -cache[node[1]]
            elif op == "a":
                cache[index] = cache[node[1]] + cache[node[2]]
            elif op == "m":
                cache[index] = cache[node[1]] * cache[node[2]]
            elif op == "x":
                cache[index] = cache[node[1]].maximum(cache[node[2]])
            else:
                raise AssertionError(op)
        return cache[root]


@dataclass
class OuterProblem:
    reward: RewardTable
    level: int
    clock_bound: int
    radius: Fraction
    factory: ExprFactory
    variable_names: tuple[str, ...]
    variable_index: dict[str, int]
    root_box: tuple[Interval, ...]
    equalities: tuple[int, ...]
    inequalities: tuple[int, ...]
    objective: int

    def interval(self, variable: int, bounds: Mapping[int, Interval]) -> Interval:
        return bounds.get(variable, self.root_box[variable])


def build_outer_problem(reward: RewardTable, level: int) -> OuterProblem:
    """Build the final-shell system with cap expressions linear in the clock."""
    reward.validate_normalized()
    if level <= 0:
        raise ValueError("level must be positive")
    clock = 8 * level + 1
    radius = Fraction(12, level)
    semantic_bound = Fraction(1) + radius
    factory = ExprFactory()
    names: list[str] = []
    root_intervals: list[Interval] = []
    name_to_index: dict[str, int] = {}

    def variable(name: str, interval: Interval) -> int:
        index = len(names)
        names.append(name)
        root_intervals.append(interval)
        name_to_index[name] = index
        return factory.var(index)

    common_u = [
        variable(f"point.u{player}", Interval(-semantic_bound, semantic_bound))
        for player in PLAYERS
    ]
    common_b = [
        variable(f"point.b{player}", Interval(-semantic_bound, semantic_bound))
        for player in PLAYERS
    ]

    mass: dict[tuple[int, Atom], int] = {}
    for player in PLAYERS:
        for time_index in range(clock + 1):  # clock is the zero auxiliary.
            mass[player, time_index] = variable(
                f"p{player}.t{time_index}", Interval(Fraction(0), Fraction(1))
            )
        mass[player, None] = variable(
            f"p{player}.N", Interval(Fraction(0), Fraction(1))
        )

    equalities: list[int] = []
    for player in PLAYERS:
        atoms: list[Atom] = list(range(clock + 1)) + [None]
        equalities.append(
            factory.sub(factory.sum(mass[player, atom] for atom in atoms),
                        factory.const(1))
        )
        equalities.append(mass[player, clock])

    survival: dict[tuple[int, int], int] = {}
    for player in PLAYERS:
        tail = mass[player, None]
        survival[player, clock] = tail
        for time_index in range(clock - 1, -1, -1):
            tail = factory.add(mass[player, time_index + 1], tail)
            survival[player, time_index] = tail

    joint_probability: dict[tuple[int, int], int] = {}
    for time_index in range(clock):
        for mask in COALITIONS:
            joint_probability[time_index, mask] = factory.prod(
                mass[player, time_index]
                if mask & (1 << player)
                else survival[player, time_index]
                for player in PLAYERS
            )

    payoff_expr: list[int] = []
    for observer in PLAYERS:
        terms = []
        for time_index in range(clock):
            for mask in COALITIONS:
                coefficient = reward(mask, observer)
                if coefficient:
                    terms.append(
                        factory.mul(
                            factory.const(coefficient),
                            joint_probability[time_index, mask],
                        )
                    )
        payoff_expr.append(factory.sum(terms))

    cap_expr: list[int] = []
    for player in PLAYERS:
        opponents = tuple(other for other in PLAYERS if other != player)
        prefix = factory.const(0)
        candidates: list[int] = []
        for time_index in range(clock + 1):
            tie_terms = []
            early_terms = []
            for submask in range(1 << len(opponents)):
                mask = 1 << player
                factors = []
                for offset, opponent in enumerate(opponents):
                    if submask & (1 << offset):
                        mask |= 1 << opponent
                        factors.append(mass[opponent, time_index])
                    else:
                        factors.append(survival[opponent, time_index])
                probability = factory.prod(factors)
                coefficient = reward(mask, player)
                if coefficient:
                    tie_terms.append(factory.mul(factory.const(coefficient), probability))
                if submask:
                    opponent_mask = mask & ~(1 << player)
                    coefficient = reward(opponent_mask, player)
                    if coefficient:
                        early_terms.append(
                            factory.mul(factory.const(coefficient), probability)
                        )
            candidates.append(factory.add(prefix, factory.sum(tie_terms)))
            prefix = factory.add(prefix, factory.sum(early_terms))
        candidates.append(prefix)  # Never.
        cap_expr.append(factory.max_all(candidates))

    inequalities: list[int] = []
    for player in PLAYERS:
        payoff_delta = factory.sub(common_u[player], payoff_expr[player])
        cap_delta = factory.sub(common_b[player], cap_expr[player])
        inequalities.extend(
            (
                factory.sub(factory.const(radius), payoff_delta),
                factory.add(factory.const(radius), payoff_delta),
                factory.sub(factory.const(radius), cap_delta),
                factory.add(factory.const(radius), cap_delta),
            )
        )

    objective = factory.max_all(
        [factory.const(0)]
        + [factory.sub(common_b[player], common_u[player]) for player in PLAYERS]
    )
    return OuterProblem(
        reward,
        level,
        clock,
        radius,
        factory,
        tuple(names),
        name_to_index,
        tuple(root_intervals),
        tuple(equalities),
        tuple(inequalities),
        objective,
    )


PrefixStep = tuple[str, Fraction, bool]  # variable, cut, right side?


def prefix_to_json(prefix: Sequence[PrefixStep]) -> list[dict[str, Any]]:
    return [
        {"variable": variable, "cut": qjson(cut), "right": right}
        for variable, cut, right in prefix
    ]


def prefix_from_json(data: Sequence[Mapping[str, Any]]) -> tuple[PrefixStep, ...]:
    result = []
    for item in data:
        right = item["right"]
        if not isinstance(right, bool):
            raise ValueError("prefix split side must be a JSON Boolean")
        result.append((str(item["variable"]), Q(item["cut"]), right))
    return tuple(result)


def apply_prefix(
    problem: OuterProblem,
    prefix: Sequence[PrefixStep],
) -> dict[int, Interval]:
    bounds: dict[int, Interval] = {}
    for variable_name, cut, right in prefix:
        if variable_name not in problem.variable_index:
            raise ValueError(f"unknown prefix variable {variable_name}")
        variable = problem.variable_index[variable_name]
        interval = bounds.get(variable, problem.root_box[variable])
        if not interval.lo < cut < interval.hi:
            raise ValueError("prefix cut is not strictly inside its current interval")
        bounds[variable] = (
            Interval(cut, interval.hi) if right else Interval(interval.lo, cut)
        )
    return bounds


def _leaf_reason(
    problem: OuterProblem,
    bounds: Mapping[int, Interval],
    gamma: Fraction,
) -> Optional[dict[str, Any]]:
    cache: dict[int, Interval] = {}
    factory = problem.factory
    for index, equality in enumerate(problem.equalities):
        enclosure = factory.eval_interval(
            equality, problem.root_box, bounds, cache
        )
        if enclosure.hi < 0 or 0 < enclosure.lo:
            return {"kind": "leaf", "reason": "eq", "index": index}
    for index, inequality in enumerate(problem.inequalities):
        enclosure = factory.eval_interval(
            inequality, problem.root_box, bounds, cache
        )
        if enclosure.hi < 0:
            return {"kind": "leaf", "reason": "ineq", "index": index}
    objective = factory.eval_interval(
        problem.objective, problem.root_box, bounds, cache
    )
    if objective.lo >= gamma:
        return {"kind": "leaf", "reason": "goal", "index": 0}
    return None


def choose_split_variable(
    problem: OuterProblem,
    bounds: Mapping[int, Interval],
) -> int:
    """Fair normalized-longest-side splitting with stable tie breaking."""
    best: Optional[int] = None
    best_score = Fraction(-1)
    for variable, root in enumerate(problem.root_box):
        if root.width == 0:
            continue
        score = problem.interval(variable, bounds).width / root.width
        if score > best_score:
            best = variable
            best_score = score
    if best is None or best_score <= 0:
        raise RuntimeError("unclassified point box has no splittable variable")
    return best


def _bounds_to_json(bounds: Mapping[int, Interval]) -> dict[str, Any]:
    return {str(index): interval.to_json() for index, interval in bounds.items()}


def _bounds_from_json(data: Mapping[str, Any]) -> dict[int, Interval]:
    return {int(index): Interval.from_json(interval) for index, interval in data.items()}


def _node_to_json(node: Optional[dict[str, Any]]) -> Any:
    if node is None:
        return None
    result = dict(node)
    if result.get("kind") == "split":
        result["cut"] = qjson(Q(result["cut"]))
    return result


def _node_from_json(node: Any) -> Optional[dict[str, Any]]:
    if node is None:
        return None
    result = dict(node)
    if result.get("kind") == "split":
        result["cut"] = Q(result["cut"])
    return result


@dataclass(frozen=True)
class LowerTreeCertificate:
    reward: RewardTable
    level: int
    gamma: Fraction
    prefix: tuple[PrefixStep, ...]
    nodes: tuple[dict[str, Any], ...]

    @property
    def is_global(self) -> bool:
        return not self.prefix

    def verify(self) -> None:
        problem = build_outer_problem(self.reward, self.level)
        if self.gamma <= 0:
            raise ValueError("gamma must be positive")
        if not self.nodes:
            raise ValueError("a lower certificate needs a root node")
        initial = apply_prefix(problem, self.prefix)
        stack: list[tuple[int, dict[int, Interval]]] = [(0, initial)]
        seen: set[int] = set()
        while stack:
            node_index, bounds = stack.pop()
            if not 0 <= node_index < len(self.nodes):
                raise ValueError("tree child index is out of range")
            if node_index in seen:
                raise ValueError("tree contains a cycle or a shared child")
            seen.add(node_index)
            node = self.nodes[node_index]
            kind = node.get("kind")
            if kind == "leaf":
                expected = _leaf_reason(problem, bounds, self.gamma)
                if expected != node:
                    raise ValueError(
                        f"invalid leaf {node_index}: stored {node}, expected {expected}"
                    )
                continue
            if kind != "split":
                raise ValueError(f"unknown tree node kind {kind!r}")
            variable_name = str(node["variable"])
            if variable_name not in problem.variable_index:
                raise ValueError(f"unknown split variable {variable_name}")
            variable = problem.variable_index[variable_name]
            cut = Q(node["cut"])
            interval = bounds.get(variable, problem.root_box[variable])
            if not interval.lo < cut < interval.hi:
                raise ValueError("split cut is not strictly inside its interval")
            left_bounds = dict(bounds)
            right_bounds = dict(bounds)
            left_bounds[variable] = Interval(interval.lo, cut)
            right_bounds[variable] = Interval(cut, interval.hi)
            stack.append((int(node["right"]), right_bounds))
            stack.append((int(node["left"]), left_bounds))
        if len(seen) != len(self.nodes):
            raise ValueError("certificate has unreachable nodes")

    def to_json(self) -> dict[str, Any]:
        return {
            "kind": LOWER_KIND,
            "reward": self.reward.to_json(),
            "level": self.level,
            "gamma": qjson(self.gamma),
            "prefix": prefix_to_json(self.prefix),
            "nodes": [_node_to_json(node) for node in self.nodes],
        }

    @staticmethod
    def from_json(data: Mapping[str, Any]) -> "LowerTreeCertificate":
        if data.get("kind") != LOWER_KIND:
            raise ValueError("wrong lower certificate kind")
        raw_nodes = tuple(_node_from_json(node) for node in data["nodes"])
        if any(node is None for node in raw_nodes):
            raise ValueError("completed certificate contains pending nodes")
        return LowerTreeCertificate(
            RewardTable.from_json(data["reward"]),
            int(data["level"]),
            Q(data["gamma"]),
            prefix_from_json(data.get("prefix", [])),
            raw_nodes,  # type: ignore[arg-type]
        )


class LowerSearch:
    """Depth-first exact branch-and-bound with a compact resumable frontier."""

    def __init__(
        self,
        problem: OuterProblem,
        gamma: Fraction,
        prefix: Sequence[PrefixStep] = (),
    ) -> None:
        if gamma <= 0:
            raise ValueError("gamma must be positive")
        self.problem = problem
        self.gamma = gamma
        self.prefix = tuple(prefix)
        initial = apply_prefix(problem, prefix)
        self.nodes: list[Optional[dict[str, Any]]] = [None]
        self.stack: list[tuple[int, dict[int, Interval]]] = [(0, initial)]
        self.steps = 0

    def step(self) -> Optional[LowerTreeCertificate]:
        if not self.stack:
            return self.certificate()
        node_index, bounds = self.stack.pop()
        leaf = _leaf_reason(self.problem, bounds, self.gamma)
        if leaf is not None:
            self.nodes[node_index] = leaf
        else:
            variable = choose_split_variable(self.problem, bounds)
            interval = bounds.get(variable, self.problem.root_box[variable])
            cut = (interval.lo + interval.hi) / 2
            left_index = len(self.nodes)
            right_index = left_index + 1
            self.nodes.extend((None, None))
            self.nodes[node_index] = {
                "kind": "split",
                "variable": self.problem.variable_names[variable],
                "cut": cut,
                "left": left_index,
                "right": right_index,
            }
            left_bounds = dict(bounds)
            right_bounds = dict(bounds)
            left_bounds[variable] = Interval(interval.lo, cut)
            right_bounds[variable] = Interval(cut, interval.hi)
            self.stack.append((right_index, right_bounds))
            self.stack.append((left_index, left_bounds))
        self.steps += 1
        if not self.stack:
            certificate = self.certificate()
            certificate.verify()
            return certificate
        return None

    def certificate(self) -> LowerTreeCertificate:
        if self.stack or any(node is None for node in self.nodes):
            raise ValueError("lower search is not complete")
        return LowerTreeCertificate(
            self.problem.reward,
            self.problem.level,
            self.gamma,
            self.prefix,
            tuple(self.nodes),  # type: ignore[arg-type]
        )

    def to_state_json(self) -> dict[str, Any]:
        return {
            "gamma": qjson(self.gamma),
            "prefix": prefix_to_json(self.prefix),
            "nodes": [_node_to_json(node) for node in self.nodes],
            "stack": [
                {"node": node, "bounds": _bounds_to_json(bounds)}
                for node, bounds in self.stack
            ],
            "steps": self.steps,
        }

    @staticmethod
    def from_state_json(
        problem: OuterProblem,
        data: Mapping[str, Any],
    ) -> "LowerSearch":
        search = LowerSearch(
            problem,
            Q(data["gamma"]),
            prefix_from_json(data.get("prefix", [])),
        )
        search.nodes = [_node_from_json(node) for node in data["nodes"]]
        search.stack = [
            (int(item["node"]), _bounds_from_json(item["bounds"]))
            for item in data["stack"]
        ]
        search.steps = int(data.get("steps", 0))
        return search


def composition_count(total: int, parts: int) -> int:
    if total < 0 or parts <= 0:
        return 0
    return math.comb(total + parts - 1, parts - 1)


def composition_unrank(total: int, parts: int, rank: int) -> tuple[int, ...]:
    """Lexicographically unrank weak compositions without materializing them."""
    count = composition_count(total, parts)
    if not 0 <= rank < count:
        raise ValueError("composition rank is out of range")
    result = []
    remaining = total
    for position in range(parts - 1):
        rest_parts = parts - position - 1
        for value in range(remaining + 1):
            block = composition_count(remaining - value, rest_parts)
            if rank < block:
                result.append(value)
                remaining -= value
                break
            rank -= block
    result.append(remaining)
    return tuple(result)


def law_from_rank(clock: int, denominator: int, rank: int) -> RationalLaw:
    weights = composition_unrank(denominator, clock + 1, rank)
    return RationalLaw(
        clock,
        tuple(Fraction(value, denominator) for value in weights[:-1]),
        Fraction(weights[-1], denominator),
    )


class UpperSearch:
    """Resumable diagonal enumeration of all rational finite-clock profiles."""

    def __init__(
        self,
        reward: RewardTable,
        target: Fraction,
        diagonal_start: int = 2,
        diagonal_end: Optional[int] = None,
    ) -> None:
        if target <= 0:
            raise ValueError("upper target must be positive")
        if diagonal_start < 2:
            raise ValueError("diagonals start at two")
        if diagonal_end is not None and diagonal_end <= diagonal_start:
            raise ValueError("empty upper diagonal range")
        self.reward = reward
        self.target = target
        self.diagonal = diagonal_start
        self.diagonal_end = diagonal_end
        self.pair_offset = 0
        self.profile_rank = 0
        self.steps = 0
        self.exhausted = False

    def _advance_pair(self) -> None:
        self.pair_offset += 1
        self.profile_rank = 0
        if self.pair_offset >= self.diagonal - 1:
            self.diagonal += 1
            self.pair_offset = 0
            if self.diagonal_end is not None and self.diagonal >= self.diagonal_end:
                self.exhausted = True

    def step(self) -> Optional[ProfileCertificate]:
        if self.exhausted:
            return None
        clock = self.pair_offset + 1
        denominator = self.diagonal - clock
        law_count = composition_count(denominator, clock + 1)
        profile_count = law_count ** 4
        if self.profile_rank >= profile_count:
            self._advance_pair()
            return None

        rank = self.profile_rank
        law_ranks = []
        for _ in PLAYERS:
            law_ranks.append(rank % law_count)
            rank //= law_count
        laws = tuple(
            law_from_rank(clock, denominator, law_rank)
            for law_rank in law_ranks
        )
        self.profile_rank += 1
        self.steps += 1
        certificate = ProfileCertificate.build(self.reward, laws, self.target)
        if certificate.exploitability < self.target:
            certificate.verify()
            return certificate
        return None

    def to_state_json(self) -> dict[str, Any]:
        return {
            "target": qjson(self.target),
            "diagonal": self.diagonal,
            "diagonal_end": self.diagonal_end,
            "pair_offset": self.pair_offset,
            "profile_rank": str(self.profile_rank),
            "steps": self.steps,
            "exhausted": self.exhausted,
        }

    @staticmethod
    def from_state_json(
        reward: RewardTable,
        data: Mapping[str, Any],
    ) -> "UpperSearch":
        target = Q(data["target"])
        diagonal = int(data["diagonal"])
        diagonal_end = (
            None if data.get("diagonal_end") is None else int(data["diagonal_end"])
        )
        exhausted = bool(data.get("exhausted", False))
        if target <= 0 or diagonal < 2:
            raise ValueError("invalid upper checkpoint target or diagonal")
        if diagonal_end is not None and (
            diagonal > diagonal_end or (diagonal == diagonal_end and not exhausted)
        ):
            raise ValueError("upper checkpoint lies outside its diagonal range")
        search = UpperSearch.__new__(UpperSearch)
        search.reward = reward
        search.target = target
        search.diagonal = diagonal
        search.diagonal_end = diagonal_end
        search.pair_offset = int(data["pair_offset"])
        search.profile_rank = int(data["profile_rank"])
        if search.pair_offset < 0 or (
            not exhausted and search.pair_offset >= search.diagonal - 1
        ):
            raise ValueError("invalid upper checkpoint pair offset")
        if search.profile_rank < 0:
            raise ValueError("negative upper checkpoint profile rank")
        search.steps = int(data.get("steps", 0))
        search.exhausted = exhausted
        return search


def required_level(epsilon: Fraction) -> int:
    if epsilon <= 0:
        raise ValueError("epsilon must be positive")
    return math.floor(Fraction(96) / epsilon) + 1


@dataclass(frozen=True)
class ScaleContract:
    epsilon: Fraction
    level: int
    lower_gamma: Fraction
    upper_target: Fraction

    @staticmethod
    def create(epsilon: Fraction) -> "ScaleContract":
        return ScaleContract(
            epsilon,
            required_level(epsilon),
            epsilon / 4,
            3 * epsilon / 4,
        )

    def to_json(self) -> dict[str, Any]:
        return {
            "epsilon": qjson(self.epsilon),
            "level": self.level,
            "lower_gamma": qjson(self.lower_gamma),
            "upper_target": qjson(self.upper_target),
            "outer_error": qjson(Fraction(24, self.level)),
        }


@dataclass(frozen=True)
class SearchResult:
    kind: str
    certificate: LowerTreeCertificate | ProfileCertificate


class ScaleSearch:
    """Actually executable fair per-scale lower/upper search state."""

    def __init__(self, reward: RewardTable, epsilon: Fraction) -> None:
        self.reward = reward
        self.contract = ScaleContract.create(epsilon)
        self.problem = build_outer_problem(reward, self.contract.level)
        self.lower = LowerSearch(self.problem, self.contract.lower_gamma)
        self.upper = UpperSearch(reward, self.contract.upper_target)
        self.turn = 0
        self.steps = 0

    def step(self) -> Optional[SearchResult]:
        if self.turn % 2 == 0:
            certificate = self.lower.step()
            self.turn += 1
            self.steps += 1
            if certificate is not None:
                return SearchResult("lower", certificate)
            return None
        certificate = self.upper.step()
        self.turn += 1
        self.steps += 1
        if certificate is not None:
            return SearchResult("profile", certificate)
        return None

    def run(
        self,
        max_steps: Optional[int] = None,
        max_seconds: Optional[float] = None,
        checkpoint_path: Optional[Path] = None,
        checkpoint_every: int = 100,
    ) -> Optional[SearchResult]:
        started = time.monotonic()
        local_steps = 0
        while max_steps is None or local_steps < max_steps:
            if max_seconds is not None and time.monotonic() - started >= max_seconds:
                break
            result = self.step()
            local_steps += 1
            if checkpoint_path is not None and local_steps % checkpoint_every == 0:
                write_json_atomic(checkpoint_path, self.to_checkpoint_json())
            if result is not None:
                if checkpoint_path is not None:
                    write_json_atomic(checkpoint_path, self.to_checkpoint_json())
                return result
        if checkpoint_path is not None:
            write_json_atomic(checkpoint_path, self.to_checkpoint_json())
        return None

    def to_checkpoint_json(self) -> dict[str, Any]:
        return {
            "kind": CHECKPOINT_KIND,
            "reward": self.reward.to_json(),
            "table_sha256": self.reward.digest,
            "contract": self.contract.to_json(),
            "turn": self.turn,
            "steps": self.steps,
            "lower": self.lower.to_state_json(),
            "upper": self.upper.to_state_json(),
        }

    @staticmethod
    def from_checkpoint_json(data: Mapping[str, Any]) -> "ScaleSearch":
        if data.get("kind") != CHECKPOINT_KIND:
            raise ValueError("wrong checkpoint kind")
        reward = RewardTable.from_json(data["reward"])
        if reward.digest != data["table_sha256"]:
            raise ValueError("checkpoint table hash mismatch")
        epsilon = Q(data["contract"]["epsilon"])
        search = ScaleSearch.__new__(ScaleSearch)
        search.reward = reward
        search.contract = ScaleContract.create(epsilon)
        stored_contract = data["contract"]
        if (
            search.contract.level != int(stored_contract["level"])
            or search.contract.lower_gamma != Q(stored_contract["lower_gamma"])
            or search.contract.upper_target != Q(stored_contract["upper_target"])
            or Fraction(24, search.contract.level) != Q(stored_contract["outer_error"])
        ):
            raise ValueError("checkpoint scale contract mismatch")
        search.problem = build_outer_problem(reward, search.contract.level)
        search.lower = LowerSearch.from_state_json(search.problem, data["lower"])
        search.upper = UpperSearch.from_state_json(reward, data["upper"])
        if search.lower.gamma != search.contract.lower_gamma or search.lower.prefix:
            raise ValueError("checkpoint lower search does not match the scale contract")
        if (
            search.upper.target != search.contract.upper_target
            or search.upper.diagonal_end is not None
        ):
            raise ValueError("checkpoint upper search does not match the scale contract")
        search.turn = int(data["turn"])
        search.steps = int(data.get("steps", 0))
        return search


@dataclass(frozen=True)
class WorkRegion:
    table_sha256: str
    epsilon: Fraction
    level: int
    work_kind: str
    parameters: Mapping[str, Any]

    def payload(self) -> dict[str, Any]:
        return {
            "schema": REGION_KIND,
            "table_sha256": self.table_sha256,
            "epsilon": qjson(self.epsilon),
            "level": self.level,
            "work_kind": self.work_kind,
            "parameters": self.parameters,
        }

    @property
    def descriptor_sha256(self) -> str:
        return json_hash(self.payload())

    @property
    def region_id(self) -> str:
        return f"{self.work_kind}-{self.descriptor_sha256[:20]}"

    def to_json(self) -> dict[str, Any]:
        return {
            **self.payload(),
            "descriptor_sha256": self.descriptor_sha256,
            "region_id": self.region_id,
        }

    def verify_for(self, reward: RewardTable) -> None:
        if self.table_sha256 != reward.digest:
            raise ValueError("region belongs to a different reward table")
        contract = ScaleContract.create(self.epsilon)
        if self.level != contract.level:
            raise ValueError("region level does not match its epsilon")
        if self.work_kind not in {"lower", "upper", "heuristic", "full"}:
            raise ValueError("unknown work region kind")
        canonical = make_region(
            reward, self.epsilon, self.work_kind, self.parameters
        )
        if canonical != self:
            raise ValueError("region parameters are not in canonical form")

    @staticmethod
    def from_json(data: Mapping[str, Any]) -> "WorkRegion":
        if data.get("schema") != REGION_KIND:
            raise ValueError("wrong region schema")
        region = WorkRegion(
            str(data["table_sha256"]),
            Q(data["epsilon"]),
            int(data["level"]),
            str(data["work_kind"]),
            dict(data.get("parameters", {})),
        )
        if data.get("descriptor_sha256") not in (None, region.descriptor_sha256):
            raise ValueError("descriptor_sha256 does not match canonical descriptor")
        if data.get("region_id") not in (None, region.region_id):
            raise ValueError("region_id does not match canonical descriptor")
        return region


def make_region(
    reward: RewardTable,
    epsilon: Fraction,
    work_kind: str,
    parameters: Optional[Mapping[str, Any]] = None,
) -> WorkRegion:
    contract = ScaleContract.create(epsilon)
    normalized = dict(parameters or {})
    if work_kind == "lower":
        normalized["prefix"] = prefix_to_json(
            prefix_from_json(normalized.get("prefix", []))
        )
    elif work_kind == "upper":
        start = int(normalized.get("diagonal_start", 2))
        end = int(normalized["diagonal_end"])
        if start < 2 or end <= start:
            raise ValueError("upper region needs 2 <= start < end")
        normalized = {"diagonal_start": start, "diagonal_end": end}
    elif work_kind == "heuristic":
        start = int(normalized.get("seed_start", 0))
        end = int(normalized["seed_end"])
        algorithm = str(normalized.get("algorithm", "stationary-grid-v1"))
        if start < 0 or end <= start:
            raise ValueError("heuristic region needs 0 <= start < end")
        if algorithm != "stationary-grid-v1":
            raise ValueError("unknown heuristic region algorithm")
        normalized = {
            "algorithm": algorithm,
            "seed_start": start,
            "seed_end": end,
        }
    elif work_kind == "full":
        normalized = {}
    else:
        raise ValueError("unknown region kind")
    return WorkRegion(reward.digest, epsilon, contract.level, work_kind, normalized)


def canonical_lower_partition(
    reward: RewardTable,
    epsilon: Fraction,
    depth: int,
    base_prefix: Sequence[PrefixStep] = (),
) -> list[WorkRegion]:
    """Create a deterministic complete partition by fair geometric splits."""
    if depth < 0:
        raise ValueError("partition depth must be nonnegative")
    contract = ScaleContract.create(epsilon)
    problem = build_outer_problem(reward, contract.level)
    initial_prefix = tuple(base_prefix)
    frontier: list[tuple[tuple[PrefixStep, ...], dict[int, Interval]]] = [
        (initial_prefix, apply_prefix(problem, initial_prefix))
    ]
    for _ in range(depth):
        next_frontier = []
        for prefix, bounds in frontier:
            variable = choose_split_variable(problem, bounds)
            interval = bounds.get(variable, problem.root_box[variable])
            cut = (interval.lo + interval.hi) / 2
            name = problem.variable_names[variable]
            left = dict(bounds)
            right = dict(bounds)
            left[variable] = Interval(interval.lo, cut)
            right[variable] = Interval(cut, interval.hi)
            next_frontier.append((prefix + ((name, cut, False),), left))
            next_frontier.append((prefix + ((name, cut, True),), right))
        frontier = next_frontier
    return [
        make_region(
            reward,
            epsilon,
            "lower",
            {"prefix": prefix_to_json(prefix)},
        )
        for prefix, _ in frontier
    ]


def merge_lower_region_certificates(
    certificates: Sequence[LowerTreeCertificate],
) -> LowerTreeCertificate:
    """Merge a complete prefix partition into one globally verifiable tree."""
    if not certificates:
        raise ValueError("no regional certificates supplied")
    reward = certificates[0].reward
    level = certificates[0].level
    gamma = certificates[0].gamma
    for certificate in certificates:
        certificate.verify()
        if (
            certificate.reward != reward
            or certificate.level != level
            or certificate.gamma != gamma
        ):
            raise ValueError("regional certificates do not share one query")

    output_nodes: list[dict[str, Any]] = []
    roots: dict[tuple[PrefixStep, ...], int] = {}
    for certificate in certificates:
        if certificate.prefix in roots:
            raise ValueError("duplicate lower region prefix")
        offset = len(output_nodes)
        for node in certificate.nodes:
            copied = dict(node)
            if copied["kind"] == "split":
                copied["left"] = int(copied["left"]) + offset
                copied["right"] = int(copied["right"]) + offset
            output_nodes.append(copied)
        roots[certificate.prefix] = offset

    while any(prefix for prefix in roots):
        if tuple() in roots:
            raise ValueError("global prefix mixed with proper regions")
        deepest = max(len(prefix) for prefix in roots)
        deepest_prefixes = [
            prefix for prefix in roots if len(prefix) == deepest
        ]
        parent_groups: dict[
            tuple[PrefixStep, ...], dict[bool, tuple[PrefixStep, int]]
        ] = {}
        for prefix in deepest_prefixes:
            step = prefix[-1]
            children = parent_groups.setdefault(prefix[:-1], {})
            if step[2] in children:
                raise ValueError("regional prefixes overlap on one split side")
            children[step[2]] = (step, roots[prefix])

        next_roots = dict(roots)
        for parent, children in parent_groups.items():
            if set(children) != {False, True}:
                raise ValueError("regional prefixes do not form a complete partition")
            if parent in roots:
                raise ValueError("one regional prefix contains another")
            left_step, left_root = children[False]
            right_step, right_root = children[True]
            if left_step[:2] != right_step[:2]:
                raise ValueError("sibling regions disagree on their split")
            next_roots.pop(parent + (left_step,))
            next_roots.pop(parent + (right_step,))
            node_index = len(output_nodes)
            output_nodes.append(
                {
                    "kind": "split",
                    "variable": left_step[0],
                    "cut": left_step[1],
                    "left": left_root,
                    "right": right_root,
                }
            )
            next_roots[parent] = node_index
        roots = next_roots

    global_root = roots[tuple()]
    # Reindex iteratively so the public root is node zero and all nodes remain
    # reachable in deterministic preorder.
    order: list[int] = []
    stack = [global_root]
    seen: set[int] = set()
    while stack:
        old = stack.pop()
        if old in seen:
            raise ValueError("merged tree unexpectedly shares a child")
        seen.add(old)
        order.append(old)
        node = output_nodes[old]
        if node["kind"] == "split":
            stack.append(int(node["right"]))
            stack.append(int(node["left"]))
    if len(seen) != len(output_nodes):
        raise ValueError("regional merge produced unreachable nodes")
    remap = {old: new for new, old in enumerate(order)}
    normalized_nodes = []
    for old in order:
        node = dict(output_nodes[old])
        if node["kind"] == "split":
            node["left"] = remap[int(node["left"])]
            node["right"] = remap[int(node["right"])]
        normalized_nodes.append(node)
    result = LowerTreeCertificate(
        reward, level, gamma, tuple(), tuple(normalized_nodes)
    )
    result.verify()
    return result


class HeuristicSearch:
    """Deterministic untrusted stationary-grid proposal stream.

    Every proposed profile is still accepted only through exact evaluation.
    This stream is not complete and never contributes to a lower certificate.
    """

    def __init__(
        self,
        reward: RewardTable,
        target: Fraction,
        seed_start: int,
        seed_end: int,
    ) -> None:
        self.reward = reward
        self.target = target
        self.seed = seed_start
        self.seed_end = seed_end

    @staticmethod
    def _coordinate(seed: int, player: int) -> Fraction:
        digest = sha256(f"stationary-grid-v1:{seed}:{player}".encode()).digest()
        numerator = int.from_bytes(digest[:4], "big") % 257
        return Fraction(numerator, 256) if numerator <= 256 else Fraction(1)

    def step(self) -> Optional[ProfileCertificate]:
        if self.seed >= self.seed_end:
            return None
        current = self.seed
        self.seed += 1
        laws = []
        for player in PLAYERS:
            quit_mass = self._coordinate(current, player)
            laws.append(RationalLaw(1, (quit_mass,), 1 - quit_mass))
        certificate = ProfileCertificate.build(self.reward, laws, self.target)
        if certificate.exploitability < self.target:
            certificate.verify()
            return certificate
        return None


def verify_certificate_data(data: Mapping[str, Any]) -> str:
    kind = data.get("kind")
    if kind == PROFILE_KIND:
        certificate = ProfileCertificate.from_json(data)
        certificate.verify()
        return (
            "valid exact profile certificate: "
            f"{certificate.exploitability} < {certificate.epsilon}"
        )
    if kind == LOWER_KIND:
        certificate = LowerTreeCertificate.from_json(data)
        certificate.verify()
        scope = "global" if certificate.is_global else "regional"
        return (
            f"valid exact {scope} lower-tree certificate: "
            f"gamma={certificate.gamma}, level={certificate.level}"
        )
    raise ValueError(f"unknown certificate kind {kind!r}")


def verify_certificate_file(path: Path) -> str:
    return verify_certificate_data(read_json(path))


def certificate_digest(certificate: LowerTreeCertificate | ProfileCertificate) -> str:
    return json_hash(certificate.to_json())
