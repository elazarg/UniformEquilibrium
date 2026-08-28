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
from typing import Any, Iterable, Mapping, Optional, Sequence


PLAYERS = tuple(range(4))
COALITIONS = tuple(range(1, 16))
PROFILE_KIND = "fin4-rational-finite-clock-profile-v1"


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



def certificate_digest(certificate: Any) -> str:
    return json_hash(certificate.to_json())
