"""Equality-free direct-hazard finite-clock certificates for Fin4.

This module is deliberately separate from :mod:`fin4_exact_search.engine`'s
v2 outer-point problem. It reuses the engine's iterative expression evaluator
and gives the direct problem a distinct compact depth-first search and
certificate kind. Existing profile and legacy lower-tree formats are
unchanged.

The direct problem minimizes the exact exploitability of actual independent
finite-clock stopping laws.  Each marginal law is parameterized by behavioral
hazards in ``[0, 1]``; Never is the survival mass after the final represented
date.  A verified threshold ``q`` therefore proves ``F_N >= q``.  The derived
all-behavior lower bound is ``q - 24/N`` by the common-quantile compression
theorem; that analytic transport is not reproved by this Python checker.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import math
from pathlib import Path
import time
from typing import Any, Mapping, Optional, Sequence

from .engine import (
    COALITIONS,
    PLAYERS,
    ExprFactory,
    Interval,
    OuterProblem,
    PrefixStep,
    ProfileCertificate,
    Q,
    RationalLaw,
    RewardTable,
    UpperSearch,
    _bounds_from_json,
    _bounds_to_json,
    _leaf_reason,
    _node_from_json,
    _node_to_json,
    apply_prefix,
    choose_split_variable,
    prefix_from_json,
    prefix_to_json,
    qjson,
    write_json_atomic,
)


DIRECT_LOWER_KIND = "fin4-direct-hazard-lower-flat-v3"
DIRECT_SEARCH_STATE_KIND = "fin4-direct-hazard-lower-state-v2"
DIRECT_SCALE_CHECKPOINT_KIND = "fin4-direct-hazard-scale-checkpoint-v2"
ROBUST_GAP_KIND = "fin4-robust-gap-box-v1"


def finite_clock_support(level: int) -> int:
    """Number ``8 * level + 1`` of represented finite quitting dates."""
    if level <= 0:
        raise ValueError("level must be positive")
    return 8 * level + 1


def semantic_radius(level: int) -> Fraction:
    """Coordinatewise normalized Fin4 compression radius ``12 / level``."""
    if level <= 0:
        raise ValueError("level must be positive")
    return Fraction(12, level)


def exploitability_error(level: int) -> Fraction:
    """Exploitability transport error ``24 / level``."""
    return 2 * semantic_radius(level)


def hazard_name(player: int, time_index: int) -> str:
    return f"p{player}.h{time_index}"


def hazards_to_law(hazards: Sequence[Fraction]) -> RationalLaw:
    """Convert exact behavioral hazards to a finite-clock stopping law."""
    if not hazards:
        raise ValueError("at least one finite date is required")
    parsed = tuple(Q(hazard) for hazard in hazards)
    if any(hazard < 0 or 1 < hazard for hazard in parsed):
        raise ValueError("hazards must lie in [0,1]")
    survival = Fraction(1)
    finite = []
    for hazard in parsed:
        finite.append(survival * hazard)
        survival *= 1 - hazard
    return RationalLaw(len(parsed), tuple(finite), survival)


def law_to_hazards(law: RationalLaw) -> tuple[Fraction, ...]:
    """A rational right inverse of :func:`hazards_to_law`."""
    survival = Fraction(1)
    hazards = []
    for mass in law.finite:
        if survival == 0:
            if mass != 0:
                raise ValueError("positive mass follows zero survival")
            hazard = Fraction(0)
        else:
            hazard = mass / survival
        if hazard < 0 or 1 < hazard:
            raise ValueError("invalid stopping law")
        hazards.append(hazard)
        survival -= mass
    if survival != law.never:
        raise ValueError("finite masses and Never mass do not sum correctly")
    return tuple(hazards)


def hazard_profile(
    hazards: Sequence[Sequence[Fraction]],
) -> tuple[RationalLaw, RationalLaw, RationalLaw, RationalLaw]:
    """Convert four common-clock hazard rows to independent marginal laws."""
    if len(hazards) != 4:
        raise ValueError("Fin4 requires four hazard rows")
    laws = tuple(hazards_to_law(row) for row in hazards)
    if len({law.clock_bound for law in laws}) != 1:
        raise ValueError("all players must use the same finite clock")
    return laws  # type: ignore[return-value]


def build_direct_hazard_problem(reward: RewardTable, level: int) -> OuterProblem:
    """Build the equality-free exact finite-clock exploitability problem.

    The resulting :class:`OuterProblem` has only ``4 * (8*level+1)`` hazard
    variables, no equality or inequality rows, and one exact max-polynomial
    objective.  Its ``radius`` field is zero because there is no outer semantic
    tube in this problem.
    """
    reward.validate_normalized()
    clock = finite_clock_support(level)
    factory = ExprFactory()
    zero = factory.const(0)
    one = factory.const(1)

    names: list[str] = []
    root_box: list[Interval] = []
    variable_index: dict[str, int] = {}

    def variable(name: str) -> int:
        index = len(names)
        names.append(name)
        root_box.append(Interval(Fraction(0), Fraction(1)))
        variable_index[name] = index
        return factory.var(index)

    survival: dict[tuple[int, int], int] = {}
    mass: dict[tuple[int, int], int] = {}
    for player in PLAYERS:
        survival[player, 0] = one
        for time_index in range(clock):
            hazard = variable(hazard_name(player, time_index))
            mass[player, time_index] = factory.mul(
                survival[player, time_index], hazard
            )
            survival[player, time_index + 1] = factory.mul(
                survival[player, time_index], factory.sub(one, hazard)
            )

    payoff_expr: list[int] = []
    for observer in PLAYERS:
        terms = []
        for time_index in range(clock):
            for mask in COALITIONS:
                coefficient = reward(mask, observer)
                if coefficient == 0:
                    continue
                probability = factory.prod(
                    mass[player, time_index]
                    if mask & (1 << player)
                    else survival[player, time_index + 1]
                    for player in PLAYERS
                )
                terms.append(
                    factory.mul(factory.const(coefficient), probability)
                )
        payoff_expr.append(factory.sum(terms))

    cap_expr: list[int] = []
    for player in PLAYERS:
        opponents = tuple(other for other in PLAYERS if other != player)
        prefix = zero
        candidates = []
        for time_index in range(clock):
            tie_terms = []
            early_terms = []
            for submask in range(1 << len(opponents)):
                terminal_mask = 1 << player
                factors = []
                for offset, opponent in enumerate(opponents):
                    if submask & (1 << offset):
                        terminal_mask |= 1 << opponent
                        factors.append(mass[opponent, time_index])
                    else:
                        factors.append(survival[opponent, time_index + 1])
                probability = factory.prod(factors)
                tie_coefficient = reward(terminal_mask, player)
                if tie_coefficient:
                    tie_terms.append(
                        factory.mul(factory.const(tie_coefficient), probability)
                    )
                if submask:
                    opponent_mask = terminal_mask & ~(1 << player)
                    early_coefficient = reward(opponent_mask, player)
                    if early_coefficient:
                        early_terms.append(
                            factory.mul(
                                factory.const(early_coefficient), probability
                            )
                        )
            candidates.append(factory.add(prefix, factory.sum(tie_terms)))
            prefix = factory.add(prefix, factory.sum(early_terms))

        opponent_never = factory.prod(
            survival[opponent, clock] for opponent in opponents
        )
        after_support = factory.add(
            prefix,
            factory.mul(
                factory.const(reward(1 << player, player)), opponent_never
            ),
        )
        candidates.append(after_support)
        candidates.append(prefix)  # Never.
        cap_expr.append(factory.max_all(candidates))

    objective = factory.max_all(
        [zero]
        + [
            factory.sub(cap_expr[player], payoff_expr[player])
            for player in PLAYERS
        ]
    )
    return OuterProblem(
        reward=reward,
        level=level,
        clock_bound=clock,
        radius=Fraction(0),
        factory=factory,
        variable_names=tuple(names),
        variable_index=variable_index,
        root_box=tuple(root_box),
        equalities=tuple(),
        inequalities=tuple(),
        objective=objective,
    )


def hazard_point_bounds(
    problem: OuterProblem,
    hazards: Sequence[Sequence[Fraction]],
) -> dict[int, Interval]:
    """Encode one exact common-clock hazard profile as point intervals."""
    if len(hazards) != 4:
        raise ValueError("four hazard rows are required")
    clock = problem.clock_bound
    if any(len(row) != clock for row in hazards):
        raise ValueError("hazard clock does not match the direct problem")
    bounds = {}
    for player in PLAYERS:
        for time_index in range(clock):
            value = Q(hazards[player][time_index])
            if value < 0 or 1 < value:
                raise ValueError("hazards must lie in [0,1]")
            name = hazard_name(player, time_index)
            if name not in problem.variable_index:
                raise ValueError("problem is not a matching direct hazard problem")
            bounds[problem.variable_index[name]] = Interval.point(value)
    if len(bounds) != len(problem.variable_names):
        raise ValueError("problem contains non-hazard variables")
    return bounds


def eval_direct_hazard_exact(
    problem: OuterProblem,
    hazards: Sequence[Sequence[Fraction]],
) -> Fraction:
    """Evaluate the direct objective exactly at one rational hazard point."""
    bounds = hazard_point_bounds(problem, hazards)
    value = problem.factory.eval_interval(
        problem.objective, problem.root_box, bounds, {}
    )
    if value.lo != value.hi:
        raise AssertionError("point evaluation did not return a point interval")
    return value.lo


@dataclass(frozen=True)
class DirectHazardLowerTreeCertificate:
    """Flat tree proving a threshold lower bound for the direct value ``F_N``."""

    reward: RewardTable
    level: int
    threshold: Fraction
    prefix: tuple[PrefixStep, ...]
    nodes: tuple[dict[str, Any], ...]

    @property
    def is_global(self) -> bool:
        return not self.prefix

    @property
    def global_lower(self) -> Fraction:
        return self.threshold - exploitability_error(self.level)

    def verify(self) -> None:
        problem = build_direct_hazard_problem(self.reward, self.level)
        if self.threshold <= 0:
            raise ValueError("direct lower threshold must be positive")
        if not self.nodes:
            raise ValueError("a direct lower certificate needs a root node")
        initial = apply_prefix(problem, self.prefix)
        # Traverse with one mutable path box.  A conventional DFS stack that
        # copies the whole sparse box at every sibling is quadratic in the
        # depth before all hazard variables have been touched.
        current: Optional[int] = 0
        stack: list[tuple[str, int, int, Interval]] = []
        seen: set[int] = set()
        while current is not None:
            node_index = current
            if not 0 <= node_index < len(self.nodes):
                raise ValueError("tree child index is out of range")
            if node_index in seen:
                raise ValueError("tree contains a cycle or a shared child")
            seen.add(node_index)
            node = self.nodes[node_index]
            kind = node.get("kind")
            if kind == "leaf":
                expected = _leaf_reason(problem, initial, self.threshold)
                if expected != node:
                    raise ValueError(
                        f"invalid leaf {node_index}: stored {node}, "
                        f"expected {expected}"
                    )
                current = None
            else:
                if kind != "split":
                    raise ValueError(f"unknown tree node kind {kind!r}")
                variable_name = str(node["variable"])
                if variable_name not in problem.variable_index:
                    raise ValueError(f"unknown split variable {variable_name}")
                variable = problem.variable_index[variable_name]
                cut = Q(node["cut"])
                interval = initial.get(variable, problem.root_box[variable])
                if not interval.lo < cut < interval.hi:
                    raise ValueError("split cut is not strictly inside its interval")
                stack.append(("restore", -1, variable, interval))
                stack.append(
                    (
                        "visit",
                        int(node["right"]),
                        variable,
                        Interval(cut, interval.hi),
                    )
                )
                initial[variable] = Interval(interval.lo, cut)
                current = int(node["left"])
            while current is None and stack:
                action, target, variable, interval = stack.pop()
                initial[variable] = interval
                if action == "visit":
                    current = target
                elif action != "restore":
                    raise AssertionError(action)
        if len(seen) != len(self.nodes):
            raise ValueError("certificate has unreachable nodes")

    def verify_positive_global(self) -> Fraction:
        self.verify()
        if not self.is_global:
            raise ValueError("regional direct tree is not a global certificate")
        if self.global_lower <= 0:
            raise ValueError("threshold does not clear the compression error")
        return self.global_lower

    def to_json(self) -> dict[str, Any]:
        return {
            "kind": DIRECT_LOWER_KIND,
            "reward": self.reward.to_json(),
            "level": self.level,
            "threshold": qjson(self.threshold),
            "global_lower": qjson(self.global_lower),
            "prefix": prefix_to_json(self.prefix),
            "nodes": [_node_to_json(node) for node in self.nodes],
        }

    @staticmethod
    def from_json(
        data: Mapping[str, Any],
    ) -> "DirectHazardLowerTreeCertificate":
        if data.get("kind") != DIRECT_LOWER_KIND:
            raise ValueError("wrong direct lower certificate kind")
        raw_nodes = tuple(_node_from_json(node) for node in data["nodes"])
        if any(node is None for node in raw_nodes):
            raise ValueError("completed certificate contains pending nodes")
        certificate = DirectHazardLowerTreeCertificate(
            RewardTable.from_json(data["reward"]),
            int(data["level"]),
            Q(data["threshold"]),
            prefix_from_json(data.get("prefix", [])),
            raw_nodes,  # type: ignore[arg-type]
        )
        if (
            "global_lower" in data
            and Q(data["global_lower"]) != certificate.global_lower
        ):
            raise ValueError("stored direct global lower bound is inconsistent")
        return certificate


@dataclass(frozen=True)
class RobustGapCertificate:
    """A direct lower certificate and its exact reward-sup-norm neighborhood."""

    lower: DirectHazardLowerTreeCertificate
    radius: Fraction
    gamma: Fraction

    @staticmethod
    def canonical(
        lower: DirectHazardLowerTreeCertificate,
    ) -> "RobustGapCertificate":
        margin = lower.global_lower
        if margin <= 0:
            raise ValueError("direct lower tree has no positive global margin")
        return RobustGapCertificate(lower, margin / 4, margin / 2)

    def verify(self) -> None:
        margin = self.lower.verify_positive_global()
        if self.radius <= 0 or self.gamma <= 0:
            raise ValueError("robust radius and gap must be positive")
        if self.gamma > margin - 2 * self.radius:
            raise ValueError("robust gap exceeds the reward-Lipschitz remainder")

    def to_json(self) -> dict[str, Any]:
        return {
            "kind": ROBUST_GAP_KIND,
            "lower": self.lower.to_json(),
            "reward_sup_radius": qjson(self.radius),
            "uniform_gamma": qjson(self.gamma),
        }

    @staticmethod
    def from_json(data: Mapping[str, Any]) -> "RobustGapCertificate":
        if data.get("kind") != ROBUST_GAP_KIND:
            raise ValueError("wrong robust-gap certificate kind")
        certificate = RobustGapCertificate(
            DirectHazardLowerTreeCertificate.from_json(data["lower"]),
            Q(data["reward_sup_radius"]),
            Q(data["uniform_gamma"]),
        )
        return certificate


class DirectHazardLowerSearch:
    """Exact DFS with a single mutable path box and compact sibling events.

    The proof tree necessarily grows with explored proof nodes.  The live
    frontier does not copy an increasingly large interval dictionary for every
    pending sibling: it stores two constant-size events per active split.
    """

    def __init__(
        self,
        problem: OuterProblem,
        gamma: Fraction,
        prefix: Sequence[PrefixStep] = (),
    ) -> None:
        if gamma <= 0:
            raise ValueError("gamma must be positive")
        self.problem = problem
        self.gamma = Q(gamma)
        self.prefix = tuple(prefix)
        self.nodes: list[Optional[dict[str, Any]]] = [None]
        self.current_node: Optional[int] = 0
        self.bounds = apply_prefix(problem, prefix)
        self.stack: list[tuple[str, int, int, Interval]] = []
        self.steps = 0

    def _advance(self) -> None:
        self.current_node = None
        while self.current_node is None and self.stack:
            action, target, variable, interval = self.stack.pop()
            self.bounds[variable] = interval
            if action == "visit":
                self.current_node = target
            elif action != "restore":
                raise AssertionError(action)

    def step(self) -> Optional[DirectHazardLowerTreeCertificate]:
        if self.current_node is None:
            return self.certificate()
        node_index = self.current_node
        leaf = _leaf_reason(self.problem, self.bounds, self.gamma)
        if leaf is not None:
            self.nodes[node_index] = leaf
            self._advance()
        else:
            variable = choose_split_variable(self.problem, self.bounds)
            interval = self.bounds.get(variable, self.problem.root_box[variable])
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
            self.stack.append(("restore", -1, variable, interval))
            self.stack.append(
                (
                    "visit",
                    right_index,
                    variable,
                    Interval(cut, interval.hi),
                )
            )
            self.bounds[variable] = Interval(interval.lo, cut)
            self.current_node = left_index
        self.steps += 1
        if self.current_node is None:
            # Return the constructed proof object without rebuilding its DAG
            # while this producer still owns the live problem. Public CLI and
            # campaign gates release the resolver, then verify independently.
            return self.certificate()
        return None

    def certificate(self) -> DirectHazardLowerTreeCertificate:
        if self.current_node is not None or self.stack or any(
            node is None for node in self.nodes
        ):
            raise ValueError("direct lower search is not complete")
        return DirectHazardLowerTreeCertificate(
            self.problem.reward,
            self.problem.level,
            self.gamma,
            self.prefix,
            tuple(self.nodes),  # type: ignore[arg-type]
        )

    def to_state_json(self) -> dict[str, Any]:
        return {
            "kind": DIRECT_SEARCH_STATE_KIND,
            "level": self.problem.level,
            "reward_sha256": self.problem.reward.digest,
            "gamma": qjson(self.gamma),
            "prefix": prefix_to_json(self.prefix),
            "nodes": [_node_to_json(node) for node in self.nodes],
            "current_node": self.current_node,
            "bounds": _bounds_to_json(self.bounds),
            "stack": [
                {
                    "action": action,
                    "target": target,
                    "variable": variable,
                    "interval": interval.to_json(),
                }
                for action, target, variable, interval in self.stack
            ],
            "steps": self.steps,
        }

    @staticmethod
    def from_state_json(
        problem: OuterProblem,
        data: Mapping[str, Any],
    ) -> "DirectHazardLowerSearch":
        if data.get("kind") != DIRECT_SEARCH_STATE_KIND:
            raise ValueError("wrong direct lower-search state kind")
        if int(data["level"]) != problem.level:
            raise ValueError("direct lower-search level mismatch")
        if str(data["reward_sha256"]) != problem.reward.digest:
            raise ValueError("direct lower-search reward mismatch")
        search = DirectHazardLowerSearch(
            problem,
            Q(data["gamma"]),
            prefix_from_json(data.get("prefix", [])),
        )
        search.nodes = [_node_from_json(node) for node in data["nodes"]]
        raw_current = data.get("current_node")
        search.current_node = None if raw_current is None else int(raw_current)
        search.bounds = _bounds_from_json(data["bounds"])
        search.stack = [
            (
                str(item["action"]),
                int(item["target"]),
                int(item["variable"]),
                Interval.from_json(item["interval"]),
            )
            for item in data["stack"]
        ]
        search.steps = int(data.get("steps", 0))
        return search


def required_direct_level(epsilon: Fraction, alpha: Fraction) -> int:
    """Least positive ``N`` with ``24/N < (1-alpha)*epsilon``."""
    epsilon = Q(epsilon)
    alpha = Q(alpha)
    if epsilon <= 0:
        raise ValueError("epsilon must be positive")
    if not 0 < alpha < 1:
        raise ValueError("alpha must lie strictly between zero and one")
    allowance = (1 - alpha) * epsilon
    return math.floor(Fraction(24) / allowance) + 1


@dataclass(frozen=True)
class ConfigurableDirectScaleContract:
    """Exact finite/global bracket at accuracy ``epsilon`` and split ``alpha``.

    The direct lower fork proves the finite-clock value at least
    ``alpha*epsilon + 24/N``.  Quantile transport then proves the unrestricted
    value at least ``alpha*epsilon``.  The upper fork searches for a literal
    finite-clock profile with exploitability strictly below ``epsilon``.
    """

    epsilon: Fraction
    alpha: Fraction

    def __post_init__(self) -> None:
        epsilon = Q(self.epsilon)
        alpha = Q(self.alpha)
        if epsilon <= 0:
            raise ValueError("epsilon must be positive")
        if not 0 < alpha < 1:
            raise ValueError("alpha must lie strictly between zero and one")
        object.__setattr__(self, "epsilon", epsilon)
        object.__setattr__(self, "alpha", alpha)

    @property
    def level(self) -> int:
        return required_direct_level(self.epsilon, self.alpha)

    @property
    def compression_error(self) -> Fraction:
        return exploitability_error(self.level)

    @property
    def lower_finite_threshold(self) -> Fraction:
        return self.alpha * self.epsilon + self.compression_error

    @property
    def certified_global_lower(self) -> Fraction:
        return self.alpha * self.epsilon

    @property
    def upper_target(self) -> Fraction:
        return self.epsilon

    def verify(self) -> None:
        if not self.compression_error < (1 - self.alpha) * self.epsilon:
            raise AssertionError("direct scale does not have a strict bracket")
        if (
            self.lower_finite_threshold - self.compression_error
            != self.certified_global_lower
        ):
            raise AssertionError("direct lower transport identity failed")

    def to_json(self) -> dict[str, Any]:
        self.verify()
        return {
            "epsilon": qjson(self.epsilon),
            "alpha": qjson(self.alpha),
            "level": self.level,
            "finite_clock_support": finite_clock_support(self.level),
            "compression_error": qjson(self.compression_error),
            "lower_finite_threshold": qjson(self.lower_finite_threshold),
            "certified_global_lower": qjson(self.certified_global_lower),
            "upper_target": qjson(self.upper_target),
        }

    @staticmethod
    def from_json(data: Mapping[str, Any]) -> "ConfigurableDirectScaleContract":
        contract = ConfigurableDirectScaleContract(
            Q(data["epsilon"]), Q(data["alpha"])
        )
        expected = contract.to_json()
        if any(str(data.get(key)) != str(value) for key, value in expected.items()):
            raise ValueError("direct scale contract is inconsistent")
        return contract


@dataclass(frozen=True)
class DirectScaleSearchResult:
    kind: str
    certificate: DirectHazardLowerTreeCertificate | ProfileCertificate


class DirectScaleSearch:
    """Fair resumable fork between direct lower proof and exact profile search."""

    def __init__(
        self, reward: RewardTable, epsilon: Fraction, alpha: Fraction
    ) -> None:
        reward.validate_normalized()
        self.reward = reward
        self.contract = ConfigurableDirectScaleContract(epsilon, alpha)
        self.contract.verify()
        self.problem = build_direct_hazard_problem(reward, self.contract.level)
        self.lower = DirectHazardLowerSearch(
            self.problem, self.contract.lower_finite_threshold
        )
        self.upper = UpperSearch(reward, self.contract.upper_target)
        self.turn = 0
        self.steps = 0

    def step(self) -> Optional[DirectScaleSearchResult]:
        if self.turn % 2 == 0:
            certificate = self.lower.step()
            self.turn += 1
            self.steps += 1
            if certificate is None:
                return None
            if not certificate.is_global:
                raise AssertionError("scale lower fork returned a regional tree")
            if certificate.global_lower != self.contract.certified_global_lower:
                raise AssertionError("scale lower certificate has the wrong transport")
            return DirectScaleSearchResult("lower", certificate)
        certificate = self.upper.step()
        self.turn += 1
        self.steps += 1
        if certificate is not None:
            return DirectScaleSearchResult("profile", certificate)
        return None

    def run(
        self,
        max_steps: Optional[int] = None,
        max_seconds: Optional[float] = None,
        checkpoint_path: Optional[Path] = None,
        checkpoint_every: int = 100,
    ) -> Optional[DirectScaleSearchResult]:
        if checkpoint_every <= 0:
            raise ValueError("checkpoint_every must be positive")
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
            "kind": DIRECT_SCALE_CHECKPOINT_KIND,
            "reward": self.reward.to_json(),
            "table_sha256": self.reward.digest,
            "contract": self.contract.to_json(),
            "turn": self.turn,
            "steps": self.steps,
            "lower": self.lower.to_state_json(),
            "upper": self.upper.to_state_json(),
        }

    @staticmethod
    def from_checkpoint_json(data: Mapping[str, Any]) -> "DirectScaleSearch":
        if data.get("kind") != DIRECT_SCALE_CHECKPOINT_KIND:
            raise ValueError("wrong direct scale checkpoint kind")
        reward = RewardTable.from_json(data["reward"])
        if reward.digest != data.get("table_sha256"):
            raise ValueError("direct checkpoint table hash mismatch")
        contract = ConfigurableDirectScaleContract.from_json(data["contract"])
        search = DirectScaleSearch.__new__(DirectScaleSearch)
        search.reward = reward
        search.contract = contract
        search.problem = build_direct_hazard_problem(reward, contract.level)
        search.lower = DirectHazardLowerSearch.from_state_json(
            search.problem, data["lower"]
        )
        search.upper = UpperSearch.from_state_json(reward, data["upper"])
        if (
            search.lower.gamma != contract.lower_finite_threshold
            or search.lower.prefix
        ):
            raise ValueError("checkpoint lower fork violates its scale contract")
        if (
            search.upper.target != contract.upper_target
            or search.upper.diagonal_end is not None
        ):
            raise ValueError("checkpoint upper fork violates its scale contract")
        search.turn = int(data["turn"])
        search.steps = int(data.get("steps", 0))
        if search.turn < 0 or search.steps < 0 or search.turn != search.steps:
            raise ValueError("invalid direct scale scheduler counters")
        return search


__all__ = [
    "DIRECT_LOWER_KIND",
    "DIRECT_SCALE_CHECKPOINT_KIND",
    "DIRECT_SEARCH_STATE_KIND",
    "ROBUST_GAP_KIND",
    "ConfigurableDirectScaleContract",
    "DirectHazardLowerSearch",
    "DirectHazardLowerTreeCertificate",
    "DirectScaleSearch",
    "DirectScaleSearchResult",
    "RobustGapCertificate",
    "build_direct_hazard_problem",
    "eval_direct_hazard_exact",
    "exploitability_error",
    "finite_clock_support",
    "hazard_name",
    "hazard_point_bounds",
    "hazard_profile",
    "hazards_to_law",
    "law_to_hazards",
    "required_direct_level",
    "semantic_radius",
]
