"""Single-resolver outer campaign over tracked Fin4 candidate tables.

This is a producer and scheduler, not a decision procedure.  It deterministically
rationalizes the tracked candidate-search output (or an embedded fallback),
then advances exact table/scale resolvers one at a time.  A verified lower
certificate proves its stated positive all-behavior gap; a verified profile
certificate proves only that displayed profile's stated exploitability bound.
Exhaustion, timeout, and an unfinished checkpoint prove nothing about the
quitting-game conjecture.

The resolver factory is injectable. The default uses the equality-free
:class:`DirectScaleSearch`; tests may supply another resolver implementing the
same ``run`` and ``to_checkpoint_json`` operations.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
import gc
import json
from pathlib import Path
import time
from typing import Any, Callable, Mapping, Optional, Protocol, Sequence

try:
    import resource
except ImportError:  # pragma: no cover - resource is present on Unix workers.
    resource = None  # type: ignore[assignment]

from .direct_oracle import (
    ConfigurableDirectScaleContract,
    DIRECT_LOWER_KIND,
    DirectHazardLowerTreeCertificate,
    DirectScaleSearch,
    RobustGapCertificate,
)
from .engine import (
    PROFILE_KIND,
    ProfileCertificate,
    Q,
    RewardTable,
    certificate_digest,
    json_hash,
    qjson,
    read_json,
    write_json_atomic,
)


CAMPAIGN_KIND = "fin4-tracked-candidate-campaign-v1"
DEFAULT_ALPHA = Fraction(1, 2)
DEFAULT_RESULTS = (
    Path(__file__).resolve().parents[2]
    / "singleton_collision_candidate_search"
    / "results.json"
)


def _peak_rss_mib() -> Optional[float]:
    if resource is None:
        return None
    return round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024, 1)


@dataclass(frozen=True)
class Candidate:
    candidate_id: str
    source: str
    reward: RewardTable

    def to_json(self) -> dict[str, Any]:
        return {
            "candidate_id": self.candidate_id,
            "source": self.source,
            "table_sha256": self.reward.digest,
            "reward": self.reward.to_json(),
        }


def _coalition_mask(label: str) -> int:
    if not (label.startswith("{") and label.endswith("}")):
        raise ValueError(f"invalid coalition label {label!r}")
    body = label[1:-1].strip()
    if not body:
        return 0
    mask = 0
    for token in body.split(","):
        player = int(token.strip())
        if not 1 <= player <= 4:
            raise ValueError(f"invalid one-based player {player}")
        bit = 1 << (player - 1)
        if mask & bit:
            raise ValueError(f"duplicate player in coalition {label!r}")
        mask |= bit
    return mask


def _rational_coordinate(value: Any, denominator: int) -> Fraction:
    if denominator <= 0:
        raise ValueError("rationalization denominator must be positive")
    if isinstance(value, Decimal):
        rational = Fraction(value)
    elif isinstance(value, int):
        rational = Fraction(value)
    else:
        rational = Fraction(str(value))
    if abs(rational) > 4:
        raise ValueError("tracked candidate coordinate lies outside [-4,4]")
    return (rational / 4).limit_denominator(denominator)


def _table_from_labelled_rows(
    rows: Mapping[str, Sequence[Any]], denominator: int
) -> RewardTable:
    by_mask: dict[int, tuple[Fraction, Fraction, Fraction, Fraction]] = {}
    for label, raw_row in rows.items():
        mask = _coalition_mask(label)
        if mask == 0:
            continue
        if mask in by_mask or len(raw_row) != 4:
            raise ValueError("duplicate coalition or malformed reward row")
        values = tuple(_rational_coordinate(value, denominator) for value in raw_row)
        by_mask[mask] = values  # type: ignore[assignment]
    if set(by_mask) != set(range(1, 16)):
        raise ValueError("candidate table does not contain all 15 coalitions")
    reward = RewardTable(tuple(by_mask[mask] for mask in range(1, 16)))
    reward.validate_normalized()
    return reward


def _fallback_seed_rows() -> dict[str, list[int]]:
    """Exact Solan--Vieille boundary seed used when results.json is absent."""
    return {
        "{1}": [1, 4, 0, 0],
        "{2}": [4, 1, 0, 0],
        "{1,2}": [1, 1, 1, 1],
        "{3}": [0, 0, 1, 4],
        "{1,3}": [1, 1, 1, 0],
        "{2,3}": [0, 1, 1, 1],
        "{1,2,3}": [1, 0, 0, 0],
        "{4}": [0, 0, 4, 1],
        "{1,4}": [1, 0, 1, 1],
        "{2,4}": [1, 1, 0, 1],
        "{1,2,4}": [0, 1, 0, 0],
        "{3,4}": [1, 1, 1, 1],
        "{1,3,4}": [0, 0, 0, 1],
        "{2,3,4}": [0, 0, 1, 0],
        "{1,2,3,4}": [-1, -1, -1, -1],
    }


def load_tracked_candidates(
    results_path: Path = DEFAULT_RESULTS,
    denominator: int = 10_000,
) -> tuple[Candidate, ...]:
    """Return the stable exact corpus derived from tracked numerical output."""
    raw: list[tuple[str, str, Mapping[str, Sequence[Any]]]] = []
    if results_path.exists():
        data = json.loads(results_path.read_text(encoding="utf-8"), parse_float=Decimal)
        seed = data.get("seed_table", {}).get("table")
        if seed is not None:
            raw.append(("seed", "tracked-seed-table", seed))
        chains = sorted(data.get("chains", []), key=lambda chain: int(chain["seed"]))
        for chain in chains:
            seed_value = int(chain["seed"])
            table = chain.get("best", {}).get("table")
            if table is not None:
                raw.append(
                    (
                        f"chain-{seed_value}-best",
                        f"tracked-chain-{seed_value}-best",
                        table,
                    )
                )
    if not raw:
        raw.append(("seed", "embedded-exact-fallback", _fallback_seed_rows()))

    candidates: list[Candidate] = []
    seen: set[str] = set()
    for candidate_id, source, table_rows in raw:
        reward = _table_from_labelled_rows(table_rows, denominator)
        if reward.digest in seen:
            continue
        seen.add(reward.digest)
        candidates.append(Candidate(candidate_id, source, reward))
    if not candidates:
        raise ValueError("candidate corpus is empty")
    return tuple(candidates)


@dataclass(frozen=True)
class CampaignDescriptor:
    candidate_corpus_sha256: str
    rational_denominator: int
    start_epsilon: Fraction
    refinement: Fraction
    alpha: Fraction
    scale_limit: Optional[int]
    shard_count: int
    shard_index: int

    @staticmethod
    def create(
        candidates: Sequence[Candidate],
        rational_denominator: int = 10_000,
        start_epsilon: Fraction = Fraction(4),
        refinement: Fraction = Fraction(2),
        alpha: Fraction = DEFAULT_ALPHA,
        scale_limit: Optional[int] = None,
        shard_count: int = 1,
        shard_index: int = 0,
    ) -> "CampaignDescriptor":
        if rational_denominator <= 0:
            raise ValueError("rational denominator must be positive")
        if start_epsilon <= 0 or refinement <= 1:
            raise ValueError("invalid scale schedule")
        if not 0 < alpha < 1:
            raise ValueError("alpha must lie strictly between zero and one")
        if scale_limit is not None and scale_limit <= 0:
            raise ValueError("scale_limit must be positive when supplied")
        if shard_count <= 0 or not 0 <= shard_index < shard_count:
            raise ValueError("invalid campaign shard")
        corpus = json_hash([candidate.to_json() for candidate in candidates])
        return CampaignDescriptor(
            corpus,
            rational_denominator,
            start_epsilon,
            refinement,
            alpha,
            scale_limit,
            shard_count,
            shard_index,
        )

    def payload(self) -> dict[str, Any]:
        return {
            "kind": CAMPAIGN_KIND,
            "candidate_corpus_sha256": self.candidate_corpus_sha256,
            "rational_denominator": self.rational_denominator,
            "start_epsilon": qjson(self.start_epsilon),
            "refinement": qjson(self.refinement),
            "alpha": qjson(self.alpha),
            "scale_limit": self.scale_limit,
            "shard_count": self.shard_count,
            "shard_index": self.shard_index,
        }

    @property
    def descriptor_sha256(self) -> str:
        return json_hash(self.payload())

    @property
    def campaign_id(self) -> str:
        return f"candidate-campaign-{self.descriptor_sha256[:20]}"

    def to_json(self) -> dict[str, Any]:
        return {
            **self.payload(),
            "descriptor_sha256": self.descriptor_sha256,
            "campaign_id": self.campaign_id,
        }

    @staticmethod
    def from_json(data: Mapping[str, Any]) -> "CampaignDescriptor":
        if data.get("kind") != CAMPAIGN_KIND:
            raise ValueError("wrong candidate campaign kind")
        descriptor = CampaignDescriptor(
            str(data["candidate_corpus_sha256"]),
            int(data["rational_denominator"]),
            Q(data["start_epsilon"]),
            Q(data["refinement"]),
            Q(data["alpha"]),
            None if data.get("scale_limit") is None else int(data["scale_limit"]),
            int(data["shard_count"]),
            int(data["shard_index"]),
        )
        # Reuse constructor validation without needing the candidate corpus.
        if (
            descriptor.rational_denominator <= 0
            or descriptor.start_epsilon <= 0
            or descriptor.refinement <= 1
            or not 0 < descriptor.alpha < 1
            or (
                descriptor.scale_limit is not None
                and descriptor.scale_limit <= 0
            )
            or descriptor.shard_count <= 0
            or not 0 <= descriptor.shard_index < descriptor.shard_count
        ):
            raise ValueError("invalid candidate campaign descriptor")
        if data.get("descriptor_sha256") not in (None, descriptor.descriptor_sha256):
            raise ValueError("candidate campaign descriptor hash mismatch")
        if data.get("campaign_id") not in (None, descriptor.campaign_id):
            raise ValueError("candidate campaign id mismatch")
        return descriptor


@dataclass(frozen=True)
class CampaignWorkUnit:
    ordinal: int
    candidate_index: int
    scale_index: int
    candidate_id: str
    table_sha256: str
    epsilon: Fraction

    @property
    def work_id(self) -> str:
        return (
            f"candidate-{self.candidate_index}-scale-{self.scale_index}-"
            f"{self.table_sha256[:12]}"
        )

    def to_json(self) -> dict[str, Any]:
        return {
            "ordinal": self.ordinal,
            "work_id": self.work_id,
            "candidate_index": self.candidate_index,
            "scale_index": self.scale_index,
            "candidate_id": self.candidate_id,
            "table_sha256": self.table_sha256,
            "epsilon": qjson(self.epsilon),
        }


class Resolver(Protocol):
    steps: int

    def run(
        self,
        max_steps: Optional[int] = None,
        max_seconds: Optional[float] = None,
    ) -> Any: ...

    def to_checkpoint_json(self) -> Mapping[str, Any]: ...


ResolverFactory = Callable[
    [RewardTable, Fraction, Fraction, Optional[Mapping[str, Any]]], Resolver
]


def default_resolver_factory(
    reward: RewardTable,
    epsilon: Fraction,
    alpha: Fraction,
    state: Optional[Mapping[str, Any]],
) -> Resolver:
    if state is None:
        return DirectScaleSearch(reward, epsilon, alpha)
    search = DirectScaleSearch.from_checkpoint_json(state)
    if (
        search.reward != reward
        or search.contract.epsilon != epsilon
        or search.contract.alpha != alpha
    ):
        raise ValueError("resolver checkpoint belongs to another work unit")
    return search


class CandidateCampaign:
    """Scale-major campaign with at most one resident exact resolver.

    A work unit remains current until its mathematically total lower/profile
    fork resolves.  This avoids constructing finer-scale expression DAGs merely
    because a scheduling quantum elapsed.  With no ``scale_limit`` the work
    stream is infinite and the command stops only on a verified lower result
    or an external interruption.
    """

    def __init__(
        self,
        candidates: Sequence[Candidate],
        descriptor: CampaignDescriptor,
        state_dir: Path,
        resolver_factory: ResolverFactory = default_resolver_factory,
    ) -> None:
        if not candidates:
            raise ValueError("candidate campaign needs a nonempty corpus")
        corpus = json_hash([candidate.to_json() for candidate in candidates])
        if corpus != descriptor.candidate_corpus_sha256:
            raise ValueError("candidate corpus does not match descriptor")
        self.candidates = tuple(candidates)
        self.descriptor = descriptor
        self.state_dir = state_dir
        self.resolver_factory = resolver_factory
        total_first_scale = len(self.candidates)
        if descriptor.scale_limit is not None and descriptor.shard_index >= (
            total_first_scale * descriptor.scale_limit
        ):
            raise ValueError("campaign shard owns no work units")
        self.next_ordinal = descriptor.shard_index
        self.quanta = 0
        self.exact_steps = 0
        self.completed: dict[str, dict[str, Any]] = {}
        self.terminal_lower: Optional[dict[str, Any]] = None
        self.active_resolver: Optional[Resolver] = None
        self.peak_resident_resolvers = 0
        self.last_resolver_stats: dict[str, Any] = {}

    def _work_unit(self, ordinal: int) -> Optional[CampaignWorkUnit]:
        if ordinal < 0:
            raise ValueError("negative campaign work ordinal")
        candidate_index = ordinal % len(self.candidates)
        scale_index = ordinal // len(self.candidates)
        if (
            self.descriptor.scale_limit is not None
            and scale_index >= self.descriptor.scale_limit
        ):
            return None
        candidate = self.candidates[candidate_index]
        epsilon = (
            self.descriptor.start_epsilon
            / self.descriptor.refinement**scale_index
        )
        return CampaignWorkUnit(
            ordinal,
            candidate_index,
            scale_index,
            candidate.candidate_id,
            candidate.reward.digest,
            epsilon,
        )

    def preview_work_units(self, count: int) -> tuple[CampaignWorkUnit, ...]:
        """Describe the next owned units without constructing their DAGs."""
        if count < 0:
            raise ValueError("preview count must be nonnegative")
        units = []
        ordinal = self.next_ordinal
        while len(units) < count:
            unit = self._work_unit(ordinal)
            if unit is None:
                break
            units.append(unit)
            ordinal += self.descriptor.shard_count
        return tuple(units)

    @property
    def resident_resolver_count(self) -> int:
        return 0 if self.active_resolver is None else 1

    def _job_state_path(self, unit: CampaignWorkUnit) -> Path:
        return self.state_dir / "jobs" / f"{unit.work_id}.json.gz"

    def _result_path(self, unit: CampaignWorkUnit, kind: str) -> Path:
        return self.state_dir / "results" / f"{unit.work_id}.{kind}.json.gz"

    def _next_unfinished(self) -> Optional[CampaignWorkUnit]:
        return self._work_unit(self.next_ordinal)

    def advance_quantum(
        self,
        max_steps: int,
        max_seconds: Optional[float] = None,
    ) -> Optional[dict[str, Any]]:
        if max_steps <= 0:
            raise ValueError("quantum max_steps must be positive")
        if self.terminal_lower is not None:
            return self.terminal_lower
        unit = self._next_unfinished()
        if unit is None:
            return None
        candidate = self.candidates[unit.candidate_index]
        state_path = self._job_state_path(unit)
        state = read_json(state_path) if state_path.exists() else None
        if self.active_resolver is not None:
            raise AssertionError("campaign attempted to load two resident resolvers")
        resolver = self.resolver_factory(
            candidate.reward, unit.epsilon, self.descriptor.alpha, state
        )
        # Restoring constructs independent exact search objects.  Drop the
        # decoded checkpoint tree before the next quantum so it does not
        # coexist with the live proof state for the duration of the search.
        del state
        self.active_resolver = resolver
        self.peak_resident_resolvers = max(
            self.peak_resident_resolvers, self.resident_resolver_count
        )
        before = int(getattr(resolver, "steps", 0))
        try:
            result = resolver.run(max_steps=max_steps, max_seconds=max_seconds)
            after = int(getattr(resolver, "steps", before))
            self.exact_steps += max(0, after - before)
            lower = getattr(resolver, "lower", None)
            upper = getattr(resolver, "upper", None)
            self.last_resolver_stats = {
                "work_id": unit.work_id,
                "resolver_steps": after,
                "lower_nodes": len(getattr(lower, "nodes", ())),
                "lower_pending": len(getattr(lower, "stack", ())),
                "upper_diagonal": getattr(upper, "diagonal", None),
                "upper_clock": (
                    None if upper is None else getattr(upper, "pair_offset", -1) + 1
                ),
                "upper_rank": (
                    None if upper is None else str(getattr(upper, "profile_rank", 0))
                ),
            }
            write_json_atomic(state_path, resolver.to_checkpoint_json())
        finally:
            self.active_resolver = None
        self.quanta += 1
        if result is None:
            return None

        certificate = result.certificate
        kind = str(result.kind)
        # A direct certificate rebuilds its problem independently during
        # verification. Release the completed resolver DAG first so the gate
        # never holds two full direct DAGs at once.
        del result, resolver, lower, upper
        gc.collect()
        if kind == "lower":
            if not isinstance(certificate, DirectHazardLowerTreeCertificate):
                raise TypeError("direct campaign lower result has the wrong type")
            global_lower = certificate.verify_positive_global()
        else:
            certificate.verify()
        result_path = self._result_path(unit, kind)
        write_json_atomic(result_path, certificate.to_json())
        relative_result_path = result_path.relative_to(self.state_dir)
        record = {
            "work_unit": unit.to_json(),
            "result_kind": kind,
            # Keep copied campaign directories portable across remote hosts.
            # Consumers reconstruct the absolute path from the active state_dir.
            "certificate_path": str(relative_result_path),
            "certificate_payload_sha256": certificate_digest(certificate),
        }
        if kind == "lower":
            # The scale contract is scalar arithmetic.  Do not instantiate a
            # second resolver here: that would build a second expression DAG
            # exactly when the completed one is at its largest.
            contract = ConfigurableDirectScaleContract(
                unit.epsilon, self.descriptor.alpha
            )
            if (
                certificate.level != contract.level
                or certificate.threshold != contract.lower_finite_threshold
                or global_lower != contract.certified_global_lower
            ):
                raise ValueError("campaign lower result violates its scale contract")
            robust = RobustGapCertificate.canonical(certificate)
            robust_path = self._result_path(unit, "robust-gap")
            write_json_atomic(robust_path, robust.to_json())
            record["robust_certificate_path"] = str(
                robust_path.relative_to(self.state_dir)
            )
            record["robust_certificate_payload_sha256"] = certificate_digest(
                robust
            )
            record["certified_eta_lower"] = qjson(certificate.global_lower)
            record["robust_reward_radius"] = qjson(robust.radius)
            record["robust_eta_lower"] = qjson(robust.gamma)
        self.completed[unit.work_id] = record
        state_path.unlink(missing_ok=True)
        if kind == "lower":
            self.terminal_lower = record
        else:
            self.next_ordinal += self.descriptor.shard_count
        return record

    def progress(self) -> dict[str, Any]:
        next_unit = self._next_unfinished()
        if self.descriptor.scale_limit is None:
            work_unit_count: Optional[int] = None
            unresolved: Optional[int] = None
        else:
            total = len(self.candidates) * self.descriptor.scale_limit
            first = self.descriptor.shard_index
            work_unit_count = (
                0 if first >= total else (total - 1 - first) // self.descriptor.shard_count + 1
            )
            unresolved = work_unit_count - len(self.completed)
        return {
            "campaign_id": self.descriptor.campaign_id,
            "shard": f"{self.descriptor.shard_index}/{self.descriptor.shard_count}",
            "candidate_count": len(self.candidates),
            "work_unit_count": work_unit_count,
            "completed_work_units": len(self.completed),
            "unresolved_work_units": unresolved,
            "quanta": self.quanta,
            "exact_steps": self.exact_steps,
            "resident_resolvers": self.resident_resolver_count,
            "peak_resident_resolvers": self.peak_resident_resolvers,
            "peak_rss_mib": _peak_rss_mib(),
            "last_resolver": self.last_resolver_stats,
            "next_work_unit": None if next_unit is None else next_unit.to_json(),
            "terminal_lower": self.terminal_lower,
            "claim_boundary": (
                "only a verified lower certificate proves a positive gap; "
                "profiles prove only their displayed bound; unfinished or "
                "exhausted campaign state has no conjecture-level conclusion"
            ),
        }

    def to_checkpoint_json(self) -> dict[str, Any]:
        if self.active_resolver is not None:
            raise ValueError("checkpoint only at a resolver quantum boundary")
        return {
            "kind": CAMPAIGN_KIND,
            "descriptor": self.descriptor.to_json(),
            "candidates": [candidate.to_json() for candidate in self.candidates],
            "state_dir": str(self.state_dir),
            "next_ordinal": str(self.next_ordinal),
            "quanta": self.quanta,
            "exact_steps": self.exact_steps,
            "completed": self.completed,
            "terminal_lower": self.terminal_lower,
            "peak_resident_resolvers": self.peak_resident_resolvers,
            "last_resolver_stats": self.last_resolver_stats,
        }

    def save(self, checkpoint: Path) -> None:
        write_json_atomic(checkpoint, self.to_checkpoint_json())

    @staticmethod
    def load(
        checkpoint: Path,
        state_dir: Optional[Path] = None,
        resolver_factory: ResolverFactory = default_resolver_factory,
    ) -> "CandidateCampaign":
        data = read_json(checkpoint)
        if data.get("kind") != CAMPAIGN_KIND:
            raise ValueError("wrong candidate campaign checkpoint kind")
        descriptor = CampaignDescriptor.from_json(data["descriptor"])
        candidates = tuple(
            Candidate(
                str(item["candidate_id"]),
                str(item["source"]),
                RewardTable.from_json(item["reward"]),
            )
            for item in data["candidates"]
        )
        for candidate, item in zip(candidates, data["candidates"]):
            if candidate.reward.digest != item["table_sha256"]:
                raise ValueError("candidate table hash mismatch")
        campaign = CandidateCampaign(
            candidates,
            descriptor,
            state_dir or Path(data["state_dir"]),
            resolver_factory,
        )
        campaign.next_ordinal = int(data["next_ordinal"])
        campaign.quanta = int(data["quanta"])
        campaign.exact_steps = int(data["exact_steps"])
        campaign.completed = {
            str(key): dict(value) for key, value in data.get("completed", {}).items()
        }
        raw_terminal_lower = data.get("terminal_lower")
        campaign.peak_resident_resolvers = int(
            data.get("peak_resident_resolvers", 0)
        )
        campaign.last_resolver_stats = dict(data.get("last_resolver_stats", {}))
        if (
            campaign.next_ordinal < 0
            or campaign.next_ordinal % descriptor.shard_count
            != descriptor.shard_index
        ):
            raise ValueError("campaign next ordinal lies outside its shard")
        for work_id, record in campaign.completed.items():
            unit_data = record.get("work_unit", {})
            ordinal = int(unit_data.get("ordinal", -1))
            if (
                ordinal < 0
                or ordinal % descriptor.shard_count != descriptor.shard_index
            ):
                raise ValueError("checkpoint contains a foreign completed work unit")
            unit = campaign._work_unit(ordinal)
            if unit is None or unit.to_json() != unit_data:
                raise ValueError("completed work-unit descriptor mismatch")
            if work_id != unit.work_id:
                raise ValueError("completed work-unit key mismatch")
            relative = Path(str(record["certificate_path"]))
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError("completed certificate path escapes state directory")
            payload = read_json(campaign.state_dir / relative)
            kind = payload.get("kind")
            if kind == PROFILE_KIND:
                certificate: Any = ProfileCertificate.from_json(payload)
            elif kind == DIRECT_LOWER_KIND:
                certificate = DirectHazardLowerTreeCertificate.from_json(payload)
            else:
                raise ValueError("unknown completed campaign certificate kind")
            if certificate.reward != campaign.candidates[unit.candidate_index].reward:
                raise ValueError("completed certificate has the wrong reward table")
            if certificate_digest(certificate) != record[
                "certificate_payload_sha256"
            ]:
                raise ValueError("completed certificate digest mismatch")
            if record["result_kind"] == "profile":
                if not isinstance(certificate, ProfileCertificate):
                    raise ValueError("profile result stores a lower certificate")
                certificate.verify()
                if certificate.epsilon != unit.epsilon:
                    raise ValueError("profile result has the wrong threshold")
            elif record["result_kind"] == "lower":
                if not isinstance(certificate, DirectHazardLowerTreeCertificate):
                    raise ValueError("lower result stores a profile certificate")
                contract = ConfigurableDirectScaleContract(
                    unit.epsilon, descriptor.alpha
                )
                global_lower = certificate.verify_positive_global()
                if (
                    certificate.level != contract.level
                    or certificate.threshold != contract.lower_finite_threshold
                    or global_lower != contract.certified_global_lower
                ):
                    raise ValueError(
                        "completed lower certificate violates its scale contract"
                    )
                robust_relative = Path(str(record["robust_certificate_path"]))
                if robust_relative.is_absolute() or ".." in robust_relative.parts:
                    raise ValueError("robust certificate path escapes state directory")
                robust = RobustGapCertificate.from_json(
                    read_json(campaign.state_dir / robust_relative)
                )
                if robust != RobustGapCertificate.canonical(certificate):
                    raise ValueError(
                        "robust certificate is not the canonical wrapper of "
                        "the completed lower certificate"
                    )
                if certificate_digest(robust) != record[
                    "robust_certificate_payload_sha256"
                ]:
                    raise ValueError("robust certificate digest mismatch")
                if (
                    record.get("certified_eta_lower") != qjson(global_lower)
                    or record.get("robust_reward_radius") != qjson(robust.radius)
                    or record.get("robust_eta_lower") != qjson(robust.gamma)
                ):
                    raise ValueError("completed lower summary does not match certificates")
            else:
                raise ValueError("unknown completed campaign result kind")
        lower_records = [
            record
            for record in campaign.completed.values()
            if record.get("result_kind") == "lower"
        ]
        if len(lower_records) > 1:
            raise ValueError("campaign checkpoint contains multiple terminal lowers")
        if lower_records:
            if raw_terminal_lower != lower_records[0]:
                raise ValueError(
                    "terminal lower does not identify the verified completed lower"
                )
            campaign.terminal_lower = lower_records[0]
        elif raw_terminal_lower is not None:
            raise ValueError("terminal lower has no verified completed lower record")
        return campaign

    def progress_line(self, elapsed: float) -> str:
        progress = self.progress()
        unit = progress["next_work_unit"]
        stats = progress["last_resolver"]
        if unit is None:
            location = "work=complete"
        else:
            location = (
                f"candidate={unit['candidate_id']} scale={unit['scale_index']} "
                f"epsilon={unit['epsilon']}"
            )
        return (
            f"progress {location} exact_steps={progress['exact_steps']} "
            f"lower_nodes={stats.get('lower_nodes', 0)} "
            f"lower_pending={stats.get('lower_pending', 0)} "
            f"upper_diagonal={stats.get('upper_diagonal')} "
            f"peak_rss_mib={progress['peak_rss_mib']} elapsed_s={elapsed:.1f}"
        )

    def run(
        self,
        quantum_steps: int,
        max_quanta: Optional[int] = None,
        max_seconds: Optional[float] = None,
        checkpoint: Optional[Path] = None,
        report_every: int = 1,
    ) -> Optional[dict[str, Any]]:
        if report_every <= 0:
            raise ValueError("report_every must be positive")
        started = time.monotonic()
        local_quanta = 0
        while max_quanta is None or local_quanta < max_quanta:
            elapsed = time.monotonic() - started
            if max_seconds is not None and elapsed >= max_seconds:
                break
            if self.terminal_lower is not None or self._next_unfinished() is None:
                break
            remaining = None if max_seconds is None else max(0.0, max_seconds - elapsed)
            result = self.advance_quantum(quantum_steps, remaining)
            local_quanta += 1
            if checkpoint is not None:
                self.save(checkpoint)
            if local_quanta % report_every == 0:
                print(self.progress_line(time.monotonic() - started), flush=True)
            if result is not None and result["result_kind"] == "lower":
                return result
        if checkpoint is not None:
            self.save(checkpoint)
        return self.terminal_lower
