from __future__ import annotations

from dataclasses import dataclass
from contextlib import redirect_stdout
from fractions import Fraction
import io
from pathlib import Path
import tempfile
import unittest
from typing import Any, Mapping, Optional

from fin4_exact_search.candidate_campaign import (
    CampaignDescriptor,
    CandidateCampaign,
    load_tracked_candidates,
)
from fin4_exact_search.engine import (
    RewardTable,
    read_json,
    write_json_atomic,
)
from fin4_exact_search.cli import main as cli_main


@dataclass(frozen=True)
class FakeCertificate:
    reward: RewardTable
    epsilon: Fraction

    def verify(self) -> None:
        self.reward.validate_normalized()

    def to_json(self) -> dict[str, Any]:
        return {
            "kind": "fake-profile-for-campaign-test",
            "reward": self.reward.to_json(),
            "epsilon": str(self.epsilon),
        }


@dataclass(frozen=True)
class FakeResult:
    kind: str
    certificate: FakeCertificate


class FakeResolver:
    def __init__(self, reward: RewardTable, epsilon: Fraction, steps: int = 0) -> None:
        self.reward = reward
        self.epsilon = epsilon
        self.steps = steps

    def run(
        self,
        max_steps: Optional[int] = None,
        max_seconds: Optional[float] = None,
    ) -> Optional[FakeResult]:
        del max_seconds
        amount = 1 if max_steps is None else max_steps
        self.steps += amount
        if self.steps >= 3:
            certificate = FakeCertificate(self.reward, self.epsilon)
            return FakeResult("profile", certificate)
        return None

    def to_checkpoint_json(self) -> dict[str, Any]:
        return {
            "kind": "fake-resolver",
            "reward": self.reward.to_json(),
            "epsilon": str(self.epsilon),
            "steps": self.steps,
        }


def fake_factory(
    reward: RewardTable,
    epsilon: Fraction,
    alpha: Fraction,
    state: Optional[Mapping[str, Any]],
) -> FakeResolver:
    if alpha != Fraction(1, 2):
        raise ValueError("unexpected fake alpha")
    if state is None:
        return FakeResolver(reward, epsilon)
    if state.get("kind") != "fake-resolver":
        raise ValueError("wrong fake resolver state")
    restored = RewardTable.from_json(state["reward"])
    if restored != reward or Fraction(state["epsilon"]) != epsilon:
        raise ValueError("fake resolver work-unit mismatch")
    return FakeResolver(reward, epsilon, int(state["steps"]))


class NeverResolver(FakeResolver):
    def run(
        self,
        max_steps: Optional[int] = None,
        max_seconds: Optional[float] = None,
    ) -> None:
        del max_seconds
        self.steps += 1 if max_steps is None else max_steps
        return None


def never_factory(
    reward: RewardTable,
    epsilon: Fraction,
    alpha: Fraction,
    state: Optional[Mapping[str, Any]],
) -> NeverResolver:
    if alpha != Fraction(1, 2):
        raise ValueError("unexpected fake alpha")
    if state is None:
        return NeverResolver(reward, epsilon)
    return NeverResolver(reward, epsilon, int(state["steps"]))


class CandidateCampaignTests(unittest.TestCase):
    def test_tracked_candidates_are_deterministic_and_normalized(self) -> None:
        first = load_tracked_candidates()
        second = load_tracked_candidates()
        self.assertEqual(
            [(candidate.candidate_id, candidate.reward.digest) for candidate in first],
            [(candidate.candidate_id, candidate.reward.digest) for candidate in second],
        )
        self.assertGreaterEqual(len(first), 1)
        self.assertTrue(all(candidate.reward.normalized for candidate in first))

    def test_fallback_candidate_is_self_contained(self) -> None:
        missing = Path("/definitely/missing/fin4-candidate-results.json")
        candidates = load_tracked_candidates(missing)
        self.assertEqual(len(candidates), 1)
        self.assertEqual(candidates[0].source, "embedded-exact-fallback")

    def test_one_resident_job_and_checkpoint_resume(self) -> None:
        candidates = load_tracked_candidates()[:2]
        descriptor = CampaignDescriptor.create(
            candidates,
            start_epsilon=Fraction(4),
            refinement=Fraction(2),
            scale_limit=2,
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            state_dir = root / "state"
            checkpoint = root / "campaign.json.gz"
            campaign = CandidateCampaign(
                candidates, descriptor, state_dir, fake_factory
            )
            self.assertIsNone(campaign.advance_quantum(2))
            self.assertEqual(campaign.resident_resolver_count, 0)
            self.assertEqual(campaign.peak_resident_resolvers, 1)
            campaign.save(checkpoint)

            resumed = CandidateCampaign.load(checkpoint, state_dir, fake_factory)
            self.assertEqual(resumed.resident_resolver_count, 0)
            # The current exact work unit remains current until resolution.
            result = resumed.advance_quantum(1)
            self.assertIsNotNone(result)
            assert result is not None
            self.assertEqual(result["result_kind"], "profile")
            self.assertFalse(Path(result["certificate_path"]).is_absolute())
            self.assertEqual(resumed.resident_resolver_count, 0)
            self.assertEqual(resumed.peak_resident_resolvers, 1)
            self.assertEqual(len(resumed.completed), 1)

    def test_shards_partition_work_units(self) -> None:
        candidates = load_tracked_candidates()[:2]
        left_descriptor = CampaignDescriptor.create(
            candidates, scale_limit=3, shard_count=2, shard_index=0
        )
        right_descriptor = CampaignDescriptor.create(
            candidates, scale_limit=3, shard_count=2, shard_index=1
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            left = CandidateCampaign(candidates, left_descriptor, root / "left")
            right = CandidateCampaign(candidates, right_descriptor, root / "right")
            left_ordinals = {unit.ordinal for unit in left.preview_work_units(3)}
            right_ordinals = {unit.ordinal for unit in right.preview_work_units(3)}
            self.assertFalse(left_ordinals & right_ordinals)
            self.assertEqual(left_ordinals | right_ordinals, set(range(6)))

    def test_unbounded_schedule_stays_scale_major(self) -> None:
        candidates = load_tracked_candidates()[:2]
        descriptor = CampaignDescriptor.create(candidates, scale_limit=None)
        with tempfile.TemporaryDirectory() as directory:
            campaign = CandidateCampaign(
                candidates, descriptor, Path(directory), fake_factory
            )
            preview = campaign.preview_work_units(6)
            self.assertEqual(
                [(unit.candidate_index, unit.scale_index) for unit in preview],
                [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2)],
            )
            self.assertIsNone(campaign.progress()["work_unit_count"])

    def test_clean_command_starts_and_auto_resumes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            work_dir = Path(directory) / "discovery"
            arguments = [
                "discover",
                "--work-dir",
                str(work_dir),
                "--start-epsilon",
                "100",
                "--quantum-steps",
                "2",
                "--max-quanta",
                "1",
            ]
            with redirect_stdout(io.StringIO()):
                self.assertEqual(cli_main(arguments), 2)
            first = CandidateCampaign.load(
                work_dir / "campaign.checkpoint.json.gz",
                work_dir / "state",
            )
            self.assertEqual(first.next_ordinal, 1)
            self.assertEqual(first.peak_resident_resolvers, 1)
            with redirect_stdout(io.StringIO()):
                self.assertEqual(cli_main(arguments), 2)
            second = CandidateCampaign.load(
                work_dir / "campaign.checkpoint.json.gz",
                work_dir / "state",
            )
            self.assertEqual(second.next_ordinal, 2)
            self.assertEqual(second.peak_resident_resolvers, 1)

    def test_resume_rejects_unverified_terminal_lower_summary(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            work_dir = Path(directory) / "discovery"
            arguments = [
                "discover",
                "--work-dir",
                str(work_dir),
                "--start-epsilon",
                "100",
                "--quantum-steps",
                "2",
                "--max-quanta",
                "1",
            ]
            with redirect_stdout(io.StringIO()):
                self.assertEqual(cli_main(arguments), 2)
            checkpoint = work_dir / "campaign.checkpoint.json.gz"
            payload = read_json(checkpoint)
            payload["terminal_lower"] = {
                "result_kind": "lower",
                "forged": True,
            }
            write_json_atomic(checkpoint, payload)
            with self.assertRaisesRegex(ValueError, "terminal lower"):
                CandidateCampaign.load(checkpoint, work_dir / "state")

    def test_unresolved_run_overwrites_one_job_state(self) -> None:
        candidates = load_tracked_candidates()[:2]
        descriptor = CampaignDescriptor.create(candidates)
        with tempfile.TemporaryDirectory() as directory:
            state_dir = Path(directory) / "state"
            campaign = CandidateCampaign(
                candidates, descriptor, state_dir, never_factory
            )
            for _ in range(50):
                self.assertIsNone(campaign.advance_quantum(1))
            self.assertEqual(campaign.next_ordinal, 0)
            self.assertEqual(campaign.resident_resolver_count, 0)
            self.assertEqual(campaign.peak_resident_resolvers, 1)
            self.assertEqual(len(campaign.completed), 0)
            self.assertEqual(len(list((state_dir / "jobs").glob("*.json.gz"))), 1)


if __name__ == "__main__":
    unittest.main()
