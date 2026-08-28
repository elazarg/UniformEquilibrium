"""Command-line interface for the exact Fin4 search experiment."""

from __future__ import annotations

import argparse
from pathlib import Path
from hashlib import sha256
import sys
import time
from typing import Any, Mapping, Optional, Sequence

from .engine import (
    CHECKPOINT_KIND,
    HeuristicSearch,
    LowerSearch,
    LowerTreeCertificate,
    ProfileCertificate,
    Q,
    RewardTable,
    ScaleContract,
    ScaleSearch,
    UpperSearch,
    WorkRegion,
    build_outer_problem,
    canonical_lower_partition,
    certificate_digest,
    load_reward_table,
    make_region,
    merge_lower_region_certificates,
    prefix_from_json,
    qjson,
    read_json,
    verify_certificate_file,
    write_json_atomic,
)


REGION_CHECKPOINT_KIND = "fin4-exact-region-checkpoint-v1"
BATCH_KIND = "fin4-exact-search-batch-v1"
CAMPAIGN_CHECKPOINT_KIND = "fin4-exact-dyadic-campaign-v1"


def _write_certificate(path: Path, certificate: Any) -> None:
    certificate.verify()
    write_json_atomic(path, certificate.to_json())
    file_sha256 = sha256(path.read_bytes()).hexdigest()
    print(
        f"wrote {path} payload_sha256={certificate_digest(certificate)} "
        f"file_sha256={file_sha256}"
    )


def _load_or_create_search(
    table_path: Path,
    epsilon: str,
    checkpoint: Optional[Path],
    resume: bool,
) -> ScaleSearch:
    reward = load_reward_table(table_path)
    if resume:
        if checkpoint is None or not checkpoint.exists():
            raise ValueError("--resume needs an existing --checkpoint")
        search = ScaleSearch.from_checkpoint_json(read_json(checkpoint))
        if search.reward != reward:
            raise ValueError("checkpoint and supplied table disagree")
        if search.contract.epsilon != Q(epsilon):
            raise ValueError("checkpoint and supplied epsilon disagree")
        return search
    return ScaleSearch(reward, Q(epsilon))


def command_search(args: argparse.Namespace) -> int:
    if args.checkpoint_every <= 0:
        raise ValueError("--checkpoint-every must be positive")
    search = _load_or_create_search(
        args.table, args.epsilon, args.checkpoint, args.resume
    )
    result = search.run(
        max_steps=args.max_steps,
        max_seconds=args.max_seconds,
        checkpoint_path=args.checkpoint,
        checkpoint_every=args.checkpoint_every,
    )
    if result is None:
        print(
            "search incomplete; exact checkpoint saved"
            if args.checkpoint
            else "search incomplete; no mathematical conclusion"
        )
        print(
            f"steps={search.steps} lower_steps={search.lower.steps} "
            f"upper_steps={search.upper.steps}"
        )
        return 2
    output = args.output or Path(f"{result.kind}-certificate.json")
    _write_certificate(output, result.certificate)
    print(f"resolved={result.kind} total_steps={search.steps}")
    return 0


def _campaign_progress(
    search: ScaleSearch,
    scale_index: int,
    elapsed: float,
    label: str = "progress",
) -> None:
    upper_clock = search.upper.pair_offset + 1
    print(
        f"{label} scale={scale_index} epsilon={qjson(search.contract.epsilon)} "
        f"level={search.contract.level} steps={search.steps} "
        f"lower_nodes={len(search.lower.nodes)} "
        f"lower_pending={len(search.lower.stack)} "
        f"upper_diagonal={search.upper.diagonal} upper_clock={upper_clock} "
        f"upper_rank={search.upper.profile_rank} elapsed_s={elapsed:.1f}",
        flush=True,
    )


def _campaign_build_notice(epsilon: Any, scale_index: int, label: str) -> None:
    contract = ScaleContract.create(epsilon)
    print(
        f"{label} scale={scale_index} epsilon={qjson(contract.epsilon)} "
        f"level={contract.level} lower_target={qjson(contract.lower_gamma)} "
        f"upper_target={qjson(contract.upper_target)}",
        flush=True,
    )


def _campaign_payload(
    reward: RewardTable,
    start_epsilon: Any,
    refinement: Any,
    scale_index: int,
    completed: Sequence[Mapping[str, Any]],
    status: str,
    search: Optional[ScaleSearch],
    result: Optional[Mapping[str, Any]] = None,
) -> dict[str, Any]:
    return {
        "kind": CAMPAIGN_CHECKPOINT_KIND,
        "reward": reward.to_json(),
        "table_sha256": reward.digest,
        "start_epsilon": qjson(start_epsilon),
        "refinement": qjson(refinement),
        "scale_index": scale_index,
        "completed": list(completed),
        "status": status,
        "scale_search": None if search is None else search.to_checkpoint_json(),
        "result": None if result is None else dict(result),
    }


def _verify_campaign_history(
    work_dir: Path,
    reward: RewardTable,
    start_epsilon: Any,
    refinement: Any,
    completed: Sequence[Mapping[str, Any]],
) -> None:
    for expected_index, item in enumerate(completed):
        if int(item["scale_index"]) != expected_index:
            raise ValueError("campaign profile history has a noncanonical scale index")
        expected_epsilon = start_epsilon / refinement**expected_index
        if Q(item["epsilon"]) != expected_epsilon:
            raise ValueError("campaign profile history has the wrong epsilon")
        path = work_dir / str(item["certificate"])
        certificate = ProfileCertificate.from_json(read_json(path))
        certificate.verify()
        if certificate.reward != reward:
            raise ValueError("campaign profile certificate has the wrong table")
        if certificate.epsilon != 3 * expected_epsilon / 4:
            raise ValueError("campaign profile certificate has the wrong target")
        if certificate_digest(certificate) != item["payload_sha256"]:
            raise ValueError("campaign profile certificate digest mismatch")


def _verify_campaign_terminal_result(
    work_dir: Path,
    reward: RewardTable,
    start_epsilon: Any,
    refinement: Any,
    scale_index: int,
    status: str,
    result: Any,
) -> None:
    if status == "requested-scales-complete":
        if result is not None:
            raise ValueError("profile-only campaign has an unexpected final result")
        return
    if status != "positive-gap":
        raise ValueError(f"unknown campaign status {status!r}")
    if not isinstance(result, Mapping) or result.get("kind") != "positive-gap":
        raise ValueError("positive-gap campaign has no result record")
    expected_epsilon = start_epsilon / refinement**scale_index
    if Q(result["epsilon"]) != expected_epsilon:
        raise ValueError("campaign lower result has the wrong epsilon")
    path = work_dir / str(result["certificate"])
    certificate = LowerTreeCertificate.from_json(read_json(path))
    certificate.verify()
    contract = ScaleContract.create(expected_epsilon)
    if (
        not certificate.is_global
        or certificate.reward != reward
        or certificate.level != contract.level
        or certificate.gamma != contract.lower_gamma
    ):
        raise ValueError("campaign lower certificate does not match its scale")
    if certificate_digest(certificate) != result["payload_sha256"]:
        raise ValueError("campaign lower certificate digest mismatch")
    if Q(result["eta_lower_bound"]) != contract.lower_gamma:
        raise ValueError("campaign lower-bound summary mismatch")
    if Q(result["deviation_threshold"]) != contract.lower_gamma / 2:
        raise ValueError("campaign deviation-threshold summary mismatch")


def command_campaign(args: argparse.Namespace) -> int:
    """Run a resumable coarse-to-fine sequence of exact scale searches."""
    if args.checkpoint_every <= 0:
        raise ValueError("--checkpoint-every must be positive")
    if args.report_every <= 0:
        raise ValueError("--report-every must be positive")
    if args.report_seconds <= 0:
        raise ValueError("--report-seconds must be positive")
    if args.stop_after_scales is not None and args.stop_after_scales <= 0:
        raise ValueError("--stop-after-scales must be positive")

    reward = load_reward_table(args.table)
    start_epsilon = Q(args.start_epsilon)
    refinement = Q(args.refinement)
    if start_epsilon <= 0:
        raise ValueError("--start-epsilon must be positive")
    if refinement <= 1:
        raise ValueError("--refinement must be greater than one")

    work_dir = args.work_dir.resolve()
    work_dir.mkdir(parents=True, exist_ok=True)
    checkpoint = work_dir / "campaign.checkpoint.json.gz"
    summary = work_dir / "campaign.summary.json"

    if args.resume:
        if not checkpoint.exists():
            raise ValueError("--resume needs campaign.checkpoint.json.gz")
        data = read_json(checkpoint)
        if data.get("kind") != CAMPAIGN_CHECKPOINT_KIND:
            raise ValueError("wrong campaign checkpoint kind")
        if data.get("table_sha256") != reward.digest:
            raise ValueError("campaign checkpoint and supplied table disagree")
        if RewardTable.from_json(data["reward"]) != reward:
            raise ValueError("campaign checkpoint contains a different table")
        if Q(data["start_epsilon"]) != start_epsilon:
            raise ValueError("campaign checkpoint and --start-epsilon disagree")
        if Q(data["refinement"]) != refinement:
            raise ValueError("campaign checkpoint and --refinement disagree")
        completed = list(data.get("completed", []))
        scale_index = int(data["scale_index"])
        if scale_index != len(completed):
            raise ValueError("campaign checkpoint history length mismatch")
        _verify_campaign_history(
            work_dir, reward, start_epsilon, refinement, completed
        )
        status = str(data.get("status", "running"))
        if status != "running":
            _verify_campaign_terminal_result(
                work_dir,
                reward,
                start_epsilon,
                refinement,
                scale_index,
                status,
                data.get("result"),
            )
            print(
                f"campaign already complete status={status} "
                f"scales={len(completed)} summary={summary}"
            )
            return 0
        if data.get("scale_search") is None:
            raise ValueError("running campaign has no per-scale checkpoint")
        expected_epsilon = start_epsilon / refinement**scale_index
        _campaign_build_notice(expected_epsilon, scale_index, "loading-scale")
        search = ScaleSearch.from_checkpoint_json(data["scale_search"])
        if search.reward != reward or search.contract.epsilon != expected_epsilon:
            raise ValueError("campaign per-scale checkpoint mismatch")
    else:
        if checkpoint.exists() or summary.exists():
            raise ValueError("campaign state already exists; use --resume")
        if any(work_dir.glob("scale-*-profile.certificate.json.gz")):
            raise ValueError("campaign work directory contains profile certificates")
        completed = []
        scale_index = 0
        _campaign_build_notice(start_epsilon, scale_index, "building-scale")
        search = ScaleSearch(reward, start_epsilon)

    started = time.monotonic()
    last_report = started
    local_steps = 0
    _campaign_progress(search, scale_index, 0, label="scale-start")

    try:
        while True:
            elapsed = time.monotonic() - started
            if args.max_steps is not None and local_steps >= args.max_steps:
                break
            if args.max_seconds is not None and elapsed >= args.max_seconds:
                break

            result = search.step()
            local_steps += 1
            now = time.monotonic()
            if local_steps % args.checkpoint_every == 0:
                write_json_atomic(
                    checkpoint,
                    _campaign_payload(
                        reward,
                        start_epsilon,
                        refinement,
                        scale_index,
                        completed,
                        "running",
                        search,
                    ),
                )
            if (
                local_steps % args.report_every == 0
                or now - last_report >= args.report_seconds
            ):
                _campaign_progress(search, scale_index, now - started)
                last_report = now

            if result is None:
                continue

            epsilon = search.contract.epsilon
            if result.kind == "lower":
                assert isinstance(result.certificate, LowerTreeCertificate)
                output = work_dir / f"scale-{scale_index:04d}-lower.certificate.json.gz"
                _write_certificate(output, result.certificate)
                result_record = {
                    "kind": "positive-gap",
                    "scale_index": scale_index,
                    "epsilon": qjson(epsilon),
                    "eta_lower_bound": qjson(search.contract.lower_gamma),
                    "deviation_threshold": qjson(search.contract.lower_gamma / 2),
                    "certificate": output.name,
                    "payload_sha256": certificate_digest(result.certificate),
                }
                payload = _campaign_payload(
                    reward,
                    start_epsilon,
                    refinement,
                    scale_index,
                    completed,
                    "positive-gap",
                    None,
                    result_record,
                )
                write_json_atomic(checkpoint, payload)
                write_json_atomic(summary, payload)
                print(
                    "positive-gap-certified "
                    f"scale={scale_index} eta_lower_bound="
                    f"{qjson(search.contract.lower_gamma)} "
                    f"deviation_threshold={qjson(search.contract.lower_gamma / 2)} "
                    f"certificate={output}",
                    flush=True,
                )
                return 0

            output = work_dir / f"scale-{scale_index:04d}-profile.certificate.json.gz"
            _write_certificate(output, result.certificate)
            assert isinstance(result.certificate, ProfileCertificate)
            completed.append(
                {
                    "scale_index": scale_index,
                    "epsilon": qjson(epsilon),
                    "exploitability": qjson(result.certificate.exploitability),
                    "target": qjson(search.contract.upper_target),
                    "certificate": output.name,
                    "payload_sha256": certificate_digest(result.certificate),
                }
            )
            print(
                f"profile-certified scale={scale_index} epsilon={qjson(epsilon)} "
                f"exploitability={qjson(result.certificate.exploitability)} "
                f"target={qjson(search.contract.upper_target)} certificate={output}",
                flush=True,
            )
            scale_index += 1
            if (
                args.stop_after_scales is not None
                and scale_index >= args.stop_after_scales
            ):
                payload = _campaign_payload(
                    reward,
                    start_epsilon,
                    refinement,
                    scale_index,
                    completed,
                    "requested-scales-complete",
                    None,
                )
                write_json_atomic(checkpoint, payload)
                write_json_atomic(summary, payload)
                print(
                    f"campaign-target-reached scales={scale_index}; "
                    "profile sequence certified, but no zero-gap conclusion",
                    flush=True,
                )
                return 0

            next_epsilon = start_epsilon / refinement**scale_index
            _campaign_build_notice(next_epsilon, scale_index, "building-scale")
            search = ScaleSearch(reward, next_epsilon)
            write_json_atomic(
                checkpoint,
                _campaign_payload(
                    reward,
                    start_epsilon,
                    refinement,
                    scale_index,
                    completed,
                    "running",
                    search,
                ),
            )
            _campaign_progress(
                search, scale_index, time.monotonic() - started, label="scale-start"
            )
    except KeyboardInterrupt:
        write_json_atomic(
            checkpoint,
            _campaign_payload(
                reward,
                start_epsilon,
                refinement,
                scale_index,
                completed,
                "running",
                search,
            ),
        )
        print(f"campaign interrupted; checkpoint={checkpoint}", flush=True)
        return 130

    write_json_atomic(
        checkpoint,
        _campaign_payload(
            reward,
            start_epsilon,
            refinement,
            scale_index,
            completed,
            "running",
            search,
        ),
    )
    _campaign_progress(
        search, scale_index, time.monotonic() - started, label="paused"
    )
    print(f"no mathematical conclusion; resume checkpoint={checkpoint}", flush=True)
    return 2


def command_region(args: argparse.Namespace) -> int:
    reward = load_reward_table(args.table)
    parameters: dict[str, Any] = {}
    if args.kind == "lower":
        if args.prefix:
            parameters["prefix"] = read_json(args.prefix)
        else:
            parameters["prefix"] = []
    elif args.kind == "upper":
        if args.diagonal_end is None:
            raise ValueError("upper region requires --diagonal-end")
        parameters = {
            "diagonal_start": args.diagonal_start,
            "diagonal_end": args.diagonal_end,
        }
    elif args.kind == "heuristic":
        if args.seed_end is None:
            raise ValueError("heuristic region requires --seed-end")
        parameters = {
            "algorithm": "stationary-grid-v1",
            "seed_start": args.seed_start,
            "seed_end": args.seed_end,
        }
    region = make_region(reward, Q(args.epsilon), args.kind, parameters)
    if args.output:
        write_json_atomic(args.output, region.to_json())
        print(
            f"wrote {args.output} region_id={region.region_id} "
            f"descriptor_sha256={region.descriptor_sha256}"
        )
    else:
        print_json(region.to_json())
    return 0


def print_json(data: Any) -> None:
    import json

    print(json.dumps(data, sort_keys=True, indent=2))


def command_partition_lower(args: argparse.Namespace) -> int:
    reward = load_reward_table(args.table)
    epsilon = Q(args.epsilon)
    base_prefix = prefix_from_json(read_json(args.prefix)) if args.prefix else tuple()
    regions = canonical_lower_partition(
        reward, epsilon, args.depth, base_prefix=base_prefix
    )
    payload = {
        "schema": "fin4-exact-lower-partition-v1",
        "table_sha256": reward.digest,
        "epsilon": qjson(epsilon),
        "depth": args.depth,
        "regions": [region.to_json() for region in regions],
    }
    write_json_atomic(args.output, payload)
    if args.regions_dir:
        args.regions_dir.mkdir(parents=True, exist_ok=True)
        for region in regions:
            write_json_atomic(
                args.regions_dir / f"{region.region_id}.json", region.to_json()
            )
    print(f"wrote {args.output} with {len(regions)} disjoint lower regions")
    return 0


def _region_checkpoint(
    region: WorkRegion,
    search_kind: str,
    state: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "kind": REGION_CHECKPOINT_KIND,
        "region": region.to_json(),
        "search_kind": search_kind,
        "state": state,
    }


def command_scan_region(args: argparse.Namespace) -> int:
    if args.checkpoint_every <= 0:
        raise ValueError("--checkpoint-every must be positive")
    reward = load_reward_table(args.table)
    region = WorkRegion.from_json(read_json(args.region))
    region.verify_for(reward)
    contract = ScaleContract.create(region.epsilon)
    checkpoint_data = None
    if args.resume:
        if args.checkpoint is None or not args.checkpoint.exists():
            raise ValueError("--resume needs an existing --checkpoint")
        checkpoint_data = read_json(args.checkpoint)
        if checkpoint_data.get("kind") != REGION_CHECKPOINT_KIND:
            raise ValueError("wrong regional checkpoint kind")
        old_region = WorkRegion.from_json(checkpoint_data["region"])
        if old_region != region:
            raise ValueError("regional checkpoint descriptor mismatch")
        if checkpoint_data.get("search_kind") != region.work_kind:
            raise ValueError("regional checkpoint search kind mismatch")

    started = time.monotonic()
    steps = 0
    result: Optional[LowerTreeCertificate | ProfileCertificate] = None
    exhausted = False
    if region.work_kind == "lower":
        problem = build_outer_problem(reward, contract.level)
        if checkpoint_data:
            search = LowerSearch.from_state_json(problem, checkpoint_data["state"])
        else:
            prefix = prefix_from_json(region.parameters.get("prefix", []))
            search = LowerSearch(problem, contract.lower_gamma, prefix)
        expected_prefix = prefix_from_json(region.parameters.get("prefix", []))
        if search.gamma != contract.lower_gamma or search.prefix != expected_prefix:
            raise ValueError("lower checkpoint does not match its region")
        while args.max_steps is None or steps < args.max_steps:
            if args.max_seconds is not None and time.monotonic() - started >= args.max_seconds:
                break
            result = search.step()
            steps += 1
            if result is not None:
                break
            if args.checkpoint and steps % args.checkpoint_every == 0:
                write_json_atomic(
                    args.checkpoint,
                    _region_checkpoint(region, "lower", search.to_state_json()),
                )
        state = search.to_state_json()
    elif region.work_kind == "upper":
        if checkpoint_data:
            search = UpperSearch.from_state_json(reward, checkpoint_data["state"])
        else:
            search = UpperSearch(
                reward,
                contract.upper_target,
                int(region.parameters["diagonal_start"]),
                int(region.parameters["diagonal_end"]),
            )
        if (
            search.target != contract.upper_target
            or search.diagonal_end != int(region.parameters["diagonal_end"])
            or search.diagonal < int(region.parameters["diagonal_start"])
        ):
            raise ValueError("upper checkpoint does not match its region")
        while args.max_steps is None or steps < args.max_steps:
            if args.max_seconds is not None and time.monotonic() - started >= args.max_seconds:
                break
            result = search.step()
            steps += 1
            if result is not None or search.exhausted:
                break
            if args.checkpoint and steps % args.checkpoint_every == 0:
                write_json_atomic(
                    args.checkpoint,
                    _region_checkpoint(region, "upper", search.to_state_json()),
                )
        exhausted = search.exhausted
        state = search.to_state_json()
    elif region.work_kind == "heuristic":
        start = int(region.parameters["seed_start"])
        end = int(region.parameters["seed_end"])
        if checkpoint_data:
            start = int(checkpoint_data["state"]["seed"])
        if not int(region.parameters["seed_start"]) <= start <= end:
            raise ValueError("heuristic checkpoint does not match its region")
        search = HeuristicSearch(reward, contract.upper_target, start, end)
        while args.max_steps is None or steps < args.max_steps:
            if args.max_seconds is not None and time.monotonic() - started >= args.max_seconds:
                break
            if search.seed >= search.seed_end:
                exhausted = True
                break
            result = search.step()
            steps += 1
            if result is not None:
                break
        state = {"seed": search.seed, "seed_end": search.seed_end}
    elif region.work_kind == "full":
        if checkpoint_data:
            search = ScaleSearch.from_checkpoint_json(checkpoint_data["state"])
            if search.reward != reward or search.contract.epsilon != region.epsilon:
                raise ValueError("full checkpoint does not match its region")
        else:
            search = ScaleSearch(reward, region.epsilon)
        while args.max_steps is None or steps < args.max_steps:
            if args.max_seconds is not None and time.monotonic() - started >= args.max_seconds:
                break
            scale_result = search.step()
            steps += 1
            if scale_result is not None:
                result = scale_result.certificate
                break
            if args.checkpoint and steps % args.checkpoint_every == 0:
                write_json_atomic(
                    args.checkpoint,
                    _region_checkpoint(region, "full", search.to_checkpoint_json()),
                )
        state = search.to_checkpoint_json()
    else:
        raise ValueError("unknown regional search kind")

    if args.checkpoint:
        write_json_atomic(
            args.checkpoint,
            _region_checkpoint(region, region.work_kind, state),
        )
    if result is not None:
        output = args.output or Path(f"{region.region_id}-certificate.json")
        _write_certificate(output, result)
        return 0
    status = "exhausted without certificate" if exhausted else "incomplete"
    print(f"region {region.region_id}: {status}; no mathematical conclusion")
    return 3 if exhausted else 2


def command_merge_lower(args: argparse.Namespace) -> int:
    certificates = [
        LowerTreeCertificate.from_json(read_json(path)) for path in args.certificates
    ]
    result = merge_lower_region_certificates(certificates)
    if not result.is_global:
        raise AssertionError("merge did not produce a global certificate")
    _write_certificate(args.output, result)
    return 0


def command_batch(args: argparse.Namespace) -> int:
    if args.checkpoint_every <= 0:
        raise ValueError("--checkpoint-every must be positive")
    manifest_path = args.manifest.resolve()
    manifest = read_json(manifest_path)
    if manifest.get("schema") != BATCH_KIND:
        raise ValueError("wrong batch manifest schema")
    work_dir = args.work_dir.resolve()
    work_dir.mkdir(parents=True, exist_ok=True)
    failures = 0
    for job in manifest["jobs"]:
        job_id = str(job["id"])
        table = Path(job["table"])
        if not table.is_absolute():
            table = manifest_path.parent / table
        epsilon = str(job["epsilon"])
        checkpoint = work_dir / f"{job_id}.checkpoint.json.gz"
        output = work_dir / f"{job_id}.certificate.json.gz"
        resume = checkpoint.exists()
        search = _load_or_create_search(table, epsilon, checkpoint, resume)
        result = search.run(
            max_steps=int(job.get("max_steps", args.max_steps)),
            max_seconds=(
                args.max_seconds
                if job.get("max_seconds") is None
                else float(job["max_seconds"])
            ),
            checkpoint_path=checkpoint,
            checkpoint_every=args.checkpoint_every,
        )
        if result is None:
            print(f"{job_id}: incomplete at {search.steps} steps")
            failures += 1
        else:
            _write_certificate(output, result.certificate)
            print(f"{job_id}: resolved {result.kind}")
    return 2 if failures else 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="fin4-exact-search")
    sub = parser.add_subparsers(dest="command", required=True)

    validate = sub.add_parser("validate-table", help="validate a normalized table")
    validate.add_argument("table", type=Path)

    scale = sub.add_parser("scale", help="print the exact scale contract")
    scale.add_argument("epsilon")

    verify = sub.add_parser("verify", help="verify a certificate exactly")
    verify.add_argument("certificate", type=Path)

    search = sub.add_parser("search", help="run or resume the fair per-scale search")
    search.add_argument("--table", required=True, type=Path)
    search.add_argument("--epsilon", required=True)
    search.add_argument("--checkpoint", type=Path)
    search.add_argument("--resume", action="store_true")
    search.add_argument("--output", type=Path)
    search.add_argument("--max-steps", type=int)
    search.add_argument("--max-seconds", type=float)
    search.add_argument("--checkpoint-every", type=int, default=100)

    campaign = sub.add_parser(
        "campaign", help="run a resumable coarse-to-fine exact search campaign"
    )
    campaign.add_argument("--table", required=True, type=Path)
    campaign.add_argument("--start-epsilon", required=True)
    campaign.add_argument("--refinement", default="2")
    campaign.add_argument("--work-dir", required=True, type=Path)
    campaign.add_argument("--resume", action="store_true")
    campaign.add_argument("--max-steps", type=int)
    campaign.add_argument("--max-seconds", type=float)
    campaign.add_argument("--checkpoint-every", type=int, default=1000)
    campaign.add_argument("--report-every", type=int, default=10000)
    campaign.add_argument("--report-seconds", type=float, default=60)
    campaign.add_argument(
        "--stop-after-scales",
        type=int,
        help="engineering stop after this many certified profile scales",
    )

    region = sub.add_parser("region", help="canonicalize a remote work region")
    region.add_argument("--table", required=True, type=Path)
    region.add_argument("--epsilon", required=True)
    region.add_argument(
        "--kind", choices=("full", "lower", "upper", "heuristic"), required=True
    )
    region.add_argument("--prefix", type=Path)
    region.add_argument("--diagonal-start", type=int, default=2)
    region.add_argument("--diagonal-end", type=int)
    region.add_argument("--seed-start", type=int, default=0)
    region.add_argument("--seed-end", type=int)
    region.add_argument("--output", type=Path)

    partition = sub.add_parser(
        "partition-lower", help="emit a deterministic complete lower partition"
    )
    partition.add_argument("--table", required=True, type=Path)
    partition.add_argument("--epsilon", required=True)
    partition.add_argument("--depth", type=int, required=True)
    partition.add_argument(
        "--prefix",
        type=Path,
        help="optional JSON prefix list when splitting an existing lower region",
    )
    partition.add_argument("--output", type=Path, required=True)
    partition.add_argument("--regions-dir", type=Path)

    scan = sub.add_parser("scan-region", help="run or resume one claimed region")
    scan.add_argument("--table", required=True, type=Path)
    scan.add_argument("--region", required=True, type=Path)
    scan.add_argument("--checkpoint", type=Path)
    scan.add_argument("--resume", action="store_true")
    scan.add_argument("--output", type=Path)
    scan.add_argument("--max-steps", type=int)
    scan.add_argument("--max-seconds", type=float)
    scan.add_argument("--checkpoint-every", type=int, default=100)

    merge = sub.add_parser(
        "merge-lower", help="merge a complete family of regional lower trees"
    )
    merge.add_argument("--output", required=True, type=Path)
    merge.add_argument("certificates", nargs="+", type=Path)

    batch = sub.add_parser("batch", help="advance every job in a manifest")
    batch.add_argument("--manifest", required=True, type=Path)
    batch.add_argument("--work-dir", required=True, type=Path)
    batch.add_argument("--max-steps", type=int, default=1000)
    batch.add_argument("--max-seconds", type=float)
    batch.add_argument("--checkpoint-every", type=int, default=100)
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "validate-table":
        reward = load_reward_table(args.table)
        print(f"valid normalized rational Fin4 table sha256={reward.digest}")
        return 0
    if args.command == "scale":
        print_json(ScaleContract.create(Q(args.epsilon)).to_json())
        return 0
    if args.command == "verify":
        print(verify_certificate_file(args.certificate))
        return 0
    if args.command == "search":
        return command_search(args)
    if args.command == "campaign":
        return command_campaign(args)
    if args.command == "region":
        return command_region(args)
    if args.command == "partition-lower":
        return command_partition_lower(args)
    if args.command == "scan-region":
        return command_scan_region(args)
    if args.command == "merge-lower":
        return command_merge_lower(args)
    if args.command == "batch":
        return command_batch(args)
    raise AssertionError(args.command)


def entrypoint() -> None:
    try:
        raise SystemExit(main())
    except (KeyError, TypeError, ValueError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1) from error
