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
