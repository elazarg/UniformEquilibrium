"""Command-line interface for the exact Fin4 search experiment."""

from __future__ import annotations

import argparse
import gc
from hashlib import sha256
from pathlib import Path
import signal
import sys
from typing import Any, Optional, Sequence

from .candidate_campaign import (
    CampaignDescriptor,
    CandidateCampaign,
    DEFAULT_ALPHA,
    load_tracked_candidates,
)
from .direct_oracle import (
    DIRECT_LOWER_KIND,
    ROBUST_GAP_KIND,
    ConfigurableDirectScaleContract,
    DirectHazardLowerTreeCertificate,
    DirectScaleSearch,
    RobustGapCertificate,
)
from .engine import (
    PROFILE_KIND,
    ProfileCertificate,
    Q,
    certificate_digest,
    load_reward_table,
    qjson,
    read_json,
    write_json_atomic,
)


def print_json(data: Any) -> None:
    import json

    print(json.dumps(data, sort_keys=True, indent=2))


def _write_certificate(
    path: Path, certificate: Any, *, already_verified: bool = False
) -> None:
    if not already_verified:
        certificate.verify()
    write_json_atomic(path, certificate.to_json())
    file_sha256 = sha256(path.read_bytes()).hexdigest()
    print(
        f"wrote {path} payload_sha256={certificate_digest(certificate)} "
        f"file_sha256={file_sha256}"
    )


def command_search(args: argparse.Namespace) -> int:
    """Run one equality-free direct finite-clock scale resolver."""
    if args.checkpoint_every <= 0:
        raise ValueError("--checkpoint-every must be positive")
    reward = load_reward_table(args.table)
    epsilon = Q(args.epsilon)
    alpha = Q(args.alpha)
    if args.resume:
        if args.checkpoint is None or not args.checkpoint.exists():
            raise ValueError("--resume needs an existing --checkpoint")
        search = DirectScaleSearch.from_checkpoint_json(read_json(args.checkpoint))
        if (
            search.reward != reward
            or search.contract.epsilon != epsilon
            or search.contract.alpha != alpha
        ):
            raise ValueError("checkpoint and supplied search contract disagree")
    else:
        search = DirectScaleSearch(reward, epsilon, alpha)
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
            f"steps={search.steps} lower_nodes={len(search.lower.nodes)} "
            f"lower_pending={len(search.lower.stack)} "
            f"upper_diagonal={search.upper.diagonal}"
        )
        return 2
    kind = result.kind
    certificate = result.certificate
    total_steps = search.steps
    contract = search.contract
    # Verification reconstructs the expression problem.  Release the
    # completed resolver first so only one full DAG is resident.
    del result, search
    gc.collect()
    output = args.output or Path(f"{kind}-certificate.json.gz")
    if kind == "lower":
        if not isinstance(certificate, DirectHazardLowerTreeCertificate):
            raise TypeError("lower resolver returned the wrong certificate")
        global_lower = certificate.verify_positive_global()
        if global_lower != contract.certified_global_lower:
            raise ValueError("lower result violates its scale contract")
        _write_certificate(output, certificate, already_verified=True)
        robust = RobustGapCertificate.canonical(certificate)
        robust_output = output.with_name(output.name + ".robust.json.gz")
        _write_certificate(robust_output, robust, already_verified=True)
        print(
            f"certified_eta_lower={qjson(certificate.global_lower)} "
            f"robust_radius={qjson(robust.radius)} "
            f"robust_eta_lower={qjson(robust.gamma)}"
        )
    else:
        _write_certificate(output, certificate)
    print(f"resolved={kind} total_steps={total_steps}")
    return 0


def command_discover(args: argparse.Namespace) -> int:
    """Run the no-input, source-tracked, resumable candidate campaign."""
    if args.quantum_steps <= 0 or args.report_every <= 0:
        raise ValueError("quantum and report intervals must be positive")
    work_dir = args.work_dir.resolve()
    state_dir = work_dir / "state"
    checkpoint = work_dir / "campaign.checkpoint.json.gz"
    candidates = load_tracked_candidates(denominator=args.denominator)
    descriptor = CampaignDescriptor.create(
        candidates,
        args.denominator,
        Q(args.start_epsilon),
        Q(args.refinement),
        Q(args.alpha),
        args.scale_limit,
        args.shard_count,
        args.shard_index,
    )
    if checkpoint.exists():
        campaign = CandidateCampaign.load(checkpoint, state_dir)
        if campaign.descriptor != descriptor:
            raise ValueError("existing work directory has a different search contract")
        print(
            f"resuming campaign={descriptor.campaign_id} "
            f"checkpoint={checkpoint}",
            flush=True,
        )
    else:
        work_dir.mkdir(parents=True, exist_ok=True)
        campaign = CandidateCampaign(candidates, descriptor, state_dir)
        campaign.save(checkpoint)
        print(
            f"starting campaign={descriptor.campaign_id} "
            f"candidates={len(candidates)} shard="
            f"{descriptor.shard_index}/{descriptor.shard_count} "
            f"checkpoint={checkpoint}",
            flush=True,
        )

    old_handler = signal.getsignal(signal.SIGTERM)

    def stop_at_boundary(_signum: int, _frame: Any) -> None:
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, stop_at_boundary)
    try:
        result = campaign.run(
            args.quantum_steps,
            args.max_quanta,
            args.max_seconds,
            checkpoint,
            args.report_every,
        )
    except KeyboardInterrupt:
        campaign.save(checkpoint)
        print(
            "interrupted at an exact checkpoint boundary; "
            "no mathematical conclusion",
            flush=True,
        )
        print_json(campaign.progress())
        return 130
    finally:
        signal.signal(signal.SIGTERM, old_handler)
    print_json(campaign.progress())
    if result is None:
        print("search paused or finite scale limit exhausted; no conclusion")
        return 2
    print("verified robust positive-gap certificate produced")
    return 0


def command_verify(path: Path) -> int:
    payload = read_json(path)
    kind = payload.get("kind")
    if kind == DIRECT_LOWER_KIND:
        certificate = DirectHazardLowerTreeCertificate.from_json(payload)
        certificate.verify()
        if certificate.is_global and certificate.global_lower > 0:
            global_lower = certificate.verify_positive_global()
            print(
                "verified global direct finite-clock lower tree; "
                f"eta_lower={qjson(global_lower)}"
            )
        else:
            print(
                "verified regional direct finite-clock lower tree; "
                f"F_level_threshold={qjson(certificate.threshold)}; "
                "no global eta conclusion"
            )
        return 0
    if kind == ROBUST_GAP_KIND:
        certificate = RobustGapCertificate.from_json(payload)
        certificate.verify()
        print(
            "verified robust reward box; "
            f"radius={qjson(certificate.radius)} "
            f"eta_lower={qjson(certificate.gamma)}"
        )
        return 0
    if kind == PROFILE_KIND:
        certificate = ProfileCertificate.from_json(payload)
        certificate.verify()
        print(
            "verified exact profile certificate; "
            f"exploitability={qjson(certificate.exploitability)} "
            f"threshold={qjson(certificate.epsilon)}"
        )
        return 0
    raise ValueError(f"unknown certificate kind {kind!r}")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="fin4-exact-search")
    sub = parser.add_subparsers(dest="command", required=True)

    validate = sub.add_parser("validate-table", help="validate a normalized table")
    validate.add_argument("table", type=Path)

    scale = sub.add_parser("scale", help="print the exact search scale contract")
    scale.add_argument("epsilon")
    scale.add_argument("--alpha", default=qjson(DEFAULT_ALPHA))

    verify = sub.add_parser("verify", help="verify a certificate exactly")
    verify.add_argument("certificate", type=Path)

    search = sub.add_parser("search", help="run one exact table/scale search")
    search.add_argument("--table", required=True, type=Path)
    search.add_argument("--epsilon", required=True)
    search.add_argument("--alpha", default=qjson(DEFAULT_ALPHA))
    search.add_argument("--checkpoint", type=Path)
    search.add_argument("--resume", action="store_true")
    search.add_argument("--output", type=Path)
    search.add_argument("--max-steps", type=int)
    search.add_argument("--max-seconds", type=float)
    search.add_argument("--checkpoint-every", type=int, default=100)

    discover = sub.add_parser(
        "discover",
        help="run or resume the tracked-candidate discovery campaign",
    )
    discover.add_argument(
        "--work-dir",
        type=Path,
        default=Path("Experiments/fin4_exact_search/runs/default"),
    )
    discover.add_argument("--denominator", type=int, default=10_000)
    discover.add_argument("--start-epsilon", default="4")
    discover.add_argument("--refinement", default="2")
    discover.add_argument("--alpha", default=qjson(DEFAULT_ALPHA))
    discover.add_argument("--scale-limit", type=int)
    discover.add_argument("--shard-count", type=int, default=1)
    discover.add_argument("--shard-index", type=int, default=0)
    discover.add_argument("--quantum-steps", type=int, default=1000)
    discover.add_argument("--max-quanta", type=int)
    discover.add_argument("--max-seconds", type=float)
    discover.add_argument("--report-every", type=int, default=1)
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "validate-table":
        reward = load_reward_table(args.table)
        print(f"valid normalized rational Fin4 table sha256={reward.digest}")
        return 0
    if args.command == "scale":
        print_json(
            ConfigurableDirectScaleContract(
                Q(args.epsilon), Q(args.alpha)
            ).to_json()
        )
        return 0
    if args.command == "verify":
        return command_verify(args.certificate)
    if args.command == "search":
        return command_search(args)
    if args.command == "discover":
        return command_discover(args)
    raise AssertionError(args.command)


def entrypoint() -> None:
    try:
        raise SystemExit(main())
    except (KeyError, TypeError, ValueError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1) from error
