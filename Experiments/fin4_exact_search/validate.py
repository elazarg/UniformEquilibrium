#!/usr/bin/env python3
"""Clean-clone validation gate for the exact Fin4 search package."""

from __future__ import annotations

from contextlib import redirect_stdout
import io
from pathlib import Path
import sys
import tempfile
import unittest


sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from fin4_exact_search.cli import main  # noqa: E402


def run() -> int:
    suite = unittest.defaultTestLoader.discover(
        str(ROOT / "tests"), pattern="test_*.py", top_level_dir=str(ROOT)
    )
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        return 1

    with tempfile.TemporaryDirectory(prefix="fin4-exact-search-") as directory:
        temporary = Path(directory)
        certificate = temporary / "certificate.json.gz"
        checkpoint = temporary / "checkpoint.json.gz"
        region = temporary / "full.region.json"
        region_checkpoint = temporary / "full.region.state.json.gz"
        region_certificate = temporary / "full.region.certificate.json.gz"
        table = ROOT / "examples" / "zero_table.json"
        output = io.StringIO()
        with redirect_stdout(output):
            search_status = main(
                [
                    "search",
                    "--table",
                    str(table),
                    "--epsilon",
                    "100",
                    "--max-steps",
                    "4",
                    "--checkpoint",
                    str(checkpoint),
                    "--output",
                    str(certificate),
                ]
            )
            verify_status = main(["verify", str(certificate)])
            region_status = main(
                [
                    "region",
                    "--table",
                    str(table),
                    "--epsilon",
                    "100",
                    "--kind",
                    "full",
                    "--output",
                    str(region),
                ]
            )
            first_scan_status = main(
                [
                    "scan-region",
                    "--table",
                    str(table),
                    "--region",
                    str(region),
                    "--checkpoint",
                    str(region_checkpoint),
                    "--max-steps",
                    "1",
                    "--output",
                    str(region_certificate),
                ]
            )
            second_scan_status = main(
                [
                    "scan-region",
                    "--table",
                    str(table),
                    "--region",
                    str(region),
                    "--checkpoint",
                    str(region_checkpoint),
                    "--resume",
                    "--max-steps",
                    "2",
                    "--output",
                    str(region_certificate),
                ]
            )
            region_verify_status = main(["verify", str(region_certificate)])
        if (
            search_status != 0
            or verify_status != 0
            or region_status != 0
            or first_scan_status != 2
            or second_scan_status != 0
            or region_verify_status != 0
        ):
            print(output.getvalue(), file=sys.stderr)
            return 1

    print("fin4_exact_search validation passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(run())
