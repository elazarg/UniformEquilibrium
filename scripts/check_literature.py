#!/usr/bin/env python3
"""Check literature catalog, claim lifecycle, and source policy."""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys
from dataclasses import dataclass

try:
    from scripts.check_import_graph import check_import_graph
    from scripts.check_import_graph import project_lean_files
    from scripts.check_trust import strip_comments_and_strings
except ModuleNotFoundError:  # Direct execution from the scripts directory.
    from check_import_graph import check_import_graph
    from check_import_graph import project_lean_files
    from check_trust import strip_comments_and_strings


ROOT = pathlib.Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class ReferencedDeclaration:
    """A declaration name stored in a paper claim status."""

    paper: pathlib.Path
    claim_status: str
    name: str
    name_index: int


STATUS_RE = re.compile(
    r"\bstatus\s*:=\s*\.(sourceOnly|outOfScope|openInLean|provedInLean|"
    r"refutedInLean)\b((?:\s+\"(?:\\[\s\S]|[^\"\\])*\")*)"
)
STRING_RE = re.compile(r'"(?:\\[\s\S]|[^"\\])*"')
LEAN_IDENT = r"(?:[^\W\d]|_)[\w']*"
DECLARATION_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev|opaque|instance)\s+"
    rf"({LEAN_IDENT}(?:\.{LEAN_IDENT})*)",
    re.MULTILINE,
)
NAMESPACE_RE = re.compile(
    r"^\s*namespace\s+"
    rf"({LEAN_IDENT}(?:\.{LEAN_IDENT})*)\s*$",
    re.MULTILINE,
)
SECTION_RE = re.compile(
    rf"^\s*(?:noncomputable\s+)?section(?:\s+{LEAN_IDENT})?\s*$",
    re.MULTILINE,
)
END_NAMESPACE_RE = re.compile(
    rf"^\s*end(?:\s+{LEAN_IDENT}(?:\.{LEAN_IDENT})*)?\s*$",
    re.MULTILINE,
)
AUDIT_STATUS_RE = re.compile(r"\bauditStatus\s*:=\s*\.([A-Za-z_][A-Za-z0-9_]*)\b")


def _lean_string(raw: str) -> str:
    """Decode the small Lean-string subset used for declaration names."""

    # Declaration names are ordinary ASCII identifiers.  Handling escaped
    # quotes/backslashes here keeps the status parser conservative without
    # pretending to be a Lean parser.
    body = raw[1:-1]
    body = re.sub(r"\\\r?\n", "", body)
    return re.sub(r"\\(.)", r"\1", body)


def _status_references(
    path: pathlib.Path, root: pathlib.Path
) -> tuple[list[ReferencedDeclaration], list[str]]:
    """Read status constructors from a paper module.

    The paper schema is deliberately a tiny, fixed constructor language.  We
    reject a status with the wrong number of names instead of silently
    skipping it; this keeps the checker honest when the schema evolves.
    """

    text = path.read_text(encoding="utf-8")
    clean = strip_comments_and_strings(text)
    references: list[ReferencedDeclaration] = []
    errors: list[str] = []
    for match in STATUS_RE.finditer(text):
        # The raw scan retains strings so it can recover declaration names;
        # use the trust scanner's comment/string mask to discard prose and
        # string literals that happen to mention a status constructor.
        if clean[match.start() : match.start() + len("status")] != "status":
            continue
        status = match.group(1)
        names = [_lean_string(item.group(0)) for item in STRING_RE.finditer(match.group(2))]
        expected = {
            "sourceOnly": 0,
            "outOfScope": 0,
            "openInLean": 1,
            "provedInLean": 2,
            "refutedInLean": 2,
        }[status]
        if len(names) != expected:
            errors.append(
                f"{path.relative_to(root)}: status .{status} has {len(names)} "
                f"declaration names; expected {expected}"
            )
            continue
        references.extend(
            ReferencedDeclaration(path, status, name, index)
            for index, name in enumerate(names)
        )
    return references, errors


def _declaration_names(root: pathlib.Path) -> dict[str, set[str]]:
    """Collect declaration names with a conservative namespace-aware scan.

    Maps each name to the set of top-level lane directories whose files
    define it, so callers can test lane residence by file location rather
    than by name prefix: a namespace does not determine the lane of the file
    that declares it."""

    names: dict[str, set[str]] = {}
    paths = project_lean_files(root)
    # GameTheory is a pinned source dependency and is intentionally a leaf of
    # the project import graph.  Literature proofs may nevertheless delegate
    # to its declarations, so include its source for name validation when the
    # checkout is present; this does not make it a project-owned module.
    dependency = root / "GameTheory"
    if dependency.is_dir():
        paths.extend(sorted(dependency.rglob("*.lean")))
    for path in paths:
        try:
            lane = path.relative_to(root).parts[0]
        except ValueError:
            lane = "GameTheory"
        clean = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        blocks: list[tuple[str, str]] = []
        events = sorted(
            [(match.start(), "namespace", match.group(1))
             for match in NAMESPACE_RE.finditer(clean)]
            + [(match.start(), "section", "")
               for match in SECTION_RE.finditer(clean)]
            + [(match.start(), "end", "")
               for match in END_NAMESPACE_RE.finditer(clean)],
            key=lambda event: event[0],
        )
        declarations = list(DECLARATION_RE.finditer(clean))
        event_index = 0
        for declaration in declarations:
            while event_index < len(events) and events[event_index][0] < declaration.start():
                _, kind, value = events[event_index]
                if kind in {"namespace", "section"}:
                    blocks.append((kind, value))
                elif blocks:
                    blocks.pop()
                event_index += 1
            short_name = declaration.group(1)
            names.setdefault(short_name, set()).add(lane)
            namespace = [value for kind, value in blocks if kind == "namespace"]
            if namespace and "." not in short_name:
                qualified = ".".join(namespace + [short_name])
                names.setdefault(qualified, set()).add(lane)
    return names


def check_claim_declarations(root: pathlib.Path = ROOT) -> list[str]:
    """Check that every non-source claim status names real declarations.

    This intentionally checks declaration existence, not theorem meaning:
    Lean remains the authority for whether a named statement is a proposition,
    proof, or refutation.  The distinction is important for explicit
    ``refutedInLean`` records, whose proof name must be checked just like a
    positive theorem's proof name.
    """

    infrastructure = {"Catalog.lean"}
    paper_paths = sorted(
        path
        for path in (root / "Literature").glob("*.lean")
        if path.name not in infrastructure
    )
    references: list[ReferencedDeclaration] = []
    errors: list[str] = []
    for path in paper_paths:
        found, status_errors = _status_references(path, root)
        references.extend(found)
        errors.extend(status_errors)
        paper_text = path.read_text(encoding="utf-8")
        paper_clean = strip_comments_and_strings(paper_text)
        status_matches = [
            match for match in STATUS_RE.finditer(paper_text)
            if paper_clean[match.start() : match.start() + len("status")] == "status"
        ]
        statuses = [match.group(1) for match in status_matches]
        audit_match = AUDIT_STATUS_RE.search(paper_clean)
        if audit_match is None:
            errors.append(f"{path.relative_to(root)}: missing auditStatus")
            continue
        audit_status = audit_match.group(1)
        terminal_statuses = {"provedInLean", "refutedInLean", "outOfScope"}
        if audit_status == "catalogued" and statuses:
            errors.append(
                f"{path.relative_to(root)}: catalogued paper has claim statuses"
            )
        elif audit_status == "sourceInspected" and statuses:
            errors.append(
                f"{path.relative_to(root)}: sourceInspected paper has claim statuses"
            )
        elif audit_status == "claimAuditComplete" and "sourceOnly" in statuses:
            errors.append(
                f"{path.relative_to(root)}: claimAuditComplete paper has sourceOnly claims"
            )
        elif audit_status == "correspondenceComplete" and any(
            status not in terminal_statuses for status in statuses
        ):
            errors.append(
                f"{path.relative_to(root)}: correspondenceComplete paper has "
                "open or source-only claims"
            )
    declarations = _declaration_names(root)
    for reference in references:
        paper_module = ".".join(reference.paper.relative_to(root).with_suffix("").parts)
        if reference.name not in declarations:
            errors.append(
                f"{reference.paper.relative_to(root)}: .{reference.claim_status} "
                f"references missing Lean declaration {reference.name!r}"
            )
        if reference.name_index == 0 and not reference.name.startswith(
            paper_module + "."
        ):
            errors.append(
                f"{reference.paper.relative_to(root)}: .{reference.claim_status} "
                f"statement {reference.name!r} is not owned by {paper_module}"
            )
        if (
            reference.claim_status in {"provedInLean", "refutedInLean"}
            and reference.name_index == 1
            and declarations.get(reference.name, set()) & {"Research", "Experiments"}
        ):
            errors.append(
                f"{reference.paper.relative_to(root)}: final .{reference.claim_status} "
                f"proof {reference.name!r} belongs to a non-final lane"
            )
    return errors


def main() -> int:
    errors: list[str] = []
    generated = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "generate_literature.py"), "--check"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if generated.returncode:
        errors.append(generated.stdout.strip())
    tracked = subprocess.run(
        ["git", "ls-files", "--", "*.pdf", "*.PDF"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if tracked.returncode:
        errors.append(tracked.stderr.strip())
    elif tracked.stdout.strip():
        errors.append("tracked PDF files are forbidden:\n" + tracked.stdout.strip())
    errors.extend(check_claim_declarations(ROOT))
    errors.extend(check_import_graph(ROOT, ("Literature",)))
    if errors:
        print("Literature check failed:", file=sys.stderr)
        print(*errors, sep="\n", file=sys.stderr)
        return 1
    print("Literature check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
