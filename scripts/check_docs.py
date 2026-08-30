#!/usr/bin/env python3
"""Validate generated documentation, status references, and local links."""

from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import sys
from urllib.parse import unquote


ROOT = pathlib.Path(__file__).resolve().parents[1]
STATUS_PATH = ROOT / "docs" / "ProjectStatus.json"
FRONTIER_PATH = ROOT / "docs" / "QuittingProofFrontier.json"
CORE_LIVE_DOCS = (
    ROOT / "README.md",
    ROOT / "AGENTS.md",
    ROOT / "CLAUDE.md",
    ROOT / "CONTRIBUTING.md",
    ROOT / ".github" / "PULL_REQUEST_TEMPLATE.md",
    ROOT / "Literature" / "README.md",
    ROOT / "docs" / "README.md",
    ROOT / "docs" / "SEMANTICS.md",
    ROOT / "docs" / "STATUS.md",
    ROOT / "docs" / "FRONTIER.md",
    ROOT / "docs" / "TOOLKIT.md",
    ROOT / "docs" / "PROGRAM.md",
    ROOT / "docs" / "PIPELINE.md",
    ROOT / "docs" / "ENGINEERING_ROADMAP.md",
    ROOT / "docs" / "SOFTWARE_ENGINEERING_REVIEW.md",
    ROOT / "docs" / "GAMETHEORY_INTEGRATION.md",
    ROOT / "UniformEquilibrium" / "README.md",
    ROOT / "UniformEquilibrium" / "UNIFORM_EQUILIBRIUM_PROBLEM.md",
)
TOP_LEVEL_LIVING_DOCS = tuple(sorted((ROOT / "docs").glob("*.md")))
METHOD_LIVING_DOCS = tuple(sorted((ROOT / "docs" / "methods").glob("*.md")))
DESIGN_LIVING_DOCS = tuple(
    document
    for document in sorted((ROOT / "docs" / "design").glob("*.md"))
    if "Historical design record." not in document.read_text(encoding="utf-8")[:512]
)
LANE_LIVING_DOCS = tuple(
    sorted(
        document
        for lane in ("Research", "Reverse", "Theorems", "UniformEquilibrium")
        for pattern in ("README.md", "MANIFEST.md")
        for document in (ROOT / lane).rglob(pattern)
    )
)
LIVE_DOCS = tuple(
    dict.fromkeys(
        (
            *CORE_LIVE_DOCS,
            *TOP_LEVEL_LIVING_DOCS,
            *METHOD_LIVING_DOCS,
            *DESIGN_LIVING_DOCS,
            *LANE_LIVING_DOCS,
        )
    )
)
TIMELESS_DOCS = LIVE_DOCS
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
IMPORT_RE = re.compile(r"^import\s+([^\s]+)", re.MULTILINE)
SOURCE_REFERENCE_RE = re.compile(
    r"`([A-Za-z0-9_./+-]+\.lean)(?::(\d+)(?:-(\d+))?)?`"
)
NAMED_SOURCE_REFERENCE_RE = re.compile(
    r"`([^\s`\n]+)`\s*"
    r"\(`([A-Za-z0-9_./+-]+\.lean)(?::\d+(?:-\d+)?)?`\)"
)
TABLE_SOURCE_REFERENCE_RE = re.compile(
    r"^\|\s*[A-Z][A-Z0-9]*\s*\|\s*`([^\s`\n]+)`\s*\|\s*"
    r"`([A-Za-z0-9_./+-]+\.lean)(?::\d+(?:-\d+)?)?`\s*\|",
    re.MULTILINE,
)
COMMIT_HASH_RE = re.compile(
    r"(?<![0-9A-Za-z])"
    r"(?=[0-9a-f]{7,40}(?![0-9A-Za-z]))"
    r"(?=[0-9a-f]*[a-f])"
    r"[0-9a-f]{7,40}"
)
DOI_PREFIX_RE = re.compile(r"(?:\bdoi\s+)?10\.\d{4,9}/$", re.IGNORECASE)
CALENDAR_DATE_RE = re.compile(r"\b(?:19|20)\d{2}-\d{2}-\d{2}\b")
HISTORICAL_HEADING_RE = re.compile(
    r"^#{1,6}\s+.*(?:"
    r"change\s*log|implementation history|historical baseline|"
    r"remediation record|review-start|progress (?:log|table)|"
    r"phase\s+\d+.*(?:complete|completed|results?)"
    r")",
    re.IGNORECASE | re.MULTILINE,
)
HISTORICAL_NARRATIVE_RE = re.compile(
    r"\b(?:"
    r"first pass of (?:this|the) document|"
    r"landed at|committed at|previous revision|"
    r"(?:module|shim|file|path|import|declaration|theorem|producer|compiler|"
    r"adapter|implementation|body|chain|leaf|route|branch|argument|hypothesis)"
    r"s? (?:was|were|has been|have been) removed"
    r")\b",
    re.IGNORECASE,
)
PRUNED_DIRECTORIES = {
    ".git",
    ".lake",
    "GameTheory",
    "Games",
    "__pycache__",
    ".pytest_cache",
    "ephemeral",
    "literature",
    "overleaf",
}
ROOT_PRUNED_DIRECTORIES = {ROOT / "math"}


def relative(path: pathlib.Path) -> str:
    return str(path.relative_to(ROOT))


def project_markdown_files() -> list[pathlib.Path]:
    documents: list[pathlib.Path] = []
    for directory, names, filenames in os.walk(ROOT):
        base = pathlib.Path(directory)
        names[:] = [
            name
            for name in names
            if name not in PRUNED_DIRECTORIES
            and base / name not in ROOT_PRUNED_DIRECTORIES
        ]
        documents.extend(base / name for name in filenames if name.endswith(".md"))
    return documents


def is_dedicated_history_or_evidence(document: pathlib.Path) -> bool:
    """Whether a Markdown file is an explicitly scoped non-living record."""
    relative_path = document.relative_to(ROOT)
    parts = relative_path.parts
    if parts[0] == "Experiments":
        return True
    if parts[:2] in {
        ("docs", "audits"),
        ("docs", "history"),
        ("docs", "references"),
    }:
        return True
    if parts[:2] == ("Reverse", "Tasks") and document.name != "README.md":
        return True
    if parts[:2] == ("Reverse", "Runs") and document.name != "README.md":
        return True
    prefix = document.read_text(encoding="utf-8")[:512]
    return (
        "Historical design record." in prefix
        or "Historical case-study record." in prefix
    )


def check_document_classification(errors: list[str]) -> None:
    documents = set(project_markdown_files())
    living = {document for document in LIVE_DOCS if document.is_file()}
    evidence = {
        document for document in documents if is_dedicated_history_or_evidence(document)
    }
    overlap = living & evidence
    if overlap:
        errors.append(
            "Markdown files classified as both living and historical/evidence: "
            + ", ".join(relative(document) for document in sorted(overlap))
        )
    unclassified = documents - living - evidence
    if unclassified:
        errors.append(
            "unclassified Markdown files: "
            + ", ".join(relative(document) for document in sorted(unclassified))
        )


def check_generated(errors: list[str]) -> None:
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "generate_docs.py"), "--check"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if result.returncode:
        errors.append(result.stdout.strip())

    k11_result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "check_k11_generated_data.py")],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if k11_result.returncode:
        errors.append(k11_result.stdout.strip())

    adapter_result = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "generate_quitting_repair_adapters.py"),
            "--check",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if adapter_result.returncode:
        errors.append(adapter_result.stdout.strip())


def check_markdown_names(errors: list[str]) -> None:
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "normalize_markdown_names.py")],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if result.returncode:
        errors.append(result.stdout.strip())


def check_status(errors: list[str]) -> None:
    status = json.loads(STATUS_PATH.read_text(encoding="utf-8"))
    if status.get("schema_version") != 1:
        errors.append("docs/ProjectStatus.json: unsupported schema_version")
    ids: set[str] = set()
    for claim in status.get("claims", []):
        claim_id = claim.get("id")
        if not claim_id or claim_id in ids:
            errors.append(f"docs/ProjectStatus.json: duplicate or empty id {claim_id!r}")
        ids.add(claim_id)
        source = ROOT / claim["source"]
        umbrella = ROOT / claim["umbrella"]
        if not source.is_file():
            errors.append(f"{claim_id}: missing source {claim['source']}")
            continue
        if not umbrella.is_file():
            errors.append(f"{claim_id}: missing umbrella {claim['umbrella']}")
            continue
        source_text = source.read_text(encoding="utf-8")
        declarations = {
            name: kind
            for kind, name in re.findall(
                r"^\s*(def|theorem)\s+([A-Za-z0-9_'.]+)",
                source_text,
                re.MULTILINE,
            )
        }
        declaration = claim["declaration"]
        if declaration not in declarations:
            errors.append(
                f"{claim_id}: declaration {declaration} not found in "
                f"{claim['source']}"
            )
        else:
            expected_kind = "def" if claim["kind"] == "Open proposition" else "theorem"
            if declarations[declaration] != expected_kind:
                errors.append(
                    f"{claim_id}: expected {expected_kind} but found "
                    f"{declarations[declaration]} for {declaration}"
                )
        module = claim["source"].removesuffix(".lean").replace("/", ".")
        imports = set(IMPORT_RE.findall(umbrella.read_text(encoding="utf-8")))
        if module not in imports:
            errors.append(f"{claim_id}: {module} is not imported by {claim['umbrella']}")


LEAN_NAME_RE = re.compile(r"\A[A-Za-z_][A-Za-z0-9_'ε]*(?:\.[A-Za-z_][A-Za-z0-9_'ε]*)+\Z")
PROSE_FIELDS = frozenset(
    {"id", "kind", "summary", "evidence", "source", "target_ids", "cover_clause_ids",
     "superseded_by", "obstruction_class", "representative", "evidence_seals", "status",
     "producer"}
)
DECLARATION_RE = re.compile(
    r"\A\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
    r"([A-Za-z_][^\s({\[:]*)"
)
NAMESPACE_RE = re.compile(r"\A\s*namespace\s+(\S+)")
SECTION_RE = re.compile(r"\A\s*section(?:\s+(\S+))?\s*\Z")
END_RE = re.compile(r"\A\s*end(?:\s+(\S+))?\s*\Z")


def collect_lean_names(value: object, field: str | None = None) -> set[str]:
    """Every dotted-identifier string reachable from a ledger entry.

    Collection is by shape, not by a field whitelist, so a register field added
    later is covered without touching this function; prose and path fields are
    excluded by name because their contents are not declaration names.
    """
    if isinstance(value, str):
        if field in PROSE_FIELDS or not LEAN_NAME_RE.match(value):
            return set()
        return {value}
    if isinstance(value, list):
        return set().union(*(collect_lean_names(item, field) for item in value)) if value else set()
    if isinstance(value, dict):
        found: set[str] = set()
        for key, item in value.items():
            if key in PROSE_FIELDS:
                continue
            found |= collect_lean_names(key, key)
            found |= collect_lean_names(item, key)
        return found
    return set()


def qualified_declaration_names(text: str) -> set[str]:
    """Fully qualified names declared in one Lean source, read lexically."""
    scopes: list[tuple[str, str | None]] = []
    names: set[str] = set()
    for line in text.splitlines():
        namespace = NAMESPACE_RE.match(line)
        if namespace:
            scopes.append(("namespace", namespace.group(1)))
            continue
        section = SECTION_RE.match(line)
        if section:
            scopes.append(("section", section.group(1)))
            continue
        closing = END_RE.match(line)
        if closing:
            label = closing.group(1)
            for index in range(len(scopes) - 1, -1, -1):
                if scopes[index][1] == label:
                    del scopes[index:]
                    break
            continue
        declaration = DECLARATION_RE.match(line)
        if declaration:
            prefix = [name for kind, name in scopes if kind == "namespace" and name]
            names.add(".".join(prefix + [declaration.group(1)]))
    return names


def check_frontier_names(entry: dict, sources: list[str], errors: list[str]) -> None:
    """Every declaration name an entry records must occur in its own evidence.

    Lexical only, in the spirit of the trust scan: the final segment must appear
    in some evidence file, and where that file's namespaces can be reconstructed
    the fully qualified name must match one of them.  A `#check` sweep over the
    recorded names remains the semantic backstop.
    """
    names = collect_lean_names(entry)
    if not names:
        return
    texts = {}
    for source in sources:
        path = ROOT / source
        if path.is_file():
            texts[source] = path.read_text(encoding="utf-8")
    if not texts:
        errors.append(
            f"{entry['id']}: records declaration names but has no readable evidence file; "
            "a #check sweep remains the semantic backstop"
        )
        return
    for name in sorted(names):
        segment = name.rsplit(".", 1)[-1]
        hosts = [source for source, text in texts.items() if segment in text]
        if not hosts:
            errors.append(
                f"{entry['id']}: recorded name {name} does not occur in its evidence "
                f"({', '.join(sources)}); a #check sweep remains the semantic backstop"
            )
            continue
        qualified: set[str] = set()
        for source in hosts:
            qualified |= qualified_declaration_names(texts[source])
        if qualified and name not in qualified:
            errors.append(
                f"{entry['id']}: recorded name {name} is not declared under that namespace "
                f"in {', '.join(hosts)}; a #check sweep remains the semantic backstop"
            )


def check_frontier(errors: list[str]) -> None:
    frontier = json.loads(FRONTIER_PATH.read_text(encoding="utf-8"))
    if frontier.get("schema_version") != 3:
        errors.append("docs/QuittingProofFrontier.json: unsupported schema_version")
    nodes = frontier.get("nodes", [])
    allowed_node_statuses = {"proved", "proved-alternative", "consumer-ready", "target"}
    allowed_edge_statuses = {"proved", "proved-branch", "open-producer", "proved-consumer"}
    allowed_seals = {"M", "L", "A", "C"}
    node_ids = {node["id"] for node in nodes}
    if len(node_ids) != len(nodes):
        errors.append("docs/QuittingProofFrontier.json: duplicate DAG node id")
    for node in nodes:
        if node.get("status") not in allowed_node_statuses:
            errors.append(f"{node['id']}: unknown DAG node status {node.get('status')}")
        unknown_seals = set(node.get("evidence_seals", [])) - allowed_seals
        if unknown_seals:
            errors.append(f"{node['id']}: unknown evidence seals {sorted(unknown_seals)}")
        source = ROOT / node["source"]
        if not source.is_file():
            errors.append(f"{node['id']}: missing source {node['source']}")
        elif node["declaration"].rsplit(".", 1)[-1] not in source.read_text(
            encoding="utf-8"
        ):
            errors.append(
                f"{node['id']}: declaration {node['declaration']} not found in "
                f"{node['source']}"
            )
        check_frontier_names(node, [node["source"]], errors)
    edges = frontier.get("edges", [])
    edge_ids = {edge["id"] for edge in edges}
    if len(edge_ids) != len(edges):
        errors.append("docs/QuittingProofFrontier.json: duplicate DAG edge id")
    for edge in edges:
        if edge.get("status") not in allowed_edge_statuses:
            errors.append(f"{edge['id']}: unknown DAG edge status {edge.get('status')}")
        unknown_seals = set(edge.get("evidence_seals", [])) - allowed_seals
        if unknown_seals:
            errors.append(f"{edge['id']}: unknown evidence seals {sorted(unknown_seals)}")
        unknown = {edge["from"], edge["to"]} - node_ids
        if unknown:
            errors.append(
                f"{edge['id']}: unknown node ids {', '.join(sorted(unknown))}"
            )
        source = ROOT / edge["source"]
        if not source.is_file():
            errors.append(f"{edge['id']}: missing source {edge['source']}")
        check_frontier_names(edge, [edge["source"]], errors)
    adjacency = {node_id: set() for node_id in node_ids}
    for edge in edges:
        if edge.get("from") in adjacency and edge.get("to") in node_ids:
            adjacency[edge["from"]].add(edge["to"])
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node_id: str) -> None:
        if node_id in visiting:
            errors.append(f"docs/QuittingProofFrontier.json: DAG cycle at {node_id}")
            return
        if node_id in visited:
            return
        visiting.add(node_id)
        for target in adjacency[node_id]:
            visit(target)
        visiting.remove(node_id)
        visited.add(node_id)

    for node_id in node_ids:
        visit(node_id)
    capstones = frontier.get("conditional_capstones", [])
    capstone_ids = {capstone["id"] for capstone in capstones}
    if len(capstone_ids) != len(capstones):
        errors.append("docs/QuittingProofFrontier.json: duplicate capstone id")
    for capstone in capstones:
        unknown_seals = set(capstone.get("evidence_seals", [])) - allowed_seals
        if unknown_seals:
            errors.append(f"{capstone['id']}: unknown evidence seals {sorted(unknown_seals)}")
        source = ROOT / capstone["source"]
        if not source.is_file():
            errors.append(f"{capstone['id']}: missing source {capstone['source']}")
        check_frontier_names(capstone, [capstone["source"]], errors)


def source_reference_issues(
    text: str,
    root: pathlib.Path = ROOT,
) -> list[str]:
    """Validate root-relative Lean source references, which carry no line numbers.

    A line number goes stale whenever anything is inserted above the cited
    declaration, so it reports a spurious failure for an untouched declaration
    and has to be repinned by hand.  The declaration name is the stable
    locator, and `named_source_reference_issues` resolves it.
    """
    issues: list[str] = []
    for raw_path, first_text, last_text in SOURCE_REFERENCE_RE.findall(text):
        source = root / raw_path
        if not source.is_file():
            issues.append(f"missing source reference {raw_path}")
            continue
        if first_text:
            locator = raw_path + ":" + first_text
            if last_text:
                locator += f"-{last_text}"
            issues.append(
                f"line-pinned source reference {locator}; "
                "cite the declaration name instead"
            )
    return issues


def named_source_reference_issues(
    text: str,
    root: pathlib.Path = ROOT,
) -> list[str]:
    """Check that a named source locator names a file containing that name.

    Resolution is by name rather than by position, so moving a declaration
    within its file leaves the reference correct.  A missing path is reported
    once by `source_reference_issues`, so it is skipped here.
    """
    issues: list[str] = []
    references = (
        NAMED_SOURCE_REFERENCE_RE.findall(text)
        + TABLE_SOURCE_REFERENCE_RE.findall(text)
    )
    for name, raw_path in references:
        source = root / raw_path
        if not source.is_file():
            continue
        terminal_name = name.rsplit(".", 1)[-1]
        if terminal_name not in source.read_text(encoding="utf-8"):
            issues.append(f"named source reference {name} not found in {raw_path}")
    return issues


def check_living_document_sources(errors: list[str]) -> None:
    for document in TIMELESS_DOCS:
        if not document.is_file():
            continue
        text = document.read_text(encoding="utf-8")
        for issue in source_reference_issues(text):
            errors.append(f"{relative(document)}: {issue}")
        for issue in named_source_reference_issues(text):
            errors.append(f"{relative(document)}: {issue}")


def check_links(errors: list[str]) -> None:
    for document in project_markdown_files():
        if "audits" in document.relative_to(ROOT).parts:
            continue
        text = document.read_text(encoding="utf-8")
        for raw_target in LINK_RE.findall(text):
            target = raw_target.strip().split()[0].strip("<>")
            if target.startswith(("http://", "https://", "mailto:", "#")):
                continue
            path_text = unquote(target.split("#", 1)[0])
            if not path_text:
                continue
            resolved = (document.parent / path_text).resolve()
            if not resolved.exists():
                errors.append(
                    f"{relative(document)}: broken local link {raw_target}"
                )


def check_live_docs(errors: list[str]) -> None:
    forbidden = {
        "`Math/": "old Math path",
        "`Models/": "old Models path",
    }
    for document in LIVE_DOCS:
        if not document.is_file():
            errors.append(f"missing live document {relative(document)}")
            continue
        text = document.read_text(encoding="utf-8")
        for token, label in forbidden.items():
            if token in text:
                errors.append(f"{relative(document)}: contains {label}: {token}")
        if re.search(r"ideas/[A-Za-z0-9_.-]+", text):
            errors.append(
                f"{relative(document)}: contains a dead pre-extraction ideas path"
            )


def timeless_document_issues(text: str) -> list[str]:
    """Return chronology markers that do not belong in living documentation."""
    issues: list[str] = []
    hash_matches = (
        match
        for match in COMMIT_HASH_RE.finditer(text)
        if not DOI_PREFIX_RE.search(text[max(0, match.start() - 32) : match.start()])
    )
    if next(hash_matches, None) is not None:
        issues.append("contains a raw Git commit hash")
    if CALENDAR_DATE_RE.search(text):
        issues.append("contains a calendar-dated snapshot")
    if HISTORICAL_HEADING_RE.search(text):
        issues.append("contains a changelog-style heading")
    if HISTORICAL_NARRATIVE_RE.search(text):
        issues.append("contains repository-change narrative")
    return issues


def check_timeless_docs(errors: list[str]) -> None:
    for document in TIMELESS_DOCS:
        if not document.is_file():
            continue
        for issue in timeless_document_issues(document.read_text(encoding="utf-8")):
            errors.append(f"{relative(document)}: {issue}")


def main() -> int:
    errors: list[str] = []
    check_markdown_names(errors)
    check_document_classification(errors)
    check_generated(errors)
    check_status(errors)
    check_frontier(errors)
    check_living_document_sources(errors)
    check_links(errors)
    check_live_docs(errors)
    check_timeless_docs(errors)
    if errors:
        print("Documentation check failed:", file=sys.stderr)
        print(*errors, sep="\n", file=sys.stderr)
        return 1
    print("Documentation check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
