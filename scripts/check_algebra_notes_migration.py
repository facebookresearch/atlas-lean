#!/usr/bin/env python3
"""Check the compact AlgebraNotes identity ledger, not proofs or source fidelity."""

import argparse
from collections import Counter
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

import yaml

import inventory_v1 as inventory

SCHEMA = "algebra-notes-migration/1"
BOOK = "AlgebraNotes"
BASE = "8de8f74fa5760eb8b768a9804494ca2ab631cf87"
COUNT = 176
FINDINGS = {
    "mapped_existing",
    "incomplete_hole",
    "scope_unresolved",
    "mapping_unresolved",
    "reuse_unresolved",
    "rejected_parallel_or_incomplete_definition",
    "rejected_semantic_mismatch",
    "rejected_false_statement",
}
GATES = {
    "compiler": "parent_owned_pending",
    "formal_equivalence": "parent_owned_pending",
    "semantic_review": "parent_owned_pending",
}
STATUSES = {
    "static_candidate",
    "unresolved",
    "blocked_false",
    "blocked_sorry",
    "blocked_semantics",
    "blocked_parallel",
    "partial_source",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fields(value, expected, label):
    require(
        isinstance(value, dict) and set(value) == set(expected),
        f"{label}: unexpected or missing fields",
    )


def digest(value, length=64):
    require(
        isinstance(value, str) and re.fullmatch(f"[0-9a-f]{{{length}}}", value),
        "invalid fingerprint",
    )


def load_json(data):
    return json.loads(
        data,
        object_pairs_hook=inventory.unique_object,
        parse_constant=inventory.reject_constant,
        parse_float=inventory.finite_float,
    )


def source_refs(summary):
    return [
        {k: source[k] for k in ("path", "git_blob", "sha256", "bytes")}
        for source in summary["sources"]
    ]


def legacy_matches(record):
    # Preserve the report relation; never zip names with files or deduplicate.
    return [
        {
            "row": match["report_row_ordinal"],
            "hash": match["report_row_sha256"],
            "declarations": match["declarations"],
            "files": [
                {k: file[k] for k in ("path", "git_blob") if k in file}
                for file in match["files"]
            ],
        }
        for match in record["legacy_matches"]
    ]


def disposition(record, declarations):
    """Only non-acceptance dispositions; findings are historical static reports."""
    names = [
        name for match in record["legacy_matches"] for name in match["declarations"]
    ]
    entries = [declarations[name] for name in names]
    findings = {entry["finding"] for entry in entries}
    for finding, status, reason in (
        ("rejected_false_statement", "blocked_false", "historical_false_statement"),
        ("incomplete_hole", "blocked_sorry", "historical_sorry_dependency"),
        (
            "rejected_semantic_mismatch",
            "blocked_semantics",
            "historical_semantic_mismatch",
        ),
        (
            "rejected_parallel_or_incomplete_definition",
            "blocked_parallel",
            "historical_parallel_or_incomplete",
        ),
    ):
        if finding in findings:
            return status, sorted({reason, *record["gaps"]})
    if record["gaps"]:
        return "partial_source", record["gaps"]
    if entries and findings == {"mapped_existing"}:
        return "static_candidate", ["fresh_api_semantic_gates_pending"]
    return "unresolved", ["scope_api_review_pending"]


def validate(ledger, source, expected_count=COUNT, expected_base=None):
    fields(
        ledger,
        (
            "schema",
            "book",
            "base",
            "sources",
            "pins",
            "prior_audit",
            "migration",
            "printed_source",
            "gates",
            "proof_receipts",
            "legacy_declarations",
            "destination_apis",
            "records",
        ),
        "ledger",
    )
    require(
        ledger["schema"] == SCHEMA and ledger["book"] == BOOK,
        "wrong ledger schema/book",
    )
    frozen_base = source.revision if expected_base is None else expected_base
    require(ledger["base"] == frozen_base, "stale source revision")
    require(ledger["migration"] == "partial", "migration must remain partial")
    require(
        ledger["printed_source"]
        == {"status": "unverified_no_primary_bytes", "sha256": None},
        "text identity is not printed source fidelity",
    )
    require(ledger["gates"] == GATES, "compiler/semantic gates remain parent-owned")
    # This first static packet admits no compiler or equivalence receipts.
    # Adding such evidence requires a separately reviewed, hash-bound contract.
    require(
        ledger["proof_receipts"] == [],
        "unbound proof evidence: static packet admits no receipts",
    )
    fields(
        ledger["prior_audit"],
        ("candidates_sha256", "api_mappings_sha256", "status"),
        "prior audit",
    )
    require(
        ledger["prior_audit"]["status"] == "historical_static_only",
        "historical audit is not acceptance",
    )
    digest(ledger["prior_audit"]["candidates_sha256"])
    digest(ledger["prior_audit"]["api_mappings_sha256"])

    records, summary = inventory.book_inventory(source, BOOK)
    require(
        len(records) == expected_count and expected_count > 0,
        "pinned inventory target count mismatch or empty source",
    )
    require(
        inventory.canonical(ledger["sources"])
        == inventory.canonical(source_refs(summary)),
        "stale source/report fingerprints",
    )
    manifest = load_json(source.read("lake-manifest.json"))
    mathlib = [p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"]
    require(len(mathlib) == 1, "missing/ambiguous Mathlib pin")
    require(
        ledger["pins"]
        == {
            "mathlib": mathlib[0],
            "lean": source.read("lean-toolchain").decode().strip(),
        },
        "stale destination/toolchain pins",
    )
    require(isinstance(ledger["destination_apis"], list), "APIs must be a list")
    apis = {}
    for api in ledger["destination_apis"]:
        fields(
            api,
            ("id", "name", "module", "revision", "relation", "scope", "reason"),
            "API",
        )
        require(
            isinstance(api["id"], str) and api["id"] and api["id"] not in apis,
            "duplicate/invalid API id",
        )
        require(isinstance(api["name"], str) and api["name"], "invalid API name")
        require(
            isinstance(api["module"], str)
            and re.fullmatch(r"(?:Mathlib|MathlibExt)\.[A-Za-z0-9_'.]+", api["module"]),
            "invalid destination module",
        )
        pin = mathlib[0] if api["module"].startswith("Mathlib.") else frozen_base
        require(api["revision"] == pin, "stale API pin")
        require(
            api["relation"] in {"replacement_candidate", "related_candidate"},
            "API relation must be static, not accepted",
        )
        reason = (
            "static_shape_only"
            if api["relation"] == "replacement_candidate"
            else "partial_bridge_unverified"
        )
        require(
            api["scope"] == "unverified" and api["reason"] == reason,
            "missing or misleading mapping scope/reason",
        )
        apis[api["id"]] = api

    require(
        isinstance(ledger["legacy_declarations"], list), "declarations must be a list"
    )
    declarations = {}
    used_apis = set()
    for entry in ledger["legacy_declarations"]:
        fields(
            entry,
            (
                "name",
                "file",
                "git_blob",
                "historical_excerpt_sha256",
                "finding",
                "historical_hole_dependencies",
                "apis",
            ),
            "legacy declaration",
        )
        name = entry["name"]
        require(
            isinstance(name, str) and name and name not in declarations,
            "duplicate/invalid legacy declaration identity",
        )
        path = entry["file"]
        require(
            isinstance(path, str)
            and path.startswith(f"v1/Atlas/{BOOK}/code/")
            and path.endswith(".lean")
            and ".." not in path.split("/"),
            "invalid legacy file",
        )
        require(
            path in source.tree and source.tree[path]["git_blob"] == entry["git_blob"],
            "stale legacy file fingerprint",
        )
        digest(entry["historical_excerpt_sha256"])
        require(entry["finding"] in FINDINGS, "unknown or accepted historical finding")
        holes = entry["historical_hole_dependencies"]
        require(
            isinstance(holes, list) and all(isinstance(n, str) and n for n in holes),
            "invalid historical hole references",
        )
        require(
            isinstance(entry["apis"], list)
            and all(isinstance(a, str) and a in apis for a in entry["apis"]),
            "unbound API mapping",
        )
        require(
            len(entry["apis"]) == len(set(entry["apis"])), "duplicate API reference"
        )
        if entry["finding"] == "mapped_existing":
            require(
                entry["apis"]
                and all(
                    apis[a]["relation"] == "replacement_candidate"
                    for a in entry["apis"]
                ),
                "mapped finding needs static replacement candidates",
            )
        if holes:
            require(
                entry["finding"] in {"incomplete_hole", "rejected_false_statement"},
                "misleading sorry-tainted disposition",
            )
        if entry["finding"] == "incomplete_hole":
            require(holes, "hole finding needs explicit historical dependency")
        used_apis.update(entry["apis"])
        declarations[name] = entry
    require(used_apis == set(apis), "unbound destination API")
    for entry in declarations.values():
        require(
            all(n in declarations for n in entry["historical_hole_dependencies"]),
            "unbound historical hole dependency",
        )

    require(
        isinstance(ledger["records"], list)
        and len(ledger["records"]) == expected_count,
        "missing/duplicate target records",
    )
    seen = set()
    for record in ledger["records"]:
        fields(
            record,
            ("ordinal", "sourceHash", "legacy_matches", "disposition", "reasons"),
            "target",
        )
        ordinal = record["ordinal"]
        require(
            type(ordinal) is int and 0 <= ordinal < expected_count,
            "out-of-range ordinal",
        )
        require(ordinal not in seen, "duplicate target ordinal")
        seen.add(ordinal)
        expected = records[ordinal]
        require(
            record["sourceHash"] == expected["key"]["source_sha256"],
            "stale target sourceHash",
        )
        require(
            inventory.canonical(record["legacy_matches"])
            == inventory.canonical(legacy_matches(expected)),
            "legacy match join differs",
        )
        for match in record["legacy_matches"]:
            for name in match["declarations"]:
                require(name in declarations, "unbound legacy declaration")
                require(
                    declarations[name]["file"] in {f["path"] for f in match["files"]},
                    "legacy declaration file not among report hints",
                )
        status, reasons = disposition(expected, declarations)
        require(
            record["disposition"] in STATUSES and record["disposition"] == status,
            "unknown or misleading target disposition",
        )
        require(
            record["reasons"] == reasons, "missing or misleading disposition reasons"
        )
    require(seen == set(range(expected_count)), "incomplete target coverage")
    return {
        "targets": len(seen),
        "unique_source_hashes": len({r["sourceHash"] for r in ledger["records"]}),
        "legacy_report_references": sum(
            len(m["declarations"])
            for r in ledger["records"]
            for m in r["legacy_matches"]
        ),
        "legacy_declarations": len(declarations),
        "destination_api_candidates": len(apis),
        "dispositions": dict(Counter(r["disposition"] for r in ledger["records"])),
        "evidence": "source identity only; migration partial; no accepted proofs or printed fidelity",
    }


CHECKS_SCHEMA = "algebra-notes-checks/2"
TRIAGE_STATUSES = {
    "static_reuse",
    "partial_static_reuse",
    "blocked_source_api_unresolved",
    "do_not_port_parallel_definition",
    "blocked_proof_hole",
    "blocked_semantic_mismatch",
    "blocked_false_statement",
}


def identity_hash(ledger):
    return inventory.sha256(
        inventory.canonical(
            {key: ledger[key] for key in ("book", "base", "sources", "pins")}
        )
    )


def content_sha256(value):
    return inventory.sha256(inventory.canonical(value))


def row_content_sha256(row):
    """Hash every committed row field except the content-hash field itself."""
    return content_sha256(
        {key: value for key, value in row.items() if key != "row_content_sha256"}
    )


def lane_content_fingerprints(lane, triage_rows, api_rows):
    """Reproducible lane digests over the committed triage transcription."""
    lane_triage = sorted(
        (
            {key: value for key, value in row.items() if key != "row_content_sha256"}
            for row in triage_rows
            if row["lane"] == lane
        ),
        key=lambda row: row["ordinal"],
    )
    declarations = [
        {"ordinal": row["ordinal"], "legacy_declarations": row["legacy_declarations"]}
        for row in lane_triage
    ]
    lane_apis = sorted(
        (
            {key: value for key, value in row.items() if key != "row_content_sha256"}
            for row in api_rows
            if row["lane"] == lane
        ),
        key=lambda row: row["id"],
    )
    return {
        "targets_content_sha256": content_sha256(lane_triage),
        "declarations_content_sha256": content_sha256(declarations),
        "api_rows_content_sha256": content_sha256(lane_apis),
    }


def example_id(span):
    return f"bytes:{span['byte_start']}:{span['byte_end']}:{span['sha256']}"


def validate_checks(checks, ledger, root):
    """Bind fresh triage and exact test bytes; do not verify Lean or acceptance."""
    fields(
        checks,
        (
            "schema",
            "identity_sha256",
            "source_fidelity",
            "migration_gate",
            "v1_compiler_gate",
            "compiler_environments",
            "triage_sources",
            "triage_apis",
            "triage",
            "canonical_use_tests",
            "pending_targets",
        ),
        "checks index",
    )
    require(
        checks["schema"] == CHECKS_SCHEMA
        and checks["identity_sha256"] == identity_hash(ledger),
        "stale checks source/pin identity",
    )
    require(
        checks["source_fidelity"] == "unverified",
        "checks cannot verify source fidelity",
    )
    require(
        checks["migration_gate"]
        == checks["v1_compiler_gate"]
        == "parent_owned_pending",
        "canonical-use checks do not pass migration/v1 gates",
    )
    require(
        all(
            isinstance(checks[k], list)
            for k in (
                "compiler_environments",
                "triage_sources",
                "triage_apis",
                "triage",
                "canonical_use_tests",
                "pending_targets",
            )
        ),
        "checks tables must be lists",
    )
    require(
        checks["compiler_environments"] == [],
        "compiler environments require verified receipt artifacts",
    )
    sources = {}
    for source in checks["triage_sources"]:
        fields(
            source,
            (
                "lane",
                "target_count",
                "targets_content_sha256",
                "declarations_content_sha256",
                "api_rows_content_sha256",
            ),
            "triage source",
        )
        lane = source["lane"]
        require(
            isinstance(lane, str)
            and re.fullmatch(r"[a-z][a-z0-9_]*", lane)
            and lane not in sources,
            "duplicate/invalid triage lane",
        )
        require(
            type(source["target_count"]) is int and source["target_count"] > 0,
            "empty triage source",
        )
        for key in (
            "targets_content_sha256",
            "declarations_content_sha256",
            "api_rows_content_sha256",
        ):
            digest(source[key])
        sources[lane] = source
    apis = {}
    for api in checks["triage_apis"]:
        fields(
            api,
            ("id", "lane", "name", "kind", "module", "revision", "row_content_sha256"),
            "triage API",
        )
        require(
            api["lane"] in sources
            and isinstance(api["id"], str)
            and api["id"].startswith(api["lane"] + ":")
            and api["id"] not in apis,
            "duplicate or unbound triage API",
        )
        require(api["kind"] in {"named", "unnamed_instance"}, "unknown triage API kind")
        require(
            (
                api["kind"] == "named"
                and isinstance(api["name"], str)
                and api["name"]
                and not any(c.isspace() for c in api["name"])
            )
            or (api["kind"] == "unnamed_instance" and api["name"] is None),
            "invalid triage API name",
        )
        require(
            isinstance(api["module"], str)
            and re.fullmatch(
                r"(?:Mathlib|MathlibExt)(?:\.[A-Za-z_][A-Za-z0-9_']*)+", api["module"]
            ),
            "invalid triage API module",
        )
        pin = (
            ledger["pins"]["mathlib"]
            if api["module"].startswith("Mathlib.")
            else ledger["base"]
        )
        require(api["revision"] == pin, "stale triage API pin")
        digest(api["row_content_sha256"])
        require(
            api["row_content_sha256"] == row_content_sha256(api),
            "stale triage API row content hash",
        )
        apis[api["id"]] = api
    targets = {row["ordinal"]: row for row in ledger["records"]}
    triage = {}
    referenced_apis = set()
    for row in checks["triage"]:
        fields(
            row,
            (
                "lane",
                "ordinal",
                "sourceHash",
                "row_content_sha256",
                "legacy_declarations",
                "api_refs",
                "disposition",
                "scope",
                "issues",
            ),
            "fresh target triage",
        )
        require(
            row["lane"] in sources
            and type(row["ordinal"]) is int
            and row["ordinal"] in targets,
            "out-of-range or unbound triage target",
        )
        key = (row["lane"], row["ordinal"])
        require(key not in triage, "duplicate fresh target triage")
        require(
            row["sourceHash"] == targets[row["ordinal"]]["sourceHash"],
            "stale triage sourceHash",
        )
        names = [
            n
            for m in targets[row["ordinal"]]["legacy_matches"]
            for n in m["declarations"]
        ]
        require(
            isinstance(row["legacy_declarations"], list)
            and all(n in names for n in row["legacy_declarations"]),
            "unbound triage legacy declaration",
        )
        require(
            isinstance(row["api_refs"], list)
            and all(
                a in apis and apis[a]["lane"] == row["lane"] for a in row["api_refs"]
            ),
            "unbound fresh API reference",
        )
        require(
            row["disposition"] in TRIAGE_STATUSES
            and row["scope"] in {"partial", "unverified"},
            "unknown/overclaiming triage disposition or scope",
        )
        require(
            isinstance(row["issues"], list)
            and all(
                isinstance(i, str) and re.fullmatch(r"[a-z][a-z0-9_]*", i)
                for i in row["issues"]
            ),
            "invalid triage issue codes",
        )
        require(
            not row["issues"] or row["scope"] == "partial",
            "scope must retain triage issues",
        )
        digest(row["row_content_sha256"])
        require(
            row["row_content_sha256"] == row_content_sha256(row),
            "stale triage row content hash",
        )
        referenced_apis.update(row["api_refs"])
        triage[key] = row
    require(referenced_apis == set(apis), "unreferenced triage API rows")
    for lane, source in sources.items():
        require(
            sum(k[0] == lane for k in triage) == source["target_count"],
            "incomplete fresh triage coverage",
        )
        expected = lane_content_fingerprints(
            lane, checks["triage"], checks["triage_apis"]
        )
        require(
            all(source[key] == value for key, value in expected.items()),
            "stale lane content fingerprints",
        )
    covered = {key[1] for key in triage}
    pending = set()
    for row in checks["pending_targets"]:
        fields(row, ("ordinal", "sourceHash", "reason"), "pending target")
        ordinal = row["ordinal"]
        require(
            type(ordinal) is int
            and ordinal in targets
            and ordinal not in covered
            and ordinal not in pending,
            "duplicate/unbound pending target",
        )
        require(
            row["sourceHash"] == targets[ordinal]["sourceHash"]
            and row["reason"] == "missing_context",
            "stale or overclaiming pending target",
        )
        pending.add(ordinal)
    require(
        covered | pending == set(targets),
        "fresh triage/pending target coverage is incomplete",
    )

    files = set()
    examples = set()
    bindings_count = 0
    for test in checks["canonical_use_tests"]:
        fields(
            test,
            (
                "file",
                "sha256",
                "scope",
                "source_fidelity",
                "compiler_evidence",
                "bindings",
            ),
            "canonical-use test",
        )
        path = test["file"]
        require(
            isinstance(path, str)
            and path.startswith("MathlibExtTest/")
            and path.endswith(".lean")
            and PurePosixPath(path).as_posix() == path
            and ".." not in path.split("/")
            and path not in files,
            "invalid/duplicate canonical-use file",
        )
        file = root / path
        require(
            file.resolve().is_relative_to(root.resolve())
            and file.is_file()
            and not file.is_symlink(),
            "missing/escaped canonical-use file",
        )
        data = file.read_bytes()
        require(
            data and inventory.sha256(data) == test["sha256"],
            "stale canonical-use file hash",
        )
        require(
            test["scope"] == "canonical_use_only"
            and test["source_fidelity"] == "unverified",
            "canonical-use test overclaims equivalence/source fidelity",
        )
        evidence = test["compiler_evidence"]
        fields(
            evidence,
            ("status", "receipt_sha256", "environment"),
            "compiler evidence locator",
        )
        require(
            evidence
            == {
                "status": "parent_pending",
                "receipt_sha256": None,
                "environment": None,
            },
            "compiler evidence must remain parent_pending without a verified "
            "receipt artifact",
        )
        require(
            isinstance(test["bindings"], list) and test["bindings"],
            "unbound canonical-use test",
        )
        for binding in test["bindings"]:
            fields(
                binding,
                (
                    "lane",
                    "ordinal",
                    "sourceHash",
                    "api_refs",
                    "example",
                    "scope",
                    "reason",
                ),
                "canonical-use binding",
            )
            require(
                binding["scope"] == "partial"
                and binding["reason"]
                in {"component_only", "boundary_only", "compatibility_only"},
                "canonical-use binding overclaims coverage",
            )
            require(type(binding["ordinal"]) is int, "invalid canonical-use ordinal")
            key = (binding["lane"], binding["ordinal"])
            require(
                key in triage and binding["sourceHash"] == triage[key]["sourceHash"],
                "unbound/stale canonical-use target",
            )
            require(
                isinstance(binding["api_refs"], list)
                and binding["api_refs"]
                and all(a in triage[key]["api_refs"] for a in binding["api_refs"]),
                "canonical-use API does not bind this target",
            )
            span = binding["example"]
            fields(span, ("id", "byte_start", "byte_end", "sha256"), "example span")
            start, end = span["byte_start"], span["byte_end"]
            require(
                type(start) is int
                and type(end) is int
                and 0 <= start < end <= len(data),
                "missing/out-of-range example span",
            )
            require(
                inventory.sha256(data[start:end]) == span["sha256"]
                and span["id"] == example_id(span),
                "stale/unbound example bytes or id",
            )
            example_key = (path, key, span["id"])
            require(example_key not in examples, "duplicate canonical-use binding")
            examples.add(example_key)
            bindings_count += 1
        files.add(path)
    return {
        "fresh_triage_targets": len(covered),
        "pending_context_targets": len(pending),
        "canonical_use_test_files": len(files),
        "canonical_use_bindings": bindings_count,
        "parent_reported_canonical_compiles": 0,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path("."))
    parser.add_argument(
        "--source-revision",
        default=BASE,
        help="Read this tree against the frozen identities (HEAD for shallow CI)",
    )
    parser.add_argument(
        "--ledger", type=Path, default=Path("blueprint/migrations/AlgebraNotes.json")
    )
    parser.add_argument(
        "--checks",
        type=Path,
        default=Path("blueprint/migrations/AlgebraNotesChecks.json"),
    )
    args = parser.parse_args(argv)
    ledger = load_json(args.ledger.read_bytes())
    result = validate(
        ledger, inventory.GitSource(args.repo, args.source_revision), expected_base=BASE
    )
    result.update(
        validate_checks(load_json(args.checks.read_bytes()), ledger, args.repo)
    )
    result["ledger_sha256"] = inventory.sha256(args.ledger.read_bytes())
    result["checks_sha256"] = inventory.sha256(args.checks.read_bytes())
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (
        ValueError,
        KeyError,
        TypeError,
        yaml.YAMLError,
        UnicodeError,
        OSError,
        subprocess.CalledProcessError,
    ) as error:
        print(f"AlgebraNotes migration: {error}", file=sys.stderr)
        sys.exit(1)
