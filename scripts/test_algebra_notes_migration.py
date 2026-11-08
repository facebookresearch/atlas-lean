"""Invented-fixture identity/disposition regressions; no Lean or network calls."""

from contextlib import redirect_stdout
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_algebra_notes_migration as check
import inventory_v1 as inventory


class FixtureSource:
    revision = "a" * 40

    def __init__(self):
        target = {
            "description": "A token occupies a slot.",
            "kind": "rule",
            "location": "Fixture room",
            "name": "Token",
        }
        self.files = {
            "v1/Atlas/AlgebraNotes/targets.yaml": json.dumps([target] * 3).encode(),
            "v1/Atlas/AlgebraNotes/report.json": json.dumps(
                {
                    "statements": {
                        "details": [
                            {
                                "idx": 1,
                                **target,
                                "lean_declaration": "Fixture.first, Fixture.first",
                                "lean_file": "Atlas/AlgebraNotes/code/First.lean",
                                "compiles": True,
                            },
                            {
                                "idx": 0,
                                **target,
                                "lean_declaration": "Fixture.first, Fixture.second",
                                "lean_file": "Atlas/AlgebraNotes/code/Second.lean, Atlas/AlgebraNotes/code/First.lean",
                            },
                            {
                                "idx": 0,
                                **target,
                                "lean_declaration": "Fixture.first",
                                "lean_file": "Atlas/AlgebraNotes/code/First.lean",
                            },
                            {
                                "idx": 2,
                                **target,
                                "lean_declaration": "",
                                "lean_file": "",
                            },
                        ]
                    }
                }
            ).encode(),
            "v1/Atlas/AlgebraNotes/code/First.lean": b"-- invented fixture first\n",
            "v1/Atlas/AlgebraNotes/code/Second.lean": b"-- invented fixture second\n",
            "lake-manifest.json": json.dumps(
                {"packages": [{"name": "mathlib", "rev": "c" * 40}]}
            ).encode(),
            "lean-toolchain": b"leanprover/lean4:v0.0.0\n",
        }
        self.tree = {
            path: {
                "git_blob": "b" * 40,
                "kind": "blob",
                "mode": "100644",
                "bytes": len(data),
            }
            for path, data in self.files.items()
        }

    def read(self, path):
        return self.files[path]

    def provenance(self, path, data=None):
        result = {"revision": self.revision, "path": path, **self.tree[path]}
        if data is not None:
            result["sha256"] = inventory.sha256(data)
        return result


def fixture_ledger(source):
    records, summary = inventory.book_inventory(source, check.BOOK)
    declarations = [
        {
            "name": f"Fixture.{name}",
            "file": f"v1/Atlas/AlgebraNotes/code/{file}.lean",
            "git_blob": "b" * 40,
            "historical_excerpt_sha256": "d" * 64,
            "finding": "mapped_existing",
            "historical_hole_dependencies": [],
            "apis": ["fixture-api"],
        }
        for name, file in (("first", "First"), ("second", "Second"))
    ]
    ledger = {
        "schema": check.SCHEMA,
        "book": check.BOOK,
        "base": source.revision,
        "sources": check.source_refs(summary),
        "pins": {"mathlib": "c" * 40, "lean": "leanprover/lean4:v0.0.0"},
        "prior_audit": {
            "candidates_sha256": "e" * 64,
            "api_mappings_sha256": "f" * 64,
            "status": "historical_static_only",
        },
        "migration": "partial",
        "printed_source": {"status": "unverified_no_primary_bytes", "sha256": None},
        "gates": dict(check.GATES),
        "proof_receipts": [],
        "legacy_declarations": declarations,
        "destination_apis": [
            {
                "id": "fixture-api",
                "name": "Fixture.libraryToken",
                "module": "Mathlib.Fixture.Token",
                "revision": "c" * 40,
                "relation": "replacement_candidate",
                "scope": "unverified",
                "reason": "static_shape_only",
            }
        ],
        "records": [],
    }
    by_name = {row["name"]: row for row in declarations}
    for record in records:
        status, reasons = check.disposition(record, by_name)
        ledger["records"].append(
            {
                "ordinal": record["key"]["target_ordinal"],
                "sourceHash": record["key"]["source_sha256"],
                "legacy_matches": check.legacy_matches(record),
                "disposition": status,
                "reasons": reasons,
            }
        )
    return ledger


def fixture_checks(ledger):
    api = {
        "id": "fixture:api",
        "lane": "fixture",
        "name": "Fixture.libraryToken",
        "kind": "named",
        "module": "Mathlib.Fixture.Token",
        "revision": "c" * 40,
    }
    api["row_content_sha256"] = check.row_content_sha256(api)
    row = {
        "lane": "fixture",
        "ordinal": 1,
        "sourceHash": ledger["records"][1]["sourceHash"],
        "legacy_declarations": ["Fixture.first"],
        "api_refs": ["fixture:api"],
        "disposition": "static_reuse",
        "scope": "unverified",
        "issues": [],
    }
    row["row_content_sha256"] = check.row_content_sha256(row)
    return {
        "schema": check.CHECKS_SCHEMA,
        "identity_sha256": check.identity_hash(ledger),
        "source_fidelity": "unverified",
        "migration_gate": "parent_owned_pending",
        "v1_compiler_gate": "parent_owned_pending",
        "compiler_environments": [],
        "triage_sources": [
            {
                "lane": "fixture",
                "target_count": 1,
                **check.lane_content_fingerprints("fixture", [row], [api]),
            }
        ],
        "triage_apis": [api],
        "triage": [row],
        "canonical_use_tests": [],
        "pending_targets": [
            {
                "ordinal": i,
                "sourceHash": ledger["records"][i]["sourceHash"],
                "reason": "missing_context",
            }
            for i in (0, 2)
        ],
    }


class MigrationLedger(unittest.TestCase):
    def setUp(self):
        self.source = FixtureSource()
        self.ledger = fixture_ledger(self.source)

    def validate(self, ledger=None):
        return check.validate(
            self.ledger if ledger is None else ledger, self.source, expected_count=3
        )

    def rejected(self, mutate, message):
        changed = copy.deepcopy(self.ledger)
        mutate(changed)
        with self.assertRaisesRegex(ValueError, message):
            self.validate(changed)

    def test_populated_positive_preserves_duplicate_targets_and_declarations(self):
        result = self.validate()
        self.assertEqual(result["targets"], 3)
        self.assertEqual(result["unique_source_hashes"], 1)
        self.assertEqual(result["legacy_report_references"], 5)
        self.assertEqual(
            result["dispositions"], {"partial_source": 2, "static_candidate": 1}
        )
        self.assertEqual(
            self.ledger["records"][1]["legacy_matches"][0]["declarations"],
            ["Fixture.first", "Fixture.first"],
        )

    def test_missing_extra_and_empty_records_fail(self):
        for records in (self.ledger["records"][:-1], self.ledger["records"] * 2, []):
            self.rejected(
                lambda ledger: ledger.update(records=records), "target records"
            )

    def test_duplicate_ordinal_fails_even_with_matching_source_hash(self):
        self.rejected(
            lambda ledger: ledger["records"][1].update(ordinal=0),
            "duplicate target ordinal",
        )

    def test_out_of_range_boolean_and_negative_ordinals(self):
        for ordinal in (-1, 3, True, "0"):
            self.rejected(
                lambda ledger: ledger["records"][0].update(ordinal=ordinal),
                "out-of-range",
            )

    def test_stale_target_and_file_hashes_fail(self):
        self.rejected(
            lambda ledger: ledger["records"][0].update(sourceHash="0" * 64),
            "sourceHash",
        )
        for index in (0, 1):
            self.rejected(
                lambda ledger: ledger["sources"][index].update(sha256="0" * 64),
                "source/report fingerprints",
            )
        self.rejected(
            lambda ledger: ledger["legacy_declarations"][0].update(git_blob="0" * 40),
            "legacy file fingerprint",
        )
        self.rejected(lambda ledger: ledger.update(base="0" * 40), "source revision")

    def test_each_legacy_join_component_is_checked(self):
        for field, value in (
            ("row", 9),
            ("hash", "0" * 64),
            ("declarations", ["Fixture.second"]),
            ("files", []),
        ):
            self.rejected(
                lambda ledger: ledger["records"][0]["legacy_matches"][0].update(
                    {field: value}
                ),
                "legacy match join",
            )
        self.rejected(
            lambda ledger: ledger["records"][1]["legacy_matches"][0].update(
                declarations=["Fixture.first"]
            ),
            "legacy match join",
        )

    def test_unbound_evidence_and_api_references_fail(self):
        self.rejected(
            lambda ledger: ledger.update(
                proof_receipts=[{"ordinal": 99, "compiled": True}]
            ),
            "unbound proof evidence",
        )
        self.rejected(
            lambda ledger: ledger["legacy_declarations"][0].update(apis=["absent"]),
            "unbound API",
        )
        self.rejected(
            lambda ledger: ledger["destination_apis"].append(
                {**ledger["destination_apis"][0], "id": "orphan"}
            ),
            "unbound destination API",
        )
        self.rejected(
            lambda ledger: ledger["legacy_declarations"].pop(0),
            "unbound legacy declaration",
        )

    def test_status_and_identity_are_not_proof_badges(self):
        self.rejected(lambda ledger: ledger.update(migration="complete"), "partial")
        self.rejected(
            lambda ledger: ledger["records"][1].update(disposition="accepted"),
            "disposition",
        )
        self.rejected(
            lambda ledger: ledger["records"][0].update(disposition="static_candidate"),
            "disposition",
        )
        self.rejected(lambda ledger: ledger["records"][1].update(reasons=[]), "reasons")
        self.rejected(
            lambda ledger: ledger["gates"].update(compiler="passed"), "parent-owned"
        )
        self.rejected(
            lambda ledger: ledger["printed_source"].update(status="verified"),
            "printed source fidelity",
        )
        self.rejected(
            lambda ledger: ledger["records"][1].update(compiled=True), "fields"
        )
        self.rejected(
            lambda ledger: ledger["destination_apis"][0].update(
                relation="formal_equivalence"
            ),
            "static",
        )

    def test_false_and_sorry_dispositions_stay_explicit(self):
        for finding, status in (
            ("rejected_false_statement", "blocked_false"),
            ("incomplete_hole", "blocked_sorry"),
        ):
            ledger = copy.deepcopy(self.ledger)
            entry = ledger["legacy_declarations"][0]
            entry["finding"] = finding
            entry["historical_hole_dependencies"] = [entry["name"]]
            records, _ = inventory.book_inventory(self.source, check.BOOK)
            by_name = {row["name"]: row for row in ledger["legacy_declarations"]}
            for record, expected in zip(ledger["records"], records):
                record["disposition"], record["reasons"] = check.disposition(
                    expected, by_name
                )
            self.assertEqual(ledger["records"][1]["disposition"], status)
            self.validate(ledger)
            ledger["records"][1]["disposition"] = "static_candidate"
            with self.assertRaisesRegex(ValueError, "disposition"):
                self.validate(ledger)
        self.rejected(
            lambda ledger: ledger["legacy_declarations"][0].update(
                historical_hole_dependencies=["Fixture.first"]
            ),
            "sorry-tainted",
        )

    def test_static_api_and_toolchain_pins_are_checked(self):
        self.rejected(lambda ledger: ledger["pins"].update(mathlib="0" * 40), "pins")
        self.rejected(
            lambda ledger: ledger["pins"].update(lean="leanprover/lean4:v99.0.0"),
            "pins",
        )
        self.rejected(
            lambda ledger: ledger["destination_apis"][0].update(revision="0" * 40),
            "API pin",
        )

    def test_mapping_scope_is_explicit_and_cannot_be_promoted(self):
        self.rejected(
            lambda ledger: ledger["destination_apis"][0].update(
                scope="source_faithful"
            ),
            "scope/reason",
        )
        self.rejected(
            lambda ledger: ledger["destination_apis"][0].update(reason="verified"),
            "scope/reason",
        )

    def test_candidate_tree_identity_check_does_not_require_ancestry(self):
        frozen = self.source.revision
        self.source.revision = "9" * 40
        self.assertEqual(
            check.validate(
                self.ledger, self.source, expected_count=3, expected_base=frozen
            )["targets"],
            3,
        )
        self.source.files["v1/Atlas/AlgebraNotes/report.json"] += b"\n"
        with self.assertRaisesRegex(ValueError, "fingerprints"):
            check.validate(
                self.ledger, self.source, expected_count=3, expected_base=frozen
            )

    def test_changed_pinned_metadata_cannot_be_a_no_op(self):
        # Same ordinals and unchanged declared hashes: actual source bytes changed.
        self.source.files["v1/Atlas/AlgebraNotes/targets.yaml"] = self.source.files[
            "v1/Atlas/AlgebraNotes/targets.yaml"
        ].replace(b"token", b"parcel")
        with self.assertRaisesRegex(ValueError, "fingerprints"):
            self.validate()

    def test_empty_source_is_not_success(self):
        del self.source.tree["v1/Atlas/AlgebraNotes/targets.yaml"]
        with self.assertRaisesRegex(ValueError, "empty source"):
            self.validate()

    def test_strict_json_rejects_duplicate_fields_and_nonfinite(self):
        for data in (
            b'{"ordinal":0,"ordinal":1}',
            b'{"number":NaN}',
            b'{"number":1e9999}',
        ):
            with self.assertRaises(ValueError):
                check.load_json(data)

    def test_cli_emits_populated_summary_and_missing_ledger_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "ledger.json"
            path.write_bytes(inventory.canonical(self.ledger))
            index = Path(directory) / "checks.json"
            index.write_bytes(inventory.canonical(fixture_checks(self.ledger)))
            output = io.StringIO()
            real_validate = check.validate

            def fixture_validate(ledger, source, **kwargs):
                return real_validate(ledger, source, expected_count=3)

            with patch.object(
                inventory, "GitSource", return_value=self.source
            ), patch.object(
                check, "validate", side_effect=fixture_validate
            ), redirect_stdout(
                output
            ):
                self.assertEqual(
                    check.main(["--ledger", str(path), "--checks", str(index)]), 0
                )
            self.assertEqual(json.loads(output.getvalue())["targets"], 3)
            path.unlink()
            with self.assertRaises(FileNotFoundError):
                check.main(["--ledger", str(path)])


class CanonicalUseIndex(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.ledger = fixture_ledger(FixtureSource())
        self.checks = fixture_checks(self.ledger)
        self.file = self.root / "MathlibExtTest/Fixture/CanonicalUse.lean"
        self.file.parent.mkdir(parents=True)
        # Invented bytes, not Lean proof evidence: this tests the identity index.
        self.data = b"fixture slot A\nfixture slot B\n"
        self.file.write_bytes(self.data)
        span = {
            "byte_start": 0,
            "byte_end": 15,
            "sha256": inventory.sha256(self.data[:15]),
        }
        span["id"] = check.example_id(span)
        self.checks["canonical_use_tests"] = [
            {
                "file": "MathlibExtTest/Fixture/CanonicalUse.lean",
                "sha256": inventory.sha256(self.data),
                "scope": "canonical_use_only",
                "source_fidelity": "unverified",
                "compiler_evidence": {
                    "status": "parent_pending",
                    "receipt_sha256": None,
                    "environment": None,
                },
                "bindings": [
                    {
                        "lane": "fixture",
                        "ordinal": 1,
                        "sourceHash": self.ledger["records"][1]["sourceHash"],
                        "api_refs": ["fixture:api"],
                        "example": span,
                        "scope": "partial",
                        "reason": "component_only",
                    }
                ],
            }
        ]

    def validate(self, checks=None):
        return check.validate_checks(
            self.checks if checks is None else checks, self.ledger, self.root
        )

    def rejected(self, mutate, message):
        changed = copy.deepcopy(self.checks)
        mutate(changed)
        with self.assertRaisesRegex(ValueError, message):
            self.validate(changed)

    def test_populated_file_example_api_and_target_binding(self):
        self.assertEqual(
            self.validate(),
            {
                "fresh_triage_targets": 1,
                "pending_context_targets": 2,
                "canonical_use_test_files": 1,
                "canonical_use_bindings": 1,
                "parent_reported_canonical_compiles": 0,
            },
        )
        self.assertNotIn("accepted", self.validate())

    def test_missing_and_stale_actual_file_fail(self):
        self.file.unlink()
        with self.assertRaisesRegex(ValueError, "missing"):
            self.validate()
        self.file.write_bytes(self.data + b"stale addition")
        with self.assertRaisesRegex(ValueError, "file hash"):
            self.validate()

    def test_example_span_hash_id_and_range_fail(self):
        for changes in (
            {"id": "absent-example"},
            {"sha256": "0" * 64},
            {"byte_start": -1},
            {"byte_start": True},
            {"byte_end": 1000},
        ):
            self.rejected(
                lambda index: index["canonical_use_tests"][0]["bindings"][0][
                    "example"
                ].update(changes),
                "example",
            )

    def test_target_hash_api_and_lane_must_bind_this_example(self):
        for changes in ({"ordinal": 0}, {"sourceHash": "0" * 64}, {"lane": "unknown"}):
            self.rejected(
                lambda index: index["canonical_use_tests"][0]["bindings"][0].update(
                    changes
                ),
                "target",
            )
        self.rejected(
            lambda index: index["canonical_use_tests"][0]["bindings"][0].update(
                api_refs=["fixture:absent"]
            ),
            "API",
        )
        self.rejected(
            lambda index: index["canonical_use_tests"][0].update(bindings=[]), "unbound"
        )
        self.rejected(
            lambda index: index["canonical_use_tests"][0]["bindings"].append(
                copy.deepcopy(index["canonical_use_tests"][0]["bindings"][0])
            ),
            "duplicate",
        )

    def test_missing_duplicate_stale_and_overclaiming_triage_fail(self):
        self.rejected(lambda index: index.update(triage=[], triage_apis=[]), "coverage")
        self.rejected(
            lambda index: index["triage"].append(copy.deepcopy(index["triage"][0])),
            "duplicate",
        )
        self.rejected(
            lambda index: index["triage"][0].update(sourceHash="0" * 64), "sourceHash"
        )
        self.rejected(
            lambda index: index["triage"][0].update(api_refs=["absent"]), "API"
        )
        self.rejected(
            lambda index: index["triage"][0].update(scope="source_faithful"), "scope"
        )
        self.rejected(
            lambda index: index["triage"][0].update(disposition="accepted"),
            "disposition",
        )
        self.rejected(
            lambda index: index["triage"][0].update(issues=["missing_case"]), "scope"
        )
        self.rejected(
            lambda index: index["triage_apis"][0].update(revision="0" * 40), "API pin"
        )
        self.rejected(
            lambda index: index.update(identity_sha256="0" * 64), "source/pin identity"
        )

    def test_triage_content_hashes_reject_tampering(self):
        self.rejected(
            lambda index: index["triage"][0].update(disposition="partial_static_reuse"),
            "triage row content hash",
        )
        self.rejected(
            lambda index: index["triage"][0].update(row_content_sha256="0" * 64),
            "triage row content hash",
        )
        self.rejected(
            lambda index: index["triage_apis"][0].update(name="Fixture.otherToken"),
            "API row content hash",
        )
        self.rejected(
            lambda index: index["triage_apis"][0].update(row_content_sha256="0" * 64),
            "API row content hash",
        )
        for key in (
            "targets_content_sha256",
            "declarations_content_sha256",
            "api_rows_content_sha256",
        ):
            self.rejected(
                lambda index, key=key: index["triage_sources"][0].update(
                    {key: "0" * 64}
                ),
                "lane content fingerprints",
            )

    def test_canonical_use_cannot_pass_migration_source_or_equivalence_gates(self):
        self.rejected(
            lambda index: index.update(migration_gate="passed"), "migration/v1"
        )
        self.rejected(
            lambda index: index.update(v1_compiler_gate="passed"), "migration/v1"
        )
        self.rejected(
            lambda index: index.update(source_fidelity="verified"), "source fidelity"
        )
        self.rejected(
            lambda index: index["canonical_use_tests"][0].update(
                scope="formal_equivalence"
            ),
            "overclaims",
        )
        self.rejected(
            lambda index: index["canonical_use_tests"][0].update(
                source_fidelity="verified"
            ),
            "overclaims",
        )
        self.rejected(
            lambda index: index["canonical_use_tests"][0].update(accepted=True),
            "fields",
        )
        self.rejected(
            lambda index: index["canonical_use_tests"][0]["bindings"][0].update(
                scope="complete"
            ),
            "overclaims coverage",
        )
        self.rejected(
            lambda index: index["canonical_use_tests"][0]["bindings"][0].update(
                reason="source_faithful"
            ),
            "overclaims coverage",
        )
        self.rejected(
            lambda index: index["canonical_use_tests"][0]["compiler_evidence"].update(
                status="accepted"
            ),
            "parent_pending",
        )
        self.rejected(
            lambda index: index["canonical_use_tests"][0]["compiler_evidence"].update(
                status="parent_reported_full_compile"
            ),
            "parent_pending",
        )
        self.rejected(
            lambda index: index["canonical_use_tests"][0]["compiler_evidence"].update(
                receipt_sha256="6" * 64
            ),
            "parent_pending",
        )

    def test_overlapping_lanes_count_distinct_target_once(self):
        api = copy.deepcopy(self.checks["triage_apis"][0])
        api.update(id="parallel:api", lane="parallel")
        api["row_content_sha256"] = check.row_content_sha256(api)
        self.checks["triage_apis"].append(api)
        observation = copy.deepcopy(self.checks["triage"][0])
        observation.update(lane="parallel", api_refs=["parallel:api"])
        observation["row_content_sha256"] = check.row_content_sha256(observation)
        self.checks["triage"].append(observation)
        source = copy.deepcopy(self.checks["triage_sources"][0])
        source["lane"] = "parallel"
        source.update(
            check.lane_content_fingerprints(
                "parallel", self.checks["triage"], self.checks["triage_apis"]
            )
        )
        self.checks["triage_sources"].append(source)
        self.assertEqual(len(self.checks["triage"]), 2)
        self.assertEqual(self.validate()["fresh_triage_targets"], 1)

    def test_pending_context_must_account_for_every_untriaged_target(self):
        self.rejected(lambda index: index.update(pending_targets=[]), "coverage")
        self.rejected(
            lambda index: index["pending_targets"].append(
                copy.deepcopy(index["pending_targets"][0])
            ),
            "duplicate",
        )
        self.rejected(
            lambda index: index["pending_targets"][0].update(ordinal=1),
            "pending target",
        )
        self.rejected(
            lambda index: index["pending_targets"][0].update(sourceHash="0" * 64),
            "pending target",
        )
        self.rejected(
            lambda index: index["pending_targets"][0].update(reason="accepted"),
            "pending target",
        )

    def test_compiler_evidence_requires_verified_receipt_artifact(self):
        self.rejected(
            lambda index: index["canonical_use_tests"][0].update(
                compiler_evidence={
                    "status": "parent_reported_full_compile",
                    "receipt_sha256": "6" * 64,
                    "environment": "fixture-vm",
                }
            ),
            "parent_pending",
        )
        self.rejected(
            lambda index: index.update(
                compiler_environments=[
                    {
                        "id": "fixture-vm",
                        "lean": "leanprover/lean4:v0.0.1",
                        "mathlib": "9" * 40,
                        "image": "fixture-image",
                        "receipt_sha256": "7" * 64,
                    }
                ]
            ),
            "verified receipt artifacts",
        )
        self.assertEqual(self.validate()["parent_reported_canonical_compiles"], 0)

    def test_unreferenced_triage_api_rows_fail(self):
        orphan = copy.deepcopy(self.checks["triage_apis"][0])
        orphan.update(id="fixture:orphan", name="Fixture.orphanToken")
        orphan["row_content_sha256"] = check.row_content_sha256(orphan)
        self.rejected(
            lambda index: index["triage_apis"].append(orphan),
            "unreferenced triage API",
        )

    def test_test_paths_are_confined_and_duplicate_files_fail(self):
        self.rejected(
            lambda index: index["canonical_use_tests"][0].update(
                file="MathlibExtTest/../outside.lean"
            ),
            "file",
        )
        self.rejected(
            lambda index: index["canonical_use_tests"].append(
                copy.deepcopy(index["canonical_use_tests"][0])
            ),
            "duplicate",
        )
        self.file.unlink()
        outside = self.root / "outside"
        outside.write_bytes(self.data)
        self.file.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "escaped"):
            self.validate()


if __name__ == "__main__":
    unittest.main()
