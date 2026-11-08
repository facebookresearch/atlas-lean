"""Invented-fixture regressions for the metadata inventory; never invokes Lean."""

import errno
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import yaml

import inventory_v1 as inventory


TARGET = {
    "description": "A storage slot keeps its assigned token.",
    "kind": "rule",
    "location": "Fixture room A",
    "name": "Storage rule",
}


def targets_bytes(*targets):
    return yaml.safe_dump(
        [dict(target) for target in targets], sort_keys=False, allow_unicode=True
    ).encode()


def report_row(idx=0, **extra):
    return {"idx": idx, **TARGET, **extra}


def report_bytes(*rows):
    return json.dumps(
        {
            "repo": {"compiles": True, "compilation_output": "Fixture-only assertion"},
            "statements": {"summary": {"passed": len(rows)}, "details": list(rows)},
        }
    ).encode()


def overflow_report(section, literal):
    report = json.loads(report_bytes(report_row()))
    if section == "header":
        report["repo"]["numeric_claim"] = "OVERFLOW"
    else:
        report["statements"]["details"][0]["scores"] = {"quality": "OVERFLOW"}
    return json.dumps(report).encode().replace(b'"OVERFLOW"', literal.encode())


class FakeSource:
    revision = "a" * 40

    def __init__(self, files):
        self.files = files
        self.commands = []
        self.tree = {
            path: {
                "git_blob": "b" * 40,
                "kind": "blob",
                "mode": "100644",
                "bytes": len(data),
            }
            for path, data in files.items()
        }

    def read(self, path):
        return self.files[path]

    def provenance(self, path, data=None):
        record = {"path": path, "revision": self.revision, **self.tree[path]}
        if data is not None:
            record["sha256"] = inventory.sha256(data)
        return record


def fixture_source(targets=None, rows=None, files=None):
    data = {
        "v1/Atlas/FixtureBook/targets.yaml": targets_bytes(*(targets or [TARGET])),
        "v1/Atlas/FixtureBook/report.json": report_bytes(
            *(rows if rows is not None else [report_row()])
        ),
    }
    data.update(files or {})
    return FakeSource(data)


class YamlParsing(unittest.TestCase):
    def test_plain_and_folded_quoted_strings(self):
        data = b"- description: 'A token''s\n    assigned place'\n  kind: rule\n  location: Fixture A\n  name: Token\n"
        result = inventory.parse_targets(data)[0]
        self.assertEqual(result["fields"]["description"], "A token's assigned place")

    def test_block_and_escaped_strings(self):
        data = b'- description: |\n    first line\n    second line\n  kind: rule\n  location: "Room \\u03b1"\n  name: Token\n'
        result = inventory.parse_targets(data)[0]["fields"]
        self.assertEqual(result["description"], "first line\nsecond line\n")
        self.assertEqual(result["location"], "Room α")

    def test_flow_style_and_comments(self):
        data = b'[{description: "Token #1", kind: rule, location: A, name: Token}] # note\n'
        self.assertEqual(
            inventory.parse_targets(data)[0]["fields"]["description"], "Token #1"
        )

    def test_utf8_crlf_exact_span(self):
        data = targets_bytes({**TARGET, "description": "α token 🧩"}, TARGET).replace(
            b"\n", b"\r\n"
        )
        rows = inventory.parse_targets(data)
        self.assertEqual(len(rows), 2)
        for row in rows:
            span = row["span"]
            raw = data[span["byte_start"] : span["byte_end"]]
            self.assertEqual(inventory.sha256(raw), span["raw_sha256"])
            # A mapping-node span excludes the sequence dash and first-line indent.
            self.assertEqual(yaml.safe_load(b"  " + raw), row["fields"])
        self.assertGreater(rows[1]["span"]["byte_start"], rows[0]["span"]["byte_start"])

    def test_inclusive_citations_exclude_inter_target_trivia(self):
        first = targets_bytes(TARGET)
        data = first + b"\n# between targets\n\n" + targets_bytes(TARGET)
        rows = inventory.parse_targets(data)
        self.assertEqual(
            (rows[0]["span"]["line_start"], rows[0]["span"]["line_end"]), (1, 4)
        )
        self.assertEqual(
            (rows[1]["span"]["line_start"], rows[1]["span"]["line_end"]), (8, 11)
        )
        raw = data[rows[0]["span"]["byte_start"] : rows[0]["span"]["byte_end"]]
        self.assertNotIn(b"# between targets", raw)
        self.assertEqual(
            rows[0]["span"]["raw_sha256"],
            inventory.parse_targets(first)[0]["span"]["raw_sha256"],
        )
        self.assertLess(rows[0]["span"]["line_end"], rows[1]["span"]["line_start"])

    def test_literal_hash_content_and_keep_chomping_blanks(self):
        data = (
            b"- kind: rule\n  location: Fixture A\n  name: Token\n"
            b"  description: |+\n    first line\n    # literal data\n\n\n"
            b"# separator\n" + targets_bytes(TARGET)
        )
        rows = inventory.parse_targets(data)
        span = rows[0]["span"]
        raw = data[span["byte_start"] : span["byte_end"]]
        self.assertEqual(
            rows[0]["fields"]["description"], "first line\n# literal data\n\n\n"
        )
        self.assertIn(b"    # literal data\n\n\n", raw)
        self.assertNotIn(b"# separator", raw)
        self.assertEqual(span["line_end"], 8)
        self.assertEqual(yaml.safe_load(b"  " + raw), rows[0]["fields"])

    def test_quoted_hash_content_and_blank_line(self):
        data = (
            b"- kind: rule\n  location: Fixture A\n  name: Token\n"
            b"  description: 'first\n    # quoted data\n\n    final'\n"
            b"# separator\n" + targets_bytes(TARGET)
        )
        row = inventory.parse_targets(data)[0]
        raw = data[row["span"]["byte_start"] : row["span"]["byte_end"]]
        self.assertIn(b"# quoted data\n\n", raw)
        self.assertNotIn(b"# separator", raw)
        self.assertEqual(row["span"]["line_end"], 7)
        self.assertEqual(yaml.safe_load(b"  " + raw), row["fields"])

    def test_flow_mapping_braces_in_raw_span(self):
        data = yaml.safe_dump(
            [dict(TARGET), dict(TARGET)], default_flow_style=True, sort_keys=False
        ).encode()
        for row in inventory.parse_targets(data):
            span = row["span"]
            raw = data[span["byte_start"] : span["byte_end"]]
            self.assertTrue(raw.startswith(b"{") and raw.endswith(b"}"))
            self.assertEqual(yaml.safe_load(raw), row["fields"])

    def test_hash_ignores_formatting_not_value_changes(self):
        one = inventory.parse_targets(targets_bytes(TARGET))[0]
        other = inventory.parse_targets(
            targets_bytes(TARGET).replace(b"  kind: rule", b"  kind: 'rule'")
        )[0]
        changed = inventory.parse_targets(targets_bytes({**TARGET, "name": "Other"}))[0]
        self.assertEqual(one["source_sha256"], other["source_sha256"])
        self.assertNotEqual(one["span"]["raw_sha256"], other["span"]["raw_sha256"])
        self.assertNotEqual(one["source_sha256"], changed["source_sha256"])

    def test_duplicate_key_rejected(self):
        with self.assertRaisesRegex(ValueError, "Duplicate YAML key"):
            inventory.parse_targets(targets_bytes(TARGET) + b"  name: Repeated\n")

    def test_alias_and_merge_rejected(self):
        for data in (
            b"- &entry {description: x, kind: rule, location: A, name: Token}\n- *entry\n",
            b"- {<<: {name: Token}, description: x, kind: rule, location: A}\n",
        ):
            with self.subTest(data=data), self.assertRaises(ValueError):
                inventory.parse_targets(data)

    def test_unknown_unsafe_tag_rejected(self):
        with self.assertRaises(yaml.YAMLError):
            inventory.parse_targets(b"- !!python/object:unknown.Type {}\n")

    def test_expected_schema_rejected(self):
        bad = [
            b"",
            b"[]",
            b"name: x",
            targets_bytes({**TARGET, "extra": "x"}),
            targets_bytes(
                {key: value for key, value in TARGET.items() if key != "name"}
            ),
            targets_bytes({**TARGET, "name": None}),
            targets_bytes({**TARGET, "name": True}),
        ]
        for data in bad:
            with self.subTest(data=data), self.assertRaises(ValueError):
                inventory.parse_targets(data)


class ReportParsing(unittest.TestCase):
    def test_valid_report_and_duplicate_ordinals_retained(self):
        rows = inventory.parse_report(report_bytes(report_row(), report_row()))[
            "statements"
        ]["details"]
        self.assertEqual(len(rows), 2)

    def test_duplicate_json_key_rejected(self):
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            inventory.parse_report(b'{"statements":{"details":[],"details":[]}}')

    def test_bad_schema(self):
        bad = [
            b"[]",
            b"{}",
            b'{"statements": []}',
            b'{"statements":{"details":{}}}',
            report_bytes(report_row(idx=True)),
            report_bytes(report_row(idx=-1)),
            report_bytes(report_row(idx="0")),
            report_bytes(report_row(name=None)),
            report_bytes(report_row(lean_file=[])),
        ]
        for data in bad:
            with self.subTest(data=data), self.assertRaises(ValueError):
                inventory.parse_report(data)

    def test_overflow_literals_rejected_in_headers_and_rows(self):
        for section in ("header", "row"):
            for literal in ("1e9999", "-1e9999"):
                with self.subTest(section=section, literal=literal):
                    with self.assertRaisesRegex(ValueError, "Non-finite JSON"):
                        inventory.parse_report(overflow_report(section, literal))

    def test_large_finite_numbers_preserved(self):
        for section in ("header", "row"):
            with self.subTest(section=section):
                report = inventory.parse_report(overflow_report(section, "1e308"))
                value = (
                    report["repo"]["numeric_claim"]
                    if section == "header"
                    else report["statements"]["details"][0]["scores"]["quality"]
                )
                self.assertEqual(value, 1e308)

    def test_underflow_and_precision_loss_literals_rejected(self):
        for section in ("header", "row"):
            for literal in (
                "1e-9999",
                "-1e-9999",
                "1.0000000000000000000000000000000001",
            ):
                with self.subTest(section=section, literal=literal):
                    with self.assertRaisesRegex(
                        ValueError, "not exactly representable"
                    ):
                        inventory.parse_report(overflow_report(section, literal))

    def test_shortest_repr_decimals_preserved(self):
        for literal, expected in (("0.1", 0.1), ("1e22", 1e22), ("5e-324", 5e-324)):
            with self.subTest(literal=literal):
                self.assertEqual(inventory.finite_float(literal), expected)

    def test_nonfinite_values_rejected(self):
        with self.assertRaisesRegex(ValueError, "Non-finite JSON"):
            inventory.parse_report(b'{"statements":{"details":[]},"score":NaN}')


class InventoryRelations(unittest.TestCase):
    def test_many_to_many_historical_join(self):
        path = "v1/Atlas/FixtureBook/code/Token.lean"
        rows = [
            report_row(
                idx=i,
                lean_declaration="Storage.token, Storage.slot",
                lean_file=path,
                axioms="fixtureAx",
                deps="Storage.helper",
            )
            for i in range(2)
        ]
        records, summary = inventory.book_inventory(
            fixture_source(
                targets=[TARGET, TARGET], rows=rows, files={path: b"invented bytes"}
            ),
            "FixtureBook",
        )
        self.assertEqual(summary["reported_declaration_reference_count"], 4)
        self.assertEqual(summary["reported_unique_declaration_name_count"], 2)
        self.assertEqual(
            summary["shared_reported_declarations"]["Storage.token"], [0, 1]
        )
        self.assertEqual(
            summary["report_mentioned_non_target_dependencies"], ["Storage.helper"]
        )
        self.assertEqual(records[0]["duplicate_source_ordinals"], [0, 1])
        self.assertEqual(records[1]["duplicate_source_ordinals"], [0, 1])
        self.assertEqual(
            records[0]["legacy_matches"][0]["declarations"],
            ["Storage.token", "Storage.slot"],
        )
        self.assertEqual(
            records[0]["legacy_matches"][0]["historical_report"]["evidence"],
            inventory.HISTORICAL,
        )
        self.assertEqual(
            summary["historical_report_metadata"]["evidence"], inventory.HISTORICAL
        )
        self.assertIn("git_blob", records[0]["legacy_matches"][0]["files"][0])

    def test_unique_target_has_no_duplicate_source_ordinals(self):
        records, _summary = inventory.book_inventory(
            fixture_source(targets=[TARGET], rows=[], files={}),
            "FixtureBook",
        )
        self.assertEqual(records[0]["duplicate_source_ordinals"], [])

    def test_missing_row_file_and_declaration(self):
        source = fixture_source(
            targets=[TARGET, TARGET],
            rows=[report_row(lean_file="Atlas/FixtureBook/code/Absent.lean")],
        )
        records, summary = inventory.book_inventory(source, "FixtureBook")
        self.assertIn("reported_file_missing", records[0]["gaps"])
        self.assertIn("no_reported_declaration", records[0]["gaps"])
        self.assertIn("missing_report_row", records[1]["gaps"])
        del source.tree["v1/Atlas/FixtureBook/report.json"]
        records, summary = inventory.book_inventory(source, "FixtureBook")
        self.assertEqual(records[0]["gaps"], ["missing_report_file"])
        self.assertEqual(
            summary["missing_metadata_files"], ["v1/Atlas/FixtureBook/report.json"]
        )

    def test_missing_source_and_orphan_rows(self):
        source = fixture_source(rows=[report_row(idx=3)])
        del source.tree["v1/Atlas/FixtureBook/targets.yaml"]
        records, summary = inventory.book_inventory(source, "FixtureBook")
        self.assertEqual(records, [])
        self.assertEqual(
            summary["orphan_report_rows"][0]["historical_report"]["claims"]["idx"], 3
        )
        self.assertEqual(
            summary["missing_metadata_files"], ["v1/Atlas/FixtureBook/targets.yaml"]
        )

    def test_ambiguous_report_rows_and_metadata_difference(self):
        rows = [
            report_row(),
            report_row(description="A different fixture rule."),
            report_row(idx=8),
        ]
        records, summary = inventory.book_inventory(
            fixture_source(rows=rows), "FixtureBook"
        )
        self.assertIn("ambiguous_report_ordinal", records[0]["gaps"])
        self.assertIn("report_metadata_differs", records[0]["gaps"])
        self.assertEqual(len(records[0]["legacy_matches"]), 2)
        self.assertEqual(
            records[0]["legacy_matches"][1]["metadata_difference_fields"],
            ["description"],
        )
        self.assertEqual(len(summary["orphan_report_rows"]), 1)

    def test_optional_and_ambiguous_existing_roadmap_pointers(self):
        prior = FakeSource(
            {
                "blueprint/roadmap/A/FixtureBook/001-token.md": b"fixture article",
                "blueprint/roadmap/B/FixtureBook/001-token.md": b"other fixture article",
                "blueprint/roadmap/A/OtherBook/001-token.md": b"unrelated article",
                "blueprint/roadmap/FixtureBook/OtherBook/001-token.md": b"category collision",
            }
        )
        records, _ = inventory.book_inventory(fixture_source(), "FixtureBook", prior)
        self.assertEqual(len(records[0]["prior_roadmap_candidates"]), 2)
        records, _ = inventory.book_inventory(fixture_source(), "FixtureBook")
        self.assertEqual(records[0]["prior_roadmap_candidates"], [])


class GitSourceProvenance(unittest.TestCase):
    def _git(self, repo, *args, env=None):
        command = [
            "git", "-C", str(repo),
            "-c", "user.name=Inventory Fixture",
            "-c", "user.email=fixture@example.invalid",
            *args,
        ]
        return subprocess.check_output(command, env=env).decode().strip()

    def test_replace_ref_does_not_substitute_snapshot_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            self._git(repo, "init", "-q")
            (repo / "x.txt").write_bytes(b"original\n")
            self._git(repo, "add", "x.txt")
            self._git(repo, "commit", "-qm", "original")
            original = self._git(repo, "rev-parse", "HEAD")
            original_blob = self._git(repo, "rev-parse", "HEAD:x.txt")
            (repo / "x.txt").write_bytes(b"replacement\n")
            self._git(repo, "add", "x.txt")
            self._git(repo, "commit", "-qm", "replacement")
            replacement = self._git(repo, "rev-parse", "HEAD")
            self._git(repo, "replace", original, replacement)
            # Sanity: plain git really serves the substituted bytes here.
            self.assertEqual(
                self._git(repo, "show", original + ":x.txt"), "replacement"
            )
            source = inventory.GitSource(repo, original)
            self.assertEqual(source.revision, original)
            self.assertEqual(source.tree["x.txt"]["git_blob"], original_blob)
            self.assertEqual(source.read("x.txt"), b"original\n")
            self.assertEqual(source.provenance("x.txt")["git_blob"], original_blob)

    def test_git_env_sanitizes_repository_selection(self):
        with patch.dict(
            os.environ,
            {
                "GIT_DIR": "/elsewhere/.git",
                "GIT_OBJECT_DIRECTORY": "/elsewhere/objects",
                "GIT_CONFIG_KEY_0": "core.bare",
                "PATH": os.environ.get("PATH", ""),
            },
        ):
            env = inventory._git_env()
        self.assertEqual(env["GIT_NO_REPLACE_OBJECTS"], "1")
        self.assertEqual(env["GIT_OPTIONAL_LOCKS"], "0")
        self.assertNotIn("GIT_DIR", env)
        self.assertNotIn("GIT_OBJECT_DIRECTORY", env)
        self.assertNotIn("GIT_CONFIG_KEY_0", env)


class Command(unittest.TestCase):
    def test_populated_main_and_no_overwrite(self):
        source = fixture_source()
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "run"
            args = ["inventory_v1.py", "--base", "fixture", "--output", str(output)]
            with patch("sys.argv", args), patch.object(
                inventory, "GitSource", return_value=source
            ):
                self.assertEqual(inventory.main(), 0)
                manifest = json.loads((output / "manifest.json").read_bytes())
                data = (output / "inventory.jsonl").read_bytes()
                self.assertEqual(manifest["target_count"], 1)
                self.assertEqual(manifest["inventory_sha256"], inventory.sha256(data))
                with self.assertRaisesRegex(ValueError, "already exists"):
                    inventory.main()

    def test_overflow_reports_create_no_partial_output(self):
        for section in ("header", "row"):
            for literal in ("1e9999", "-1e9999"):
                with self.subTest(section=section, literal=literal):
                    source = fixture_source(
                        files={
                            "v1/Atlas/FixtureBook/report.json": overflow_report(
                                section, literal
                            )
                        }
                    )
                    with tempfile.TemporaryDirectory() as directory:
                        output = Path(directory) / "run"
                        args = [
                            "inventory_v1.py",
                            "--base",
                            "fixture",
                            "--output",
                            str(output),
                        ]
                        with patch("sys.argv", args), patch.object(
                            inventory, "GitSource", return_value=source
                        ):
                            with self.assertRaises(ValueError):
                                inventory.main()
                        self.assertFalse(output.exists())

    def test_manifest_serialization_failure_creates_no_output(self):
        source = fixture_source()
        source.commands = [float("inf")]
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "run"
            args = ["inventory_v1.py", "--base", "fixture", "--output", str(output)]
            with patch("sys.argv", args), patch.object(
                inventory, "GitSource", return_value=source
            ):
                with self.assertRaises(ValueError):
                    inventory.main()
            self.assertFalse(output.exists())

    def test_manifest_write_failure_cleans_staging_and_allows_retry(self):
        source = fixture_source()
        original_open = Path.open
        writes = []

        def failing_open(path, mode="r", *args, **kwargs):
            if mode == "wb":
                writes.append(path.name)
                if path.name == "manifest.json":
                    raise OSError(errno.ENOSPC, "simulated full disk")
            return original_open(path, mode, *args, **kwargs)

        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "run"
            args = ["inventory_v1.py", "--base", "fixture", "--output", str(output)]
            with patch("sys.argv", args), patch.object(
                inventory, "GitSource", return_value=source
            ):
                with patch.object(Path, "open", failing_open):
                    with self.assertRaises(OSError):
                        inventory.main()
                self.assertEqual(writes, ["inventory.jsonl", "manifest.json"])
                self.assertEqual(list(Path(directory).iterdir()), [])
                self.assertEqual(inventory.main(), 0)
                self.assertTrue((output / "manifest.json").is_file())

    def test_fsync_failures_create_no_output_or_staging(self):
        original_fsync = inventory.os.fsync
        for fail_at in (1, 3):
            calls = []

            def failing_fsync(descriptor):
                calls.append(descriptor)
                if len(calls) == fail_at:
                    raise OSError(errno.EIO, "simulated fsync failure")
                return original_fsync(descriptor)

            with self.subTest(
                fail_at=fail_at
            ), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "run"
                args = ["inventory_v1.py", "--base", "fixture", "--output", str(output)]
                with patch("sys.argv", args), patch.object(
                    inventory, "GitSource", return_value=fixture_source()
                ):
                    with patch.object(inventory.os, "fsync", failing_fsync):
                        with self.assertRaises(OSError):
                            inventory.main()
                self.assertEqual(len(calls), fail_at)
                self.assertEqual(list(Path(directory).iterdir()), [])

    def test_publish_failure_cleans_staging(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "run"
            args = ["inventory_v1.py", "--base", "fixture", "--output", str(output)]
            with patch("sys.argv", args), patch.object(
                inventory, "GitSource", return_value=fixture_source()
            ):
                with patch.object(
                    inventory,
                    "rename_no_replace",
                    side_effect=PermissionError("simulated rename failure"),
                ):
                    with self.assertRaises(PermissionError):
                        inventory.main()
            self.assertEqual(list(Path(directory).iterdir()), [])

    def test_competing_empty_output_is_not_overwritten(self):
        original_rename = inventory.rename_no_replace

        def racing_rename(temporary, output):
            self.assertTrue((temporary / "inventory.jsonl").is_file())
            self.assertTrue((temporary / "manifest.json").is_file())
            output.mkdir()
            original_rename(temporary, output)

        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "run"
            args = ["inventory_v1.py", "--base", "fixture", "--output", str(output)]
            with patch("sys.argv", args), patch.object(
                inventory, "GitSource", return_value=fixture_source()
            ):
                with patch.object(inventory, "rename_no_replace", racing_rename):
                    with self.assertRaises(FileExistsError):
                        inventory.main()
            self.assertEqual(list(Path(directory).iterdir()), [output])
            self.assertEqual(list(output.iterdir()), [])

    def test_empty_inventory_does_not_create_outputs(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "run"
            args = ["inventory_v1.py", "--base", "fixture", "--output", str(output)]
            with patch("sys.argv", args), patch.object(
                inventory, "GitSource", return_value=FakeSource({})
            ):
                with self.assertRaisesRegex(ValueError, "No v1"):
                    inventory.main()
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
