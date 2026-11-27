#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Inventory schema and graph tests; native Lean execution is explicitly mocked."""

from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
import unittest
from collections import Counter
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

import generate_import_inventory as inventory
import optimize_imports as optimizer


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def header_fixture(path: Path, imports: tuple[tuple[str, tuple[str, ...]], ...],
                   *, is_module: bool = True, data: bytes | None = None) -> dict:
    """Explicit native AST protocol fixture, not an import parser."""
    source = path.read_bytes() if data is None else data

    def token(text: str, start: int, kind: str = "atom") -> dict:
        end = start + len(text.encode())
        return {"kind": kind, "text": text, "parsed_text": text,
                "span": {"start_byte": start, "end_byte": end},
                "leading_span": {"start_byte": start, "end_byte": start},
                "trailing_span": {"start_byte": end, "end_byte": end}}

    module_start = source.index(b"module") if is_module else 0
    module = token("module", module_start) if is_module else None
    module_syntax = {"span": module["span"], "tokens": [module]} if module else None
    records = []
    for name, modifiers in imports:
        words = [word for word in modifiers if word != "all"] + ["import"]
        if "all" in modifiers:
            words.append("all")
        directive = " ".join([*words, name])
        start = source.index(directive.encode())
        tokens = []
        position = start
        for word in [*words, name]:
            tokens.append(token(word, position, "ident" if word == name else "atom"))
            position += len(word.encode()) + 1
        records.append({"module": name, "modifiers": list(modifiers),
                        "is_exported": "public" in modifiers, "is_meta": "meta" in modifiers,
                        "import_all": "all" in modifiers,
                        "source": {"span": {"start_byte": start, "end_byte": position - 1},
                                   "tokens": tokens}})
    end = records[-1]["source"]["span"]["end_byte"] if records else module_start + 6
    boundary = source.index(b"public def ") if b"public def " in source else source.index(b"def ")
    all_tokens = ([module] if module else []) + [item for record in records for item in record["source"]["tokens"]]
    for index, item in enumerate(all_tokens):
        start = item["span"]["start_byte"]
        stop = item["span"]["end_byte"]
        item["leading_span"] = {"start_byte": start if index else 0, "end_byte": start}
        item["trailing_span"] = {"start_byte": stop,
                                 "end_byte": all_tokens[index + 1]["span"]["start_byte"]
                                 if index + 1 < len(all_tokens) else boundary}
    for syntax in ([module_syntax] if module_syntax else []) + [record["source"] for record in records]:
        syntax["leading_span"] = syntax["tokens"][0]["leading_span"]
        syntax["trailing_span"] = syntax["tokens"][-1]["trailing_span"]
    header_span = ({"start_byte": all_tokens[0]["span"]["start_byte"], "end_byte": end}
                   if all_tokens else None)
    if not all_tokens:
        end = boundary
    newline = source.find(b"\n", end)
    shake_insertion = len(source) if newline < 0 else newline + 1
    return {"path": str(path), "relative_path": path.as_posix(),
            "source_sha256": digest(source), "source_utf8_bytes": len(source),
            "status": "parsed", "parse_errors": [], "is_module": is_module, "is_prelude": False,
            "module_token": module_syntax, "prelude_token": None, "imports": records,
            "header_span": header_span, "header_end_byte": end,
            "insertion_byte": shake_insertion if all_tokens else boundary,
            "shake_insertion_byte": shake_insertion,
            "body_boundary_byte": boundary}


class HeaderPositionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.path = Path(self.temporary.name).resolve() / "Example.lean"
        self.source = b"module\nimport Mathlib\ndef original : Nat := 0\n/-\nimport Mathlib\n-/\n"
        self.path.write_bytes(self.source)
        self.header = header_fixture(self.path, (("Mathlib", ()),))

    def test_import_relocated_into_body_comment_is_rejected(self) -> None:
        forged = deepcopy(self.header)
        delta = self.source.rindex(b"import Mathlib") - self.source.index(b"import Mathlib")

        def relocate(value: object) -> None:
            if isinstance(value, dict):
                if set(value) == {"start_byte", "end_byte"}:
                    value["start_byte"] += delta
                    value["end_byte"] += delta
                else:
                    for child in value.values():
                        relocate(child)
            elif isinstance(value, list):
                for child in value:
                    relocate(child)

        relocate(forged["imports"][0]["source"])
        end = forged["imports"][0]["source"]["span"]["end_byte"]
        forged.update(header_end_byte=end, insertion_byte=end + 1,
                      shake_insertion_byte=end + 1, body_boundary_byte=end + 1)
        forged["header_span"]["end_byte"] = end
        with self.assertRaisesRegex(ValueError, "header|token"):
            inventory.verify_header(forged, self.source, Counter())

    def test_boundary_fields_are_bound_to_the_real_header(self) -> None:
        cases = [(key, 0) for key in ("header_end_byte", "insertion_byte", "shake_insertion_byte")]
        cases += [("body_boundary_byte", self.header["body_boundary_byte"] + 3),
                  ("header_span", None), ("header_span", {"start_byte": 1, "end_byte": 21})]
        for key, value in cases:
            with self.subTest(key=key, value=value), self.assertRaisesRegex(ValueError, "header"):
                inventory.verify_header(dict(self.header, **{key: value}), self.source, Counter())

    def test_initial_module_and_import_cannot_be_omitted(self) -> None:
        omitted_import = dict(self.header, imports=[], header_end_byte=6, insertion_byte=7,
                              shake_insertion_byte=7, body_boundary_byte=7,
                              header_span={"start_byte": 0, "end_byte": 6})
        omitted_module = dict(self.header, is_module=False, module_token=None)
        for forged in (omitted_import, omitted_module):
            with self.subTest(module=forged["is_module"], imports=len(forged["imports"])), \
                    self.assertRaisesRegex(ValueError, "header"):
                inventory.verify_header(forged, self.source, Counter())

    def test_token_trivia_cannot_cover_body_text(self) -> None:
        for key in ("leading_span", "trailing_span"):
            forged = deepcopy(self.header)
            forged["imports"][0]["source"]["tokens"][-1][key] = {
                "start_byte": 0, "end_byte": len(self.source)}
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "header|trivia"):
                inventory.verify_header(forged, self.source, Counter())

    def test_cached_tokens_cannot_slice_identifier_prefixes(self) -> None:
        cases = [(b"moduleFoo\ndef original := 0\n", (), True),
                 (b"module\nimport Mathlib.Data\ndef original := 0\n", (("Mathlib", ()),), True),
                 ("module\nimport Mathlib.Δ₀\ndef original := 0\n".encode(), (("Mathlib", ()),), True)]
        for source, imports, is_module in cases:
            forged = header_fixture(self.path, imports, is_module=is_module, data=source)
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, "header|token"):
                inventory.verify_header(forged, source, Counter())

    def test_prelude_cannot_be_omitted_from_the_header(self) -> None:
        source = b"prelude\nimport Init\ndef original := 0\n"
        forged = header_fixture(self.path, (("Init", ()),), is_module=False, data=source)
        with self.assertRaisesRegex(ValueError, "header"):
            inventory.verify_header(forged, source, Counter())

    def test_native_trivia_unicode_multiline_modes_and_modifiers(self) -> None:
        source = ("-- license α\r\n/- import Decoy /- nested -/ -/\r\n"
                  "module\r\nprelude\r\npublic /- comment /- nested -/ -/ meta\r\n"
                  "import\r\n«A B».𝕄\r\nmeta import all Δ₀\r\n"
                  "/- trailing comment -/\r\n/-! import Body\r\n-/\r\npublic def original := 0\r\n").encode()
        body = source.index(b"/-!")
        words = [("module", source.index(b"module\r\n")),
                 ("prelude", source.index(b"prelude\r\n")),
                 ("public", source.index(b"public /-")),
                 ("meta", source.index(b"meta\r\n")),
                 ("import", source.index(b"import\r\n")),
                 ("«A B».𝕄", source.index("«A B».𝕄".encode())),
                 ("meta", source.index(b"meta import")),
                 ("import", source.index(b"meta import") + 5),
                 ("all", source.index(b"meta import") + 12),
                 ("Δ₀", source.index("Δ₀".encode()))]
        tokens = []
        for index, (word, start) in enumerate(words):
            end = start + len(word.encode())
            tokens.append({"kind": "ident" if index in (5, 9) else "atom", "text": word,
                           "parsed_text": word, "span": {"start_byte": start, "end_byte": end},
                           "leading_span": {"start_byte": start if index else 0, "end_byte": start},
                           "trailing_span": {"start_byte": end,
                                             "end_byte": words[index + 1][1] if index + 1 < len(words) else body}})

        def syntax(items: list[dict]) -> dict:
            return {"span": {"start_byte": items[0]["span"]["start_byte"],
                             "end_byte": items[-1]["span"]["end_byte"]},
                    "leading_span": items[0]["leading_span"], "trailing_span": items[-1]["trailing_span"],
                    "tokens": items}

        end = tokens[-1]["span"]["end_byte"]
        insertion = end + 2
        row = {"status": "parsed", "source_utf8_bytes": len(source), "source_sha256": digest(source),
               "parse_errors": [], "is_module": True, "is_prelude": True,
               "module_token": syntax(tokens[:1]), "prelude_token": syntax(tokens[1:2]),
               "imports": [{"module": "«A B».𝕄", "modifiers": ["public", "meta"],
                            "is_exported": True, "is_meta": True, "import_all": False,
                            "source": syntax(tokens[2:6])},
                           {"module": "Δ₀", "modifiers": ["meta", "all"],
                            "is_exported": False, "is_meta": True, "import_all": True,
                            "source": syntax(tokens[6:])}],
               "header_span": {"start_byte": words[0][1], "end_byte": end}, "header_end_byte": end,
               "body_boundary_byte": body, "insertion_byte": insertion, "shake_insertion_byte": insertion}
        counts = Counter()
        inventory.verify_header(row, source, counts)
        self.assertEqual((counts["tokens"], counts["imports"]), (10, 2))
        header = optimizer.decode_header(row, source)
        changed = optimizer.rewrite_imports(source, header, (header.specs()[1],), ())
        self.assertEqual(changed[changed.index(b"/-!"):], source[body:])
        self.assertIn(b"public /- comment /- nested -/ -/ meta", changed)
        with self.assertRaisesRegex(ValueError, "comment"):
            optimizer.rewrite_imports(source, header, (header.specs()[0],), ())

    def test_empty_header_stops_at_doc_comments_and_body(self) -> None:
        cases = [(b"", 0), (b"/-/-/\r\ndef original := 0\n", 7),
                 (b"/-- import Decoy -/\ndef original := 0\n", 0),
                 ("-- α\r\n/- ordinary /-- nested -/ -/\r\n/-! import Decoy -/\n".encode(), None)]
        for source, boundary in cases:
            if boundary is None:
                boundary = source.index(b"/-!")
            newline = source.find(b"\n", boundary)
            row = {"status": "parsed", "source_utf8_bytes": len(source), "parse_errors": [],
                   "is_module": False, "is_prelude": False, "module_token": None,
                   "prelude_token": None, "imports": [], "header_span": None,
                   "header_end_byte": boundary, "body_boundary_byte": boundary,
                   "insertion_byte": boundary, "shake_insertion_byte": newline + 1 if newline >= 0 else len(source)}
            counts = Counter()
            with self.subTest(source=source):
                inventory.verify_header(row, source, counts)
                self.assertEqual((counts["tokens"], counts["imports"]), (0, 0))

    def test_non_lean_whitespace_cannot_hide_the_initial_header(self) -> None:
        for prefix in (b"\t", b"\r", "\u00a0".encode(), "\ufeff".encode()):
            source = prefix + b"module\ndef original := 0\n"
            row = header_fixture(self.path, (), data=source)
            with self.subTest(prefix=prefix), self.assertRaisesRegex(ValueError, "header"):
                inventory.verify_header(row, source, Counter())


class InventoryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name).resolve()
        self.root = self.directory / "repository"
        self.root.mkdir()
        self.sources = {
            "Reserved/A.lean": (b"module\nimport Init\ndef a : Nat := 0\n", (("Init", ()),)),
            "Middle.lean": (b"module\npublic import Reserved.A\ndef b : Nat := 0\n",
                            (("Reserved.A", ("public",)),)),
            "Top.lean": (b"module\nmeta import Middle\ndef c : Nat := 0\n",
                         (("Middle", ("meta",)),)),
            "Checkpoint.lean": (b"module\ndef d : Nat := 0\n", ()),
            "Generated.lean": (b"-- Author: @toskua\n"
                               b"-- DO NOT EDIT MANUALLY. This file is autogenerated\n"
                               b"module\npublic import Top\ndef generated : Nat := 0\n",
                               (("Top", ("public",)),)),
            "scripts/Helper.lean": (b"module\ndef helper : Nat := 0\n", ()),
        }
        rows = []
        for relative, (source, imports) in self.sources.items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(source)
            row = header_fixture(path, imports)
            row["relative_path"] = relative
            rows.append(row)
        for name, data in {"lean-toolchain": b"leanprover/lean4:v4.34.1\n",
                           "lakefile.toml": b'name = "inventory_fixture"\n',
                           "lake-manifest.json": b"{}\n"}.items():
            (self.root / name).write_bytes(data)
        for arguments in (["init", "-q"], ["add", "."],
                          ["-c", "user.name=Inventory Test", "-c", "user.email=inventory@example.invalid",
                           "commit", "-qm", "Inventory fixture"]):
            subprocess.run(["git", *arguments], cwd=self.root, check=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (self.root / "Untracked.lean").write_text("module\ndef decoy : Nat := 0\n")
        self.cache = self.directory / "headers.jsonl"
        self.cache.write_text("".join(json.dumps(row) + "\n" for row in rows))
        self.output = self.directory / "inventory.jsonl"

    def generate(self, **options: object) -> tuple[list[dict], dict]:
        receipt = inventory.create_inventory(
            root=self.root, output=self.output, headers=self.cache,
            headers_sha256=digest(self.cache.read_bytes()), **options)
        rows = [json.loads(line) for line in self.output.read_text().splitlines()]
        return rows, receipt

    def test_tracked_source_hashes_native_graph_and_determinism(self) -> None:
        rows, receipt = self.generate()
        by_path = {row["path"]: row for row in rows}
        self.assertEqual(set(by_path), set(self.sources))
        self.assertEqual(receipt["source_count"], 6)
        self.assertEqual(by_path["Top.lean"]["direct_local_dependencies"], ["Middle"])
        self.assertEqual(by_path["Top.lean"]["old_dependency_cost"]["local_source_dependency_count"], 2)
        self.assertLess(by_path["Reserved/A.lean"]["topological_index"],
                        by_path["Middle.lean"]["topological_index"])
        self.assertLess(by_path["Middle.lean"]["topological_index"], by_path["Top.lean"]["topological_index"])
        for path, row in by_path.items():
            self.assertEqual(row["source_sha256"], digest(self.sources[path][0]))
            self.assertEqual(row["baseline_compile"], {"status": "not_run"})
            inventory.validate_manifest_row(row)
        first = self.output.read_bytes()
        self.generate()
        self.assertEqual(self.output.read_bytes(), first)
        for output in (self.root / "Top.lean", self.cache):
            with self.subTest(output=output), self.assertRaises(ValueError):
                inventory.create_inventory(root=self.root, output=output, headers=self.cache,
                                           headers_sha256=digest(self.cache.read_bytes()))
        self.assertEqual((self.root / "Top.lean").read_bytes(), self.sources["Top.lean"][0])

    def test_separate_packages_and_documentation_are_outside_the_inventory(self) -> None:
        excluded = ("Atlas/Archived.lean", "v1/Archived.lean", "docs/Example.lean")
        for name in excluded:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("not a Lean header on this toolchain\n")
        subprocess.run(["git", "add", "--", *excluded], cwd=self.root, check=True)
        rows, receipt = self.generate()
        self.assertEqual({row["path"] for row in rows}, set(self.sources))
        self.assertEqual(receipt["source_count"], len(self.sources))
        self.assertEqual(optimizer.load_inventory(self.root, self.output, []), rows)
        for name in excluded:
            with self.subTest(path=name), self.assertRaisesRegex(ValueError, "absent"):
                optimizer.load_inventory(self.root, self.output, [name])

    def test_atlas_lock_is_optional_and_pinned_in_inventory_receipts(self) -> None:
        _, before = self.generate()
        self.assertEqual(set(before["project_pins"]),
                         {"lean-toolchain", "lakefile.toml", "lake-manifest.json"})
        lock = self.root / "atlas.lock.json"
        lock.write_text(json.dumps({"revision": "a" * 40}) + "\n")
        _, first = self.generate()
        self.assertEqual(first["project_pins"],
                         {**before["project_pins"], "atlas.lock.json": digest(lock.read_bytes())})
        lock.write_text(json.dumps({"revision": "b" * 40}) + "\n")
        _, second = self.generate()
        self.assertNotEqual(first["project_pins"]["atlas.lock.json"],
                            second["project_pins"]["atlas.lock.json"])
        self.assertEqual(second["project_pins"]["atlas.lock.json"], digest(lock.read_bytes()))
        self.assertEqual(json.loads(Path(str(self.output) + ".meta.json").read_text()), second)

    def test_atlas_lock_change_during_inventory_is_rejected(self) -> None:
        lock = self.root / "atlas.lock.json"
        lock.write_text(json.dumps({"revision": "a" * 40}) + "\n")
        cached_headers = optimizer.cached_headers

        def changed_lock(*args: object) -> dict:
            headers = cached_headers(*args)
            lock.write_text(json.dumps({"revision": "b" * 40}) + "\n")
            return headers

        with patch.object(optimizer, "cached_headers", side_effect=changed_lock), \
                self.assertRaisesRegex(ValueError, "project pins.*changed during inventory"):
            self.generate()
        self.assertFalse(self.output.exists())

    def test_reserve_blocks_all_transitive_consumers_and_preserves_sources(self) -> None:
        rows, receipt = self.generate(reserve=("Reserved/",), checkpoints=("Checkpoint.lean",))
        self.assertEqual({row["path"]: row["analysis_status"] for row in rows}, {
            "Reserved/A.lean": "reserved_readonly", "Middle.lean": "reserved_consumer_readonly",
            "Top.lean": "reserved_consumer_readonly", "Generated.lean": "reserved_consumer_readonly",
            "scripts/Helper.lean": "helper_readonly", "Checkpoint.lean": "parent_owned_checkpoint",
        })
        self.assertEqual(receipt["reserved_count"], 1)
        self.assertEqual(receipt["reserved_consumer_count"], 3)
        for relative, (source, _) in self.sources.items():
            self.assertEqual((self.root / relative).read_bytes(), source)

    def test_modern_consumers_of_legacy_sources_keep_the_modern_engine(self) -> None:
        legacy_path = "Reserved/A.lean"
        self.sources[legacy_path] = (b"import Init\ndef a : Nat := 0\n", (("Init", ()),))
        (self.root / legacy_path).write_bytes(self.sources[legacy_path][0])
        headers = []
        for relative, (_, imports) in self.sources.items():
            row = header_fixture(self.root / relative, imports, is_module=relative != legacy_path)
            row["relative_path"] = relative
            headers.append(row)
        self.cache.write_text("".join(json.dumps(row) + "\n" for row in headers))
        rows, receipt = self.generate()
        for row in rows:
            expected = ("official ImportGraph legacy fallback" if row["path"] == legacy_path
                        else "official Lake shake")
            self.assertEqual(row["engine"], expected, row["path"])
            self.assertEqual(row["uses_module_system"], row["path"] != legacy_path)
        self.assertEqual(receipt["engine_counts"], {
            "official ImportGraph legacy fallback": 1, "official Lake shake": 5,
        })

    def test_generated_helper_and_checkpoint_roots_are_readonly(self) -> None:
        rows, _ = self.generate(checkpoints=("Checkpoint.lean",))
        status = {row["path"]: row["analysis_status"] for row in rows}
        self.assertEqual(status["Generated.lean"], "generated_readonly")
        self.assertEqual(status["scripts/Helper.lean"], "helper_readonly")
        self.assertEqual(status["Checkpoint.lean"], "parent_owned_checkpoint")
        self.assertTrue({status[path] for path in ("Generated.lean", "scripts/Helper.lean", "Checkpoint.lean")}
                        <= inventory.READONLY_STATUSES)

    def test_optimizer_recognizes_attribution_from_current_source(self) -> None:
        rows, _ = self.generate()
        for row in rows:
            if row["path"] == "Generated.lean":
                row["analysis_status"] = "pending"
        self.output.write_text("".join(json.dumps(row) + "\n" for row in rows))
        loaded = optimizer.load_inventory(self.root, self.output, [])
        generated = next(row for row in loaded if row["path"] == "Generated.lean")
        self.assertEqual(generated["analysis_status"], "generated_readonly")
        self.assertEqual((self.root / "Generated.lean").read_bytes(), self.sources["Generated.lean"][0])

    def test_same_length_source_edit_rejects_cached_header_before_output(self) -> None:
        source = self.root / "Top.lean"
        source.write_bytes(source.read_bytes().replace(b":= 0", b":= 1"))
        with self.assertRaisesRegex(ValueError, "[Hh]ash|identity"):
            self.generate()
        self.assertFalse(self.output.exists())

    def test_cached_module_identity_cannot_hide_reserved_consumers(self) -> None:
        original = [json.loads(line) for line in self.cache.read_text().splitlines()]
        for quoted in (False, True):
            with self.subTest(quoted=quoted):
                rows = json.loads(json.dumps(original))
                middle = next(row for row in rows if row["relative_path"] == "Middle.lean")
                if quoted:
                    source = self.root / "Middle.lean"
                    source.write_bytes(self.sources["Middle.lean"][0].replace(
                        b"Reserved.A", "«Reserved».A".encode()))
                    middle.update(header_fixture(source, (("«Reserved».A", ("public",)),)))
                    middle["relative_path"] = "Middle.lean"
                    middle["imports"][0]["module"] = "Reserved.A"
                else:
                    middle["imports"][0]["module"] = "Shadow.Reserved"
                self.cache.write_text("".join(json.dumps(row) + "\n" for row in rows))
                with self.assertRaisesRegex(ValueError, "module|identifier"):
                    self.generate(reserve=("Reserved/",))
                self.assertFalse(self.output.exists())

    def test_native_token_mutation_and_missing_row_reject_cache(self) -> None:
        original = [json.loads(line) for line in self.cache.read_text().splitlines()]
        mutated = json.loads(json.dumps(original))
        mutated[0]["imports"][0]["source"]["tokens"][-1]["parsed_text"] = "Bad!"
        for rows in (mutated, original[:-1]):
            with self.subTest(rows=len(rows)):
                self.cache.write_text("".join(json.dumps(row) + "\n" for row in rows))
                with self.assertRaises(ValueError):
                    self.generate()
                self.assertFalse(self.output.exists())

    def test_relocated_import_span_in_body_comment_rejects_cache(self) -> None:
        original = [json.loads(line) for line in self.cache.read_text().splitlines()]
        rows = json.loads(json.dumps(original))
        top = next(row for row in rows if row["relative_path"] == "Top.lean")
        source_path = self.root / "Top.lean"
        source = source_path.read_bytes() + b"-- meta import Middle\n"
        source_path.write_bytes(source)
        top["source_sha256"] = digest(source)
        top["source_utf8_bytes"] = len(source)
        record = top["imports"][0]
        span = record["source"]["span"]
        width = span["end_byte"] - span["start_byte"]
        relocated = source.rindex(b"meta import Middle")
        delta = relocated - span["start_byte"]
        span["start_byte"] = relocated
        span["end_byte"] = relocated + width
        for token in record["source"]["tokens"]:
            token["span"]["start_byte"] += delta
            token["span"]["end_byte"] += delta
            token["leading_span"] = {"start_byte": token["span"]["start_byte"],
                                     "end_byte": token["span"]["start_byte"]}
            token["trailing_span"] = {"start_byte": token["span"]["end_byte"],
                                      "end_byte": token["span"]["end_byte"]}
        top["header_span"] = {"start_byte": 0, "end_byte": span["end_byte"]}
        top["header_end_byte"] = span["end_byte"]
        top["insertion_byte"] = span["end_byte"] + 1
        top["shake_insertion_byte"] = span["end_byte"] + 1
        top["body_boundary_byte"] = len(source)
        self.cache.write_text("".join(json.dumps(row) + "\n" for row in rows))
        with self.assertRaisesRegex(ValueError, "header"):
            self.generate()
        self.assertFalse(self.output.exists())

    def test_immediately_nested_comment_decoy_rejects_cache(self) -> None:
        original = [json.loads(line) for line in self.cache.read_text().splitlines()]
        rows = json.loads(json.dumps(original))
        top = next(row for row in rows if row["relative_path"] == "Top.lean")
        source_path = self.root / "Top.lean"
        source = (b"/-/- meta import Middle -/ still comment -/\n" +
                  source_path.read_bytes())
        source_path.write_bytes(source)
        top["source_sha256"] = digest(source)
        top["source_utf8_bytes"] = len(source)
        shift = source.index(b"module\n")
        module_span = top["module_token"]["span"]
        module_span["start_byte"] = shift
        module_span["end_byte"] = shift + 6
        top["module_token"]["tokens"][0]["span"] = dict(module_span)
        record = top["imports"][0]
        span = record["source"]["span"]
        width = span["end_byte"] - span["start_byte"]
        relocated = source.index(b"meta import Middle")
        delta = relocated - span["start_byte"]
        span["start_byte"] = relocated
        span["end_byte"] = relocated + width
        for token in record["source"]["tokens"]:
            token["span"]["start_byte"] += delta
            token["span"]["end_byte"] += delta
            token["leading_span"] = {"start_byte": token["span"]["start_byte"],
                                     "end_byte": token["span"]["start_byte"]}
            token["trailing_span"] = {"start_byte": token["span"]["end_byte"],
                                      "end_byte": token["span"]["end_byte"]}
        top["header_span"] = {"start_byte": 0, "end_byte": span["end_byte"]}
        top["header_end_byte"] = span["end_byte"]
        top["insertion_byte"] = span["end_byte"] + 1
        top["shake_insertion_byte"] = span["end_byte"] + 1
        top["body_boundary_byte"] = len(source)
        self.cache.write_text("".join(json.dumps(row) + "\n" for row in rows))
        with self.assertRaisesRegex(ValueError, "header"):
            self.generate()
        self.assertFalse(self.output.exists())

    def test_omitted_import_before_body_boundary_rejects_cache(self) -> None:
        original = [json.loads(line) for line in self.cache.read_text().splitlines()]
        rows = json.loads(json.dumps(original))
        middle = next(row for row in rows if row["relative_path"] == "Middle.lean")
        middle["imports"] = []
        middle["header_span"] = {"start_byte": 0, "end_byte": 6}
        middle["header_end_byte"] = 6
        middle["insertion_byte"] = 7
        middle["shake_insertion_byte"] = 7
        self.cache.write_text("".join(json.dumps(row) + "\n" for row in rows))
        with self.assertRaisesRegex(ValueError, "header"):
            self.generate()
        self.assertFalse(self.output.exists())

    def test_empty_header_row_is_accepted(self) -> None:
        source = b"-- leading comment\ndef e : Nat := 0\n"
        path = self.root / "Empty.lean"
        path.write_bytes(source)
        subprocess.run(["git", "add", "Empty.lean"], cwd=self.root, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        subprocess.run(["git", "-c", "user.name=Inventory Test",
                        "-c", "user.email=inventory@example.invalid",
                        "commit", "-qm", "empty header"], cwd=self.root, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        boundary = source.index(b"def ")
        row = {"path": "Empty.lean", "relative_path": "Empty.lean",
               "source_sha256": digest(source), "source_utf8_bytes": len(source),
               "status": "parsed", "parse_errors": [], "is_module": False,
               "is_prelude": False, "module_token": None, "prelude_token": None,
               "imports": [], "header_span": None, "header_end_byte": boundary,
               "insertion_byte": boundary, "shake_insertion_byte": len(source),
               "body_boundary_byte": boundary}
        rows = [json.loads(line) for line in self.cache.read_text().splitlines()]
        rows.append(row)
        self.cache.write_text("".join(json.dumps(item) + "\n" for item in rows))
        generated, _receipt = self.generate()
        self.assertIn("Empty.lean", {item["path"] for item in generated})

    def test_unknown_status_missing_fields_and_wrong_module_reject_schema(self) -> None:
        valid = {"path": "Top.lean", "module": "Top", "source_sha256": digest(self.sources["Top.lean"][0]),
                 "analysis_status": "pending"}
        inventory.validate_manifest_row(valid)
        invalid = [dict(valid, analysis_status="resereved_readonly"), dict(valid, module="Other"),
                   dict(valid, source_sha256="0"), dict(valid, topological_index=True)]
        invalid.extend({key: value for key, value in valid.items() if key != missing} for missing in valid)
        for row in invalid:
            with self.subTest(row=row), self.assertRaises(ValueError):
                inventory.validate_manifest_row(row)

    def test_runner_rejects_unknown_manifest_status_before_selection(self) -> None:
        rows = [{"path": "Top.lean", "module": "Top", "source_sha256": digest(self.sources["Top.lean"][0]),
                 "analysis_status": "resereved_readonly"}]
        manifest = self.directory / "unknown.jsonl"
        manifest.write_text(json.dumps(rows[0]) + "\n")
        with self.assertRaises(ValueError):
            optimizer.load_inventory(self.root, manifest, [])

    def test_runner_rejects_incomplete_inventory_before_selection(self) -> None:
        rows, _ = self.generate(reserve=("Reserved/",), checkpoints=("Checkpoint.lean",))
        for missing in self.sources:
            truncated = [row for row in rows if row["path"] != missing]
            self.output.write_text("".join(json.dumps(row) + "\n" for row in truncated))
            for requested in ([], ["Top.lean"]):
                with self.subTest(missing=missing, requested=requested), \
                        self.assertRaisesRegex(ValueError, "Git-tracked"):
                    optimizer.load_inventory(self.root, self.output, requested)

    def test_runner_rejects_untracked_inventory_rows_before_selection(self) -> None:
        rows, _ = self.generate()
        extra = {"path": "Untracked.lean", "module": "Untracked",
                 "source_sha256": digest((self.root / "Untracked.lean").read_bytes()),
                 "analysis_status": "pending"}
        for missing in (None, "Middle.lean"):
            extended = [row for row in rows if row["path"] != missing] + [extra]
            self.output.write_text("".join(json.dumps(row) + "\n" for row in extended))
            for requested in ([], ["Top.lean"]):
                with self.subTest(missing=missing, requested=requested), \
                        self.assertRaisesRegex(ValueError, "Git-tracked"):
                    optimizer.load_inventory(self.root, self.output, requested)

    def test_runner_validates_unselected_dependency_source(self) -> None:
        self.generate()
        selected = optimizer.load_inventory(self.root, self.output, ["Top.lean"])
        self.assertEqual([row["path"] for row in selected], ["Top.lean"])
        self.assertEqual(selected[0]["direct_local_dependencies"], ["Middle"])
        dependency = self.root / "Middle.lean"
        dependency.write_bytes(self.sources["Middle.lean"][0] + b"-- concurrent edit\n")
        with self.assertRaisesRegex(ValueError, "Inventory source hash changed"):
            optimizer.load_inventory(self.root, self.output, ["Top.lean"])

    def test_fresh_mode_uses_official_helper_and_detects_concurrent_source_change(self) -> None:
        rows = [json.loads(line) for line in self.cache.read_text().splitlines()]
        native = {row["relative_path"]: row for row in rows}
        lean = self.directory / "lean"
        lean.write_text("Compiler identity fixture, never executed\n")
        def parsed_headers(tools: optimizer.Tools, tracked: list[dict]) -> dict:
            (tools.output / "native-headers.jsonl").write_bytes(self.cache.read_bytes())
            return native

        with patch.object(optimizer, "native_headers", side_effect=parsed_headers) as native_helper:
            receipt = inventory.create_inventory(root=self.root, output=self.output, lean=lean)
        self.assertEqual(native_helper.call_count, 1)
        tools, tracked = native_helper.call_args.args
        self.assertEqual(tools.lean, lean)
        self.assertEqual({row["path"] for row in tracked}, set(self.sources))
        self.assertEqual(receipt["header_mode"], "native")
        self.output.unlink()

        def source_changed(tools: optimizer.Tools, tracked: list[dict]) -> dict:
            path = self.root / "Top.lean"
            path.write_bytes(path.read_bytes().replace(b":= 0", b":= 1"))
            return native

        with patch.object(optimizer, "native_headers", side_effect=source_changed):
            with self.assertRaisesRegex(ValueError, "[Hh]ash|changed|identity"):
                inventory.create_inventory(root=self.root, output=self.output, lean=lean)
        self.assertFalse(self.output.exists())

    def test_unmatched_reservation_rejects_typo(self) -> None:
        with self.assertRaisesRegex(ValueError, "[Rr]eserv|prefix"):
            self.generate(reserve=("Typo/",))


if __name__ == "__main__":
    unittest.main()
