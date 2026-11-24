#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Bind parsed header identities to real source bytes without launching Lean."""

from __future__ import annotations

from contextlib import AbstractContextManager
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import optimize_imports as optimizer
from test_generate_import_inventory import header_fixture


class HeaderSourceTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.source = self.root / "A.lean"
        self.output = self.root / "output"
        self.output.mkdir()
        self.cache = self.root / "headers.jsonl"
        self.tools = optimizer.Tools(self.root, self.output, self.root / "lake", self.root / "lean",
                                     self.root / "helpers", {}, 5, time_binary=self.root / "time")

    def fixture(self, data: bytes, imports: tuple[tuple[str, tuple[str, ...]], ...], *,
                is_module: bool = True) -> tuple[dict[str, object], dict[str, object]]:
        self.source.write_bytes(data)
        header = header_fixture(self.source, imports, is_module=is_module)
        header["relative_path"] = "A.lean"
        row = {"path": "A.lean", "module": "A", "source_sha256": hashlib.sha256(data).hexdigest(),
               "analysis_status": "pending"}
        self.assertEqual(header["source_sha256"], row["source_sha256"])
        return row, header

    def save_cache(self, header: dict[str, object]) -> None:
        self.cache.write_text(json.dumps(header, ensure_ascii=False) + "\n")

    def external_header(self, header: dict[str, object]) -> AbstractContextManager[object]:
        def run(argv: list[str], label: Path,
                environment: dict[str, str] | None = None) -> dict[str, object]:
            label.parent.mkdir(parents=True, exist_ok=True)
            Path(str(label) + ".stdout").write_text(json.dumps(header, ensure_ascii=False) + "\n")
            Path(str(label) + ".stderr").write_text("")
            return {"argv": argv, "cwd": str(self.root), "exit_code": 0, "timed_out": False,
                    "remaining_group_killed": False, "elapsed_seconds": 0,
                    "stdout": str(label) + ".stdout", "stderr": str(label) + ".stderr"}

        return patch.object(optimizer.Tools, "run", side_effect=run)

    def test_cached_headers_reject_claimed_import_with_valid_source_digest(self) -> None:
        row, header = self.fixture(b"module\nimport Mathlib\ndef x : Nat := 0\n", (("Mathlib", ()),))
        header["imports"][0]["module"] = "Init"
        self.save_cache(header)
        self.assertEqual(header["source_sha256"], optimizer.sha256(self.source))
        with self.assertRaisesRegex(ValueError, "module identity"):
            optimizer.cached_headers(self.root, self.cache, [row])

    def test_cached_headers_reject_false_modifiers_even_when_flags_agree(self) -> None:
        row, original = self.fixture(b"module\npublic meta import all Mathlib\ndef x : Nat := 0\n",
                                     (("Mathlib", ("public", "meta", "all")),))
        for removed in ("public", "meta", "all"):
            with self.subTest(removed=removed):
                header = deepcopy(original)
                item = header["imports"][0]
                item["modifiers"].remove(removed)
                item[{"public": "is_exported", "meta": "is_meta", "all": "import_all"}[removed]] = False
                self.save_cache(header)
                with self.assertRaisesRegex(ValueError, "Native import differs"):
                    optimizer.cached_headers(self.root, self.cache, [row])

    def test_native_headers_reject_claimed_import_before_cache_publication(self) -> None:
        row, header = self.fixture(b"module\nimport Mathlib\ndef x : Nat := 0\n", (("Mathlib", ()),))
        header["imports"][0]["module"] = "Init"
        with self.external_header(header), self.assertRaisesRegex(ValueError, "module identity"):
            optimizer.native_headers(self.tools, [row])
        self.assertEqual((self.output / "native-headers.jsonl").read_bytes(), b"")

    def test_native_headers_reject_false_modifiers_before_cache_publication(self) -> None:
        row, header = self.fixture(b"module\nimport Mathlib\ndef x : Nat := 0\n", (("Mathlib", ()),))
        header["imports"][0].update(modifiers=["public"], is_exported=True)
        with self.external_header(header), self.assertRaisesRegex(ValueError, "Native import differs"):
            optimizer.native_headers(self.tools, [row])
        self.assertEqual((self.output / "native-headers.jsonl").read_bytes(), b"")

    def test_run_headers_rejects_lie_in_supplied_or_generated_resume_cache(self) -> None:
        row, header = self.fixture(b"module\nimport Mathlib\ndef x : Nat := 0\n", (("Mathlib", ()),))
        header["imports"][0]["module"] = "Init"
        for supplied in (True, False):
            with self.subTest(supplied=supplied):
                cache = self.cache if supplied else self.output / "native-headers.jsonl"
                cache.write_text(json.dumps(header) + "\n")
                identity = {"headers_input_sha256": optimizer.sha256(cache) if supplied else None}
                if not supplied:
                    identity["generated_headers_sha256"] = optimizer.sha256(cache)
                optimizer.write_json(self.output / "run.json", identity)
                self.assertEqual(header["source_sha256"], optimizer.sha256(self.source))
                with patch.object(optimizer.Tools, "run", side_effect=AssertionError("No parser replay")), \
                        self.assertRaisesRegex(ValueError, "module identity"):
                    optimizer.run_headers(self.tools, [row], cache if supplied else None, identity)

    def test_valid_comment_unicode_module_and_legacy_headers_are_preserved(self) -> None:
        variants = (
            (b"module\nimport Mathlib\ndef x : Nat := 0\n", (("Mathlib", ()),), True),
            ("-- \u03bb heading\nmodule\n-- note\npublic meta import all Foo.\u0394\n-- tail\ndef x : Nat := 0\n".encode(),
             (("Foo.\u0394", ("public", "meta", "all")),), True),
            ("-- \u03bb heading\r\nmodule\r\nimport Mathlib\r\ndef x : Nat := 0\r\n".encode(), (("Mathlib", ()),), True),
            (b"-- legacy header\nimport Mathlib\ndef x : Nat := 0\n", (("Mathlib", ()),), False),
        )
        for data, imports, is_module in variants:
            with self.subTest(data=data):
                row, header = self.fixture(data, imports, is_module=is_module)
                self.save_cache(header)
                self.assertEqual(optimizer.cached_headers(self.root, self.cache, [row]), {"A.lean": header})
                with self.external_header(header):
                    self.assertEqual(optimizer.native_headers(self.tools, [row]), {"A.lean": header})
                generated = self.output / "native-headers.jsonl"
                identity = {"generated_headers_sha256": optimizer.sha256(generated), "headers_input_sha256": None}
                optimizer.write_json(self.output / "run.json", identity)
                with patch.object(optimizer.Tools, "run", side_effect=AssertionError("No parser replay")):
                    self.assertEqual(optimizer.run_headers(self.tools, [row], None, identity), {"A.lean": header})


if __name__ == "__main__":
    unittest.main()
