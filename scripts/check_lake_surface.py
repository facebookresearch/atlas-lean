#!/usr/bin/env python3
"""Keep the archived v1 package outside the root Lake build graph."""

from __future__ import annotations

import json
import re
import sys
import tomllib
from pathlib import Path
from typing import NoReturn


def fail(message: str) -> NoReturn:
    print(f"FAIL [build surface]: {message}", file=sys.stderr)
    raise SystemExit(1)


def check_manifest() -> None:
    path = Path("lake-manifest.json")
    try:
        with path.open() as manifest_file:
            manifest = json.load(manifest_file)
    except (OSError, json.JSONDecodeError) as error:
        fail(f"cannot read root lake-manifest.json: {error}")
    if not isinstance(manifest, dict):
        fail("root lake-manifest.json must contain an object")

    allowed_top_level = {
        "version",
        "packagesDir",
        "packages",
        "name",
        "lakeDir",
        "fixedToolchain",
    }
    extra_top_level = sorted(manifest.keys() - allowed_top_level)
    if extra_top_level:
        fail(f"unapproved manifest setting: {', '.join(extra_top_level)}")
    if manifest.get("name") != "atlas":
        fail("root manifest package must be atlas")
    if manifest.get("packagesDir") != ".lake/packages":
        fail("root manifest packagesDir must be .lake/packages")
    if manifest.get("lakeDir") != ".lake":
        fail("root manifest lakeDir must be .lake")

    expected_sources = {
        "mathlib": (
            "https://github.com/leanprover-community/mathlib4",
            "leanprover-community",
        ),
        "cslib": (
            "https://github.com/leanprover/cslib",
            "leanprover",
        ),
        "plausible": (
            "https://github.com/leanprover-community/plausible",
            "leanprover-community",
        ),
        "LeanSearchClient": (
            "https://github.com/leanprover-community/LeanSearchClient",
            "leanprover-community",
        ),
        "importGraph": (
            "https://github.com/leanprover-community/import-graph",
            "leanprover-community",
        ),
        "proofwidgets": (
            "https://github.com/leanprover-community/ProofWidgets4",
            "leanprover-community",
        ),
        "aesop": (
            "https://github.com/leanprover-community/aesop",
            "leanprover-community",
        ),
        "Qq": (
            "https://github.com/leanprover-community/quote4",
            "leanprover-community",
        ),
        "batteries": (
            "https://github.com/leanprover-community/batteries",
            "leanprover-community",
        ),
        "Cli": ("https://github.com/leanprover/lean4-cli", "leanprover"),
    }
    packages = manifest.get("packages")
    if not isinstance(packages, list) or not all(
        isinstance(package, dict) for package in packages
    ):
        fail("root manifest packages must be an array of objects")

    names = [package.get("name") for package in packages]
    if not all(isinstance(name, str) for name in names):
        fail("every manifest package must have a string name")
    if len(names) != len(set(names)) or set(names) != set(expected_sources):
        fail("root manifest dependency set does not match pinned dependencies")

    allowed_package_keys = {
        "url",
        "type",
        "subDir",
        "scope",
        "rev",
        "name",
        "manifestFile",
        "inputRev",
        "inherited",
        "configFile",
    }
    commit = re.compile(r"[0-9a-f]{40}")
    for package in packages:
        name = package["name"]
        extra_keys = sorted(package.keys() - allowed_package_keys)
        if extra_keys:
            fail(f"manifest package {name} has unapproved fields: {', '.join(extra_keys)}")
        expected_url, expected_scope = expected_sources[name]
        if package.get("type") != "git" or package.get("url") != expected_url:
            fail(f"manifest package {name} must use its pinned public git source")
        if package.get("scope") != expected_scope:
            fail(f"manifest package {name} has the wrong scope")
        if package.get("subDir") is not None:
            fail(f"manifest package {name} must not redirect to a subdirectory")
        if package.get("manifestFile") != "lake-manifest.json":
            fail(f"manifest package {name} has an unapproved manifest path")
        if package.get("configFile") not in {"lakefile.lean", "lakefile.toml"}:
            fail(f"manifest package {name} has an unapproved Lake config path")
        revision = package.get("rev")
        if not isinstance(revision, str) or commit.fullmatch(revision) is None:
            fail(f"manifest package {name} is not pinned to a commit")

    mathlib = packages[names.index("mathlib")]
    if mathlib.get("inputRev") != "v4.35.0" or mathlib.get("rev") != (
        "56a005855ea17e0b0958f73ec801ae140b0a1679"
    ):
        fail("manifest Mathlib revision does not match lakefile.toml")
    if mathlib.get("inherited") is not False:
        fail("Mathlib must be the root package's direct dependency")
    cslib = packages[names.index("cslib")]
    if cslib.get("inputRev") != "v4.35.0" or cslib.get("rev") != (
        "5b56df99362532c46e1175381fbbdd755bd56030"
    ):
        fail("manifest CSLib revision does not match lakefile.toml")
    if cslib.get("inherited") is not False:
        fail("CSLib must be a direct root dependency")
    if any(
        package.get("inherited") is not True
        for package in packages
        if package["name"] not in {"mathlib", "cslib"}
    ):
        fail("only Mathlib and CSLib may be direct root dependencies")


def main() -> None:
    path = Path("lakefile.toml")
    if Path("lakefile.lean").exists():
        fail("root lakefile.lean would override the audited lakefile.toml")
    try:
        with path.open("rb") as lakefile:
            config = tomllib.load(lakefile)
    except (OSError, tomllib.TOMLDecodeError) as error:
        fail(f"cannot read root lakefile.toml: {error}")

    allowed_top_level = {
        "name",
        "version",
        "keywords",
        "defaultTargets",
        "testDriver",
        "leanOptions",
        "require",
        "lean_lib",
    }
    extra_top_level = sorted(config.keys() - allowed_top_level)
    if extra_top_level:
        fail(f"unapproved root target or setting: {', '.join(extra_top_level)}")

    if config.get("defaultTargets") != ["MathlibExt", "CSLibExt", "WantedExt"]:
        fail("root default targets must be MathlibExt, CSLibExt, and WantedExt")
    if config.get("testDriver") != "MathlibExtTest":
        fail("root test driver must be MathlibExtTest")

    expected_requirements = [
        {
            "name": "mathlib",
            "scope": "leanprover-community",
            "rev": "v4.35.0",
        },
        {
            "name": "cslib",
            "scope": "leanprover",
            "rev": "v4.35.0",
        },
    ]
    if config.get("require") != expected_requirements:
        fail("the root package may depend only on pinned public releases")

    expected_globs = {
        "CSLibExt": ["CSLibExt.+"],
        "CSLibExtTest": ["CSLibExtTest.+"],
        "MathlibExt": ["MathlibExt.+"],
        "MathlibExtTest": ["MathlibExtTest.+"],
        "WantedExt": ["WantedExt.+"],
    }
    libraries = config.get("lean_lib")
    if not isinstance(libraries, list) or not all(
        isinstance(library, dict) for library in libraries
    ):
        fail("root Lean libraries must be declared as an array of tables")

    names = [library.get("name") for library in libraries]
    if not all(isinstance(name, str) for name in names):
        fail("every root Lean library must have a string name")
    if len(names) != len(set(names)) or set(names) != set(expected_globs):
        fail(
            "root Lean libraries must be CSLibExt, CSLibExtTest, "
            "MathlibExt, MathlibExtTest, and WantedExt"
        )

    allowed_library_keys = {"name", "globs", "leanOptions"}
    for library in libraries:
        name = library["name"]
        extra_keys = sorted(library.keys() - allowed_library_keys)
        if extra_keys:
            fail(f"{name} has unapproved build fields: {', '.join(extra_keys)}")
        if library.get("globs") != expected_globs[name]:
            fail(f"{name} must use only its matching source glob")

    check_manifest()
    print("ok [build surface]: archived v1 is outside the root Lake build graph.")


if __name__ == "__main__":
    main()
