#!/usr/bin/env python3
"""Discover and build publication formalizations with the root dependency pins."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import tomllib
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Publication:
    name: str
    source_dir: Path
    modules: tuple[str, ...]


def collect_modules(directory: Path, source_dir: Path) -> tuple[str, ...]:
    if directory.is_symlink():
        raise ValueError(f"symlinked paths are not allowed in formalizations: {directory}")
    modules = []
    for path in sorted(directory.rglob("*")):
        if path.is_symlink():
            raise ValueError(f"symlinked paths are not allowed in formalizations: {path}")
        if not path.is_file() or path.suffix != ".lean":
            continue
        parts = path.relative_to(source_dir).with_suffix("").parts
        if not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part) for part in parts):
            raise ValueError(f"invalid Lean module path: {path}")
        modules.append(".".join(parts))
    return tuple(modules)


def discover(root: Path, config: dict) -> list[Publication]:
    base = root / "Formalized Publications"
    if base.is_symlink():
        raise ValueError(f"symlinked publication directory: {base}")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    reserved = {"init", "lean", "lake", "std"}
    reserved.update(library["name"].casefold() for library in config["lean_lib"])
    reserved.update(package["name"].casefold() for package in manifest["packages"])
    publications = []
    owners = {}
    for group in ("Papers", "Notes"):
        directory = base / group
        if directory.is_symlink():
            raise ValueError(f"symlinked publication directory: {directory}")
        if not directory.exists():
            continue
        for paper in sorted(directory.iterdir()):
            if paper.name.startswith("."):
                continue
            if paper.is_symlink():
                raise ValueError(f"symlinked publication directory: {paper}")
            if not paper.is_dir():
                continue
            if re.fullmatch(r"[A-Z][A-Za-z0-9]*", paper.name) is None:
                raise ValueError(f"publication folder must use UpperCamelCase: {paper}")
            source_dir = paper / "Formalization"
            if source_dir.is_symlink() or not source_dir.is_dir():
                raise ValueError(f"missing or symlinked Formalization directory: {paper}")
            for required in (
                paper / "Readme.md",
                paper / "Papers" / "citation.bib",
                source_dir / f"{paper.name}.lean",
            ):
                if not required.is_file():
                    raise ValueError(f"missing required publication file: {required}")
            for extension in ("pdf", "html"):
                files = (paper / "Papers").glob(f"*.{extension}")
                if not any(path.is_file() for path in files):
                    raise ValueError(f"missing {extension.upper()} paper in: {paper / 'Papers'}")
            for extension in ("lean", "json"):
                files = (paper / "Comparator").glob(f"*.{extension}")
                if not any(path.is_file() for path in files):
                    raise ValueError(
                        f"missing comparator {extension} file in: {paper / 'Comparator'}"
                    )
            modules = collect_modules(source_dir, source_dir)
            label = paper.relative_to(root).as_posix()
            for module in modules:
                prefix = module.split(".", 1)[0]
                if prefix.casefold() in reserved:
                    raise ValueError(f"publication module shadows an existing library: {module}")
                if prefix in owners and owners[prefix] != label:
                    raise ValueError(
                        f"module prefix {prefix} is shared by {owners[prefix]} and {label}; "
                        "use a unique module namespace for each publication"
                    )
                owners[prefix] = label
            publications.append(
                Publication(
                    f"Publication_{group}_{paper.name}",
                    source_dir.relative_to(root),
                    modules,
                )
            )
    return publications


def configuration(source: str, publications: list[Publication]) -> str:
    tables = [source.rstrip()]
    for publication in publications:
        tables.append(
            "\n".join((
                "[[lean_lib]]",
                f"name = {json.dumps(publication.name)}",
                f"srcDir = {json.dumps(publication.source_dir.as_posix())}",
                "roots = []",
                f"globs = {json.dumps(publication.modules)}",
            ))
        )
    return "\n\n".join(tables) + "\n"


def run_lake(
    root: Path, source: str, publications: list[Publication], args: list[str]
) -> int:
    # Keep the generated configuration outside the repository; source paths and
    # the manifest remain relative to the root package, selected with -d.
    with tempfile.TemporaryDirectory(prefix="atlas-publications-") as temporary:
        path = Path(temporary) / "lakefile.toml"
        path.write_text(configuration(source, publications))
        return subprocess.run(
            ["lake", "-d", str(root), "-f", str(path), *args], cwd=root
        ).returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "imports", "policy", "build", "env"))
    parser.add_argument("args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.command in {"check", "imports", "policy"} and args.args:
        parser.error(f"{args.command} takes no arguments")
    if args.command == "env" and not args.args:
        parser.error("env requires a command, for example: env lean file.lean")
    root = Path(__file__).resolve().parent.parent
    try:
        source = (root / "lakefile.toml").read_text()
        config = tomllib.loads(source)
        publications = discover(root, config)
        modules = sorted(
            module for publication in publications for module in publication.modules
        )
        if args.command == "check":
            count = len(publications)
            noun = "publication" if count == 1 else "publications"
            module_noun = "module" if len(modules) == 1 else "modules"
            print(f"ok [publications]: {count} {noun}, {len(modules)} Lean {module_noun}.")
        elif args.command == "imports":
            for module in modules:
                print(f"import {module}")
        elif args.command == "policy":
            names = ", ".join(f"`{module}" for module in modules)
            print(f"private def publicationModules : Array Lean.Name :=\n  #[{names}]")
        elif args.command == "build":
            targets = args.args or (
                [library["name"] for library in config["lean_lib"]]
                + [publication.name for publication in publications]
            )
            return run_lake(root, source, publications, ["build", *targets])
        else:
            return run_lake(root, source, publications, ["env", *args.args])
    except (OSError, ValueError, KeyError) as error:
        print(f"FAIL [publications]: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
