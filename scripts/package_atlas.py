#!/usr/bin/env python3
"""Build, verify, and install a pinned distribution of Atlas libraries.

Python 3.11+; build additionally needs Git, elan/Lake, and the selected toolchain.
All library sources are read from Git objects, never the working tree.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import tomllib

SCHEMA = "atlas-lake-package/1"
MANIFEST = "atlas-package.json"
MAX_MANIFEST_BYTES = 64 * 1024 * 1024
ROOT_METADATA = ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "LICENSE", "NOTICE")
REPOSITORY = "https://github.com/facebookresearch/atlas-lean"
HEX = re.compile(r"^[0-9a-f]{64}$")
DEFAULT_REPO = Path(__file__).resolve().parent.parent


class PackageError(Exception):
    pass


def canonical(value):
    return (json.dumps(value, sort_keys=True, ensure_ascii=False, indent=2) + "\n").encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digest_file(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def strict_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise PackageError(f"Duplicate JSON key: {key}")
            result[key] = value
        return result
    try:
        return json.loads(data, object_pairs_hook=pairs)
    except (ValueError, UnicodeDecodeError) as exc:
        raise PackageError(f"Invalid manifest JSON: {exc}") from exc


def safe_path(value):
    if not isinstance(value, str) or not value or "\\" in value or "\0" in value:
        raise PackageError(f"Invalid package path: {value!r}")
    path = PurePosixPath(value)
    if path.is_absolute() or any(p in ("", ".", "..") for p in value.split("/")):
        raise PackageError(f"Unsafe package path: {value!r}")
    return path


def host_target():
    return f"{platform.system().lower()}-{platform.machine().lower()}"


def libraries_of(config):
    libraries = config.get("lean_lib", [])
    if not isinstance(libraries, list) or not libraries:
        raise PackageError("The selected root lakefile.toml has no lean_lib declarations")
    names = []
    if (config.get("srcDir", ".") != "." or config.get("lakeDir", ".lake") != ".lake"
            or config.get("buildDir", ".lake/build") != ".lake/build"):
        raise PackageError("This packager requires the standard root source/Lake/build directories")
    for library in libraries:
        name = library.get("name", "")
        if not re.fullmatch(r"[^\W\d]\w*", name, re.UNICODE):
            raise PackageError(f"Expected a top-level library name, got {name!r}")
        if name in names:
            raise PackageError(f"Duplicate library: {name}")
        if library.get("srcDir", ".") != "." or library.get("roots", [name]) != [name]:
            raise PackageError(f"{name}: nested/alternate source roots need explicit packaging support")
        for glob in library.get("globs", [name]):
            if glob != name and not glob.startswith(name + "."):
                raise PackageError(f"{name}: glob {glob!r} escapes its top-level root")
        names.append(name)
    return names


class GitSnapshot:
    def __init__(self, repo, revision):
        self.repo = Path(repo).resolve()
        self.revision = self.git("rev-parse", "--verify", "--end-of-options",
                                 revision + "^{commit}").decode().strip()
        if not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", self.revision):
            raise PackageError("Git did not resolve the requested commit")
        self.config = tomllib.loads(self.read("lakefile.toml").decode())
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9-]*", self.config.get("name", "")):
            raise PackageError("The selected package name is not a safe directory name")
        self.libraries = libraries_of(self.config)
        specs = [*ROOT_METADATA, *self.libraries, *(x + ".lean" for x in self.libraries)]
        records = self.git("ls-tree", "-r", "-l", "-z", self.revision, "--", *specs)
        self.files = {}
        for record in records.split(b"\0"):
            if not record:
                continue
            header, path_bytes = record.split(b"\t", 1)
            mode, kind, oid, size = header.decode().split()
            path = path_bytes.decode()
            safe_path(path)
            if kind != "blob" or mode not in ("100644", "100755"):
                raise PackageError(f"Unsupported source entry {path}: {mode} {kind}")
            self.files[path] = {"git_blob": oid, "bytes": int(size), "mode": mode}
        for required in ROOT_METADATA[:3]:
            if required not in self.files:
                raise PackageError(f"Missing committed {required}")
        manifest = strict_json(self.read("lake-manifest.json"))
        if manifest.get("packagesDir", ".lake/packages") != ".lake/packages":
            raise PackageError("The dependency manifest must use .lake/packages")
        if self.config.get("name") != manifest.get("name"):
            raise PackageError("Lake configuration and resolved manifest package names differ")

    def git(self, *args):
        result = subprocess.run(["git", "-C", str(self.repo), *args],
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode:
            raise PackageError(result.stderr.decode(errors="replace").strip())
        return result.stdout

    def read(self, path):
        return self.git("show", f"{self.revision}:{path}")

    def export(self, destination):
        # Git archive is one batched read. Validate exact Git blob identities too:
        # export-ignore/export-subst attributes must not alter the selected inputs.
        specs = sorted({p.split("/")[0] for p in self.files})
        process = subprocess.Popen(
            ["git", "-C", str(self.repo), "archive", "--format=tar", self.revision, "--", *specs],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        seen = set()
        try:
            with tarfile.open(fileobj=process.stdout, mode="r|") as archive:
                for member in archive:
                    if member.isdir():
                        continue
                    path = member.name
                    if not member.isfile() or path not in self.files:
                        raise PackageError(f"Unexpected Git archive entry: {path}")
                    record = self.files[path]
                    if member.size != record["bytes"] or path in seen:
                        raise PackageError(f"Invalid Git archive entry: {path}")
                    target = destination / safe_path(path)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    algorithm = hashlib.sha1 if len(record["git_blob"]) == 40 else hashlib.sha256
                    blob = algorithm(f"blob {member.size}\0".encode())
                    with archive.extractfile(member) as source, target.open("wb") as output:
                        for chunk in iter(lambda: source.read(1024 * 1024), b""):
                            blob.update(chunk)
                            output.write(chunk)
                    if blob.hexdigest() != record["git_blob"]:
                        raise PackageError(f"Git archive changed {path}; check export attributes")
                    target.chmod(0o755 if record["mode"] == "100755" else 0o644)
                    seen.add(path)
            process.stdout.close()
            error = process.stderr.read().decode(errors="replace")
            if process.wait():
                raise PackageError(error.strip())
        finally:
            process.stdout.close()
            process.stderr.close()
            process.wait()
        missing = set(self.files) - seen
        if missing:
            raise PackageError(f"Git archive omitted selected inputs: {sorted(missing)[:8]}")
        for library in self.libraries:
            (destination / library).mkdir(exist_ok=True)


def environment(jobs):
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LAKE_PACKAGES_DIR", "ELAN_TOOLCHAIN"):
        env.pop(key, None)
    env["LEAN_NUM_THREADS"] = str(jobs)
    env["LAKE_ARTIFACT_CACHE"] = "true"
    env["LAKE_RESTORE_ARTIFACTS"] = "true"
    return env


def run_logged(command, cwd, env, log):
    print("Running: " + " ".join(command), file=sys.stderr, flush=True)
    with log.open("ab") as output:
        output.write(("\n$ " + " ".join(command) + "\n").encode())
        output.flush()
        result = subprocess.run(command, cwd=cwd, env=env, stdout=output,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        raise PackageError(f"Command failed ({result.returncode}); see {log}")


def seed_dependencies(package, cache):
    if cache is None:
        return
    cache = Path(cache).resolve()
    manifest = strict_json((package / "lake-manifest.json").read_bytes())
    if manifest.get("packagesDir", ".lake/packages") != ".lake/packages":
        raise PackageError("Dependency cache path escapes the package")
    destination = package / manifest.get("packagesDir", ".lake/packages")
    destination.mkdir(parents=True, exist_ok=True)
    for entry in manifest["packages"]:
        if entry.get("type") != "git":
            raise PackageError(f"Only pinned Git dependencies can be seeded: {entry['name']}")
        candidate = cache / entry["name"]
        if not candidate.is_dir():
            continue
        head = subprocess.run(["git", "-C", str(candidate), "rev-parse", "HEAD"],
                              text=True, capture_output=True)
        dirty = subprocess.run(["git", "-C", str(candidate), "status", "--porcelain",
                                "--untracked-files=no"], text=True, capture_output=True)
        if head.returncode or dirty.returncode or dirty.stdout or head.stdout.strip() != entry["rev"]:
            raise PackageError(f"Dependency cache {candidate} differs from the pinned clean revision")
        (destination / entry["name"]).symlink_to(candidate, target_is_directory=True)


def module_name(path):
    parts = list(PurePosixPath(path).with_suffix("").parts)
    if any("»" in x or "«" in x for x in parts):
        raise PackageError(f"Unsupported module-name delimiter in {path}")
    return ".".join("«" + x + "»" for x in parts)




def validate_checkout(package, env, log, modules_file=None):
    """Reuse the canonical CI validators; this wrapper defines no trust policy."""
    scripts = Path(__file__).resolve().parent
    command = ["bash", str(scripts / "check.sh"), "build", "--root", str(package)]
    if modules_file:
        command += ["--modules", str(modules_file)]
    run_logged(command, package, env, log)
    return {name: digest_file(scripts / name) for name in
            ("check.sh", "check_diagnostics.sh", "check_axioms.sh")}


def qualify(snapshot, package, jobs, dependency_cache, log):
    env = environment(jobs)
    seed_dependencies(package, dependency_cache)
    run_logged(["lake", "exe", "cache", "get"], package, env, log)
    validators = validate_checkout(package, env, log)
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=package,
                             env=env, capture_output=True, text=True, check=True).stdout.strip()
    return {"status": "passed", "policy": "canonical Atlas CI build and axiom policy",
            "validation_scripts_sha256": validators, "lean_version": version,
            "log_sha256": digest_file(log)}


def file_record(package, path, kind, original=None):
    safe_path(path)
    target = package / path
    if target.is_symlink() or not target.is_file():
        raise PackageError(f"Package entries must be regular files: {path}")
    result = {"path": path, "kind": kind, "bytes": target.stat().st_size,
              "sha256": digest_file(target),
              "mode": 0o755 if target.stat().st_mode & 0o111 else 0o644}
    if original:
        algorithm = hashlib.sha1 if len(original["git_blob"]) == 40 else hashlib.sha256
        blob = algorithm(f"blob {result['bytes']}\0".encode())
        with target.open("rb") as source:
            for chunk in iter(lambda: source.read(1024 * 1024), b""):
                blob.update(chunk)
        if (result["bytes"] != original["bytes"] or blob.hexdigest() != original["git_blob"]
                or result["mode"] != (0o755 if original["mode"] == "100755" else 0o644)):
            raise PackageError(f"Source changed during qualification: {path}")
        result["git_blob"] = original["git_blob"]
    return result


def pack(package, manifest, archive):
    manifest_bytes = canonical(manifest)
    if len(manifest_bytes) > MAX_MANIFEST_BYTES:
        raise PackageError("Manifest exceeds this format's 64 MiB limit; use smaller release components")
    (package / MANIFEST).write_bytes(manifest_bytes)
    prefix = manifest["package_name"]
    directories = {prefix}
    for row in manifest["files"]:
        path = PurePosixPath(prefix) / row["path"]
        directories.update(str(parent) for parent in path.parents if str(parent) != ".")
    with archive.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz:
        with tarfile.open(fileobj=gz, mode="w|", format=tarfile.PAX_FORMAT) as tar:
            for directory in sorted(directories):
                info = tarfile.TarInfo(directory)
                info.type = tarfile.DIRTYPE
                info.mode = 0o755
                tar.addfile(info)
            info = tarfile.TarInfo(prefix + "/" + MANIFEST)
            info.size = len(manifest_bytes)
            info.mode = 0o644
            tar.addfile(info, io.BytesIO(manifest_bytes))
            for row in manifest["files"]:
                info = tarfile.TarInfo(prefix + "/" + row["path"])
                info.size, info.mode = row["bytes"], row["mode"]
                with (package / row["path"]).open("rb") as source:
                    tar.addfile(info, source)


def build(snapshot, out_dir, *, source_only=False, jobs=32, dependency_cache=None,
          offline_bundle=False):
    out_dir = Path(out_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    target = "source" if source_only else host_target()
    stem = f"atlas-{snapshot.revision}-{target}"
    archive, descriptor = out_dir / (stem + ".tar.gz"), out_dir / (stem + ".json")
    index = out_dir / (stem + ".manifest.json")
    native_dir = out_dir / (stem + ".lake-cache")
    if any(path.exists() for path in (archive, descriptor, index, native_dir)):
        raise PackageError(f"Output already exists for {stem}; reuse it or choose a new output directory")
    log = out_dir / (stem + ".build.log")
    with tempfile.TemporaryDirectory(prefix=".atlas-package-", dir=out_dir) as temporary:
        package = Path(temporary) / snapshot.config["name"]
        package.mkdir()
        snapshot.export(package)
        qualification = {"status": "not_run", "reason": "explicit source-only preview"}
        if not source_only:
            qualification = qualify(snapshot, package, jobs, dependency_cache, log)
            qualification["build_workers"] = jobs
        for library in snapshot.libraries:
            for path in (package / library).rglob("*"):
                if path.is_symlink() or (path.is_file() and path.relative_to(package).as_posix() not in snapshot.files):
                    raise PackageError(f"Uncommitted source generated during qualification: {path}")
        records = [file_record(package, path, "source", row)
                   for path, row in sorted(snapshot.files.items())]
        artifact_dir = package / ".lake/build"
        if not source_only and artifact_dir.exists():
            for path in sorted(artifact_dir.rglob("*")):
                if path.is_symlink():
                    raise PackageError(f"Unexpected artifact symlink: {path}")
                if path.is_file():
                    records.append(file_record(package, path.relative_to(package).as_posix(), "artifact"))
        native = None
        if not source_only:
            # Native Lake cache: source remains a normal Git dependency.
            before = set((package / ".lake").glob("*.tar.gz"))
            run_logged(["lake", "pack"], package, environment(jobs), log)
            candidates = set((package / ".lake").glob("*.tar.gz")) - before
            if len(candidates) != 1:
                raise PackageError("Lake did not produce one default build archive")
            native = candidates.pop()
            qualification["log_sha256"] = digest_file(log)
        manifest = {
            "schema": SCHEMA, "package_name": snapshot.config["name"],
            "package_version": snapshot.config.get("version"),
            "source_repository": REPOSITORY, "source_revision": snapshot.revision,
            "libraries": snapshot.libraries,
            "toolchain": (package / "lean-toolchain").read_text().strip(),
            "dependency_lock_sha256": digest_file(package / "lake-manifest.json"),
            "target": target, "qualification": qualification, "files": records,
            "producer_script_sha256": digest_file(__file__),
        }
        manifest["source_manifest_sha256"] = sha(canonical([r for r in records if r["kind"] == "source"]))
        manifest_bytes = canonical(manifest)
        result = {"schema": SCHEMA, "source_revision": snapshot.revision,
                  "package_name": manifest["package_name"], "libraries": snapshot.libraries,
                  "qualification": qualification["status"], "target": target,
                  "build_manifest": str(index), "manifest_sha256": sha(manifest_bytes)}
        if native:
            native_dir.mkdir()
            destination = native_dir / native.name
            os.link(native, destination)
            result["lake_build_archive"] = str(destination)
            result["lake_build_archive_sha256"] = digest_file(destination)
            result["lake_build_archive_bytes"] = destination.stat().st_size
            destination.with_name(destination.name + ".sha256").write_text(
                result["lake_build_archive_sha256"] + "  " + destination.name + "\n")
        if source_only or offline_bundle:
            staging = Path(temporary) / "package.tar.gz"
            pack(package, manifest, staging)
            result.update(archive=str(archive), archive_sha256=digest_file(staging),
                          archive_bytes=staging.stat().st_size)
            os.link(staging, archive)
            (out_dir / (stem + ".tar.gz.sha256")).write_text(
                result["archive_sha256"] + "  " + archive.name + "\n")
        # Consumers see an archive only after all required qualification succeeds.
        index.write_bytes(manifest_bytes)
        published = dict(result)
        for field in ("build_manifest", "lake_build_archive", "archive"):
            if field in published:
                published[field] = Path(published[field]).name
        descriptor.write_bytes(canonical(published))
    return result


def verify_build_archive(archive, expected_sha256):
    """Verify a native Lake build asset against its trusted descriptor digest."""
    archive = Path(archive)
    if not HEX.fullmatch(expected_sha256) or digest_file(archive) != expected_sha256:
        raise PackageError("Native build archive SHA-256 does not match the trusted expected digest")
    return {"verified": True, "format": "lake-build-cache", "archive": str(archive),
            "sha256": expected_sha256, "bytes": archive.stat().st_size}


def validate_manifest(manifest):
    if manifest.get("schema") != SCHEMA:
        raise PackageError("Unknown package schema")
    name = manifest.get("package_name", "")
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9-]*", name):
        raise PackageError("Invalid package name")
    if (not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", manifest.get("source_revision", ""))
            or manifest.get("source_repository") != REPOSITORY):
        raise PackageError("Invalid Atlas source identity")
    libraries = manifest.get("libraries", [])
    if (not isinstance(libraries, list) or not libraries or len(set(libraries)) != len(libraries)
            or any(not isinstance(x, str) or not re.fullmatch(r"[^\W\d]\w*", x) for x in libraries)):
        raise PackageError("Invalid library list")
    rows = manifest.get("files", [])
    records = {}
    for row in rows:
        path = str(safe_path(row["path"]))
        if path in records or path == MANIFEST:
            raise PackageError(f"Duplicate/reserved manifest path: {path}")
        if row.get("kind") not in ("source", "artifact") or not HEX.fullmatch(row.get("sha256", "")):
            raise PackageError(f"Invalid file record: {path}")
        if type(row.get("bytes")) is not int or row["bytes"] < 0 or row.get("mode") not in (0o644, 0o755):
            raise PackageError(f"Invalid file size/mode: {path}")
        if row["kind"] == "artifact":
            if not path.startswith(".lake/build/"):
                raise PackageError(f"Artifact outside build directory: {path}")
        elif (path not in ROOT_METADATA and path not in (x + ".lean" for x in libraries)
              and path.split("/")[0] not in libraries):
            raise PackageError(f"Source outside declared library roots: {path}")
        records[path] = row
    for required in ROOT_METADATA[:3]:
        if required not in records or records[required]["kind"] != "source":
            raise PackageError(f"Manifest missing {required}")
    source_root = sha(canonical([r for r in rows if r["kind"] == "source"]))
    if source_root != manifest.get("source_manifest_sha256"):
        raise PackageError("Source manifest root does not match its entries")
    if records["lake-manifest.json"]["sha256"] != manifest.get("dependency_lock_sha256"):
        raise PackageError("Dependency lock digest does not match")
    return records


def read_archive(archive, expected_sha256, *, destination=None, allow_source_only=False):
    archive = Path(archive)
    if not HEX.fullmatch(expected_sha256) or digest_file(archive) != expected_sha256:
        raise PackageError("Archive SHA-256 does not match the trusted expected digest")
    manifest, records, prefix = None, None, None
    seen, directories = set(), []
    install_artifacts = False
    with tarfile.open(archive, mode="r|gz") as tar:
        for member in tar:
            path = safe_path(member.name)
            if not (member.isdir() or member.isfile()):
                raise PackageError(f"Symlinks, hardlinks, and special files are forbidden: {member.name}")
            if member.isdir():
                directories.append(str(path))
                continue
            if manifest is None:
                if len(path.parts) != 2 or path.name != MANIFEST or member.size > MAX_MANIFEST_BYTES:
                    raise PackageError("The first archive file must be the bounded package manifest")
                prefix = path.parts[0]
                manifest = strict_json(tar.extractfile(member).read())
                records = validate_manifest(manifest)
                if prefix != manifest["package_name"]:
                    raise PackageError("Archive prefix and package name differ")
                if manifest.get("qualification", {}).get("status") != "passed" and not allow_source_only:
                    raise PackageError("Source-only preview is not qualified; build without --source-only")
                install_artifacts = manifest["target"] == host_target()
                if destination:
                    (destination / MANIFEST).write_bytes(canonical(manifest))
                continue
            if path.parts[0] != prefix or len(path.parts) < 2:
                raise PackageError(f"Entry outside the package prefix: {member.name}")
            relative = PurePosixPath(*path.parts[1:]).as_posix()
            if relative not in records or relative in seen:
                raise PackageError(f"Unexpected/duplicate archive file: {member.name}")
            row = records[relative]
            if member.size != row["bytes"]:
                raise PackageError(f"Wrong file size: {relative}")
            h = hashlib.sha256()
            write = destination and (row["kind"] == "source" or install_artifacts)
            target = destination / relative if write else None
            if target:
                target.parent.mkdir(parents=True, exist_ok=True)
            output = target.open("wb") if target else None
            try:
                with tar.extractfile(member) as source:
                    for chunk in iter(lambda: source.read(1024 * 1024), b""):
                        h.update(chunk)
                        if output:
                            output.write(chunk)
            finally:
                if output:
                    output.close()
            if h.hexdigest() != row["sha256"]:
                raise PackageError(f"File SHA-256 mismatch: {relative}")
            if target:
                target.chmod(row["mode"] & ~0o222 if row["kind"] == "source" else row["mode"])
            seen.add(relative)
    if manifest is None or seen != set(records):
        raise PackageError("Archive is missing its manifest or declared files")
    parents = {prefix}
    for row in records.values():
        parents.update(str(p) for p in (PurePosixPath(prefix) / row["path"]).parents if str(p) != ".")
    if any(p not in parents for p in directories) or len(directories) != len(set(directories)):
        raise PackageError("Unexpected or duplicate archive directory")
    if destination:
        for library in manifest["libraries"]:
            (destination / library).mkdir(exist_ok=True)
    return manifest, install_artifacts


def verify_directory(package, expected_manifest_sha256=None):
    package = Path(package).resolve()
    if expected_manifest_sha256 is not None:
        if (not HEX.fullmatch(expected_manifest_sha256)
                or digest_file(package / MANIFEST) != expected_manifest_sha256):
            raise PackageError("Installed manifest differs from the trusted lock digest")
    manifest = strict_json((package / MANIFEST).read_bytes())
    records = validate_manifest(manifest)
    expected = {p for p, r in records.items() if r["kind"] == "source"}
    for path in expected:
        target = package / path
        if target.is_symlink() or not target.is_file() or digest_file(target) != records[path]["sha256"]:
            raise PackageError(f"Installed source changed or disappeared: {path}")
    allowed = {MANIFEST, ".lake", *manifest["libraries"],
               *(PurePosixPath(p).parts[0] for p in expected)}
    extra = {p.name for p in package.iterdir()} - allowed
    if extra:
        raise PackageError(f"Unexpected top-level package entries: {sorted(extra)}")
    for library in manifest["libraries"]:
        root = package / library
        if root.is_symlink() or not root.is_dir():
            raise PackageError(f"Library root is missing or is a symlink: {root}")
        for path in root.rglob("*"):
            if path.is_symlink() or (path.is_file() and path.relative_to(package).as_posix() not in expected):
                raise PackageError(f"Unexpected source entry: {path}")
    config = tomllib.loads((package / "lakefile.toml").read_text())
    if libraries_of(config) != manifest["libraries"] or config["name"] != manifest["package_name"]:
        raise PackageError("Installed Lake configuration differs from the declared package surface")
    return manifest


def install(archive, expected_sha256, into, *, allow_source_only=False):
    if not HEX.fullmatch(expected_sha256):
        raise PackageError("Expected archive digest must be 64 lowercase hexadecimal characters")
    into = Path(into).resolve()
    into.mkdir(parents=True, exist_ok=True)
    final = into / expected_sha256
    if final.exists():
        manifest = verify_directory(final)
        # Reverify the supplied archive and its identity, even on an idempotent install.
        published, _ = read_archive(archive, expected_sha256, allow_source_only=allow_source_only)
        if canonical(manifest) != canonical(published):
            raise PackageError("Existing content-addressed installation has a different manifest")
        return installation_result(final, manifest, expected_sha256)
    with tempfile.TemporaryDirectory(prefix=".atlas-install-", dir=into) as temporary:
        package = Path(temporary) / "package"
        package.mkdir()
        manifest, _ = read_archive(archive, expected_sha256, destination=package,
                                   allow_source_only=allow_source_only)
        verify_directory(package)
        package.rename(final)
    return installation_result(final, manifest, expected_sha256)


def installation_result(path, manifest, archive_sha256):
    return {"package_path": str(path), "package_name": manifest["package_name"],
            "archive_sha256": archive_sha256, "source_revision": manifest["source_revision"],
            "libraries": manifest["libraries"], "qualification": manifest["qualification"]["status"],
            "lake_dependency": {"name": manifest["package_name"], "path": str(path)},
            "lock": {"schema": "atlas-consumer-lock/1", "repository": REPOSITORY,
                     "source_revision": manifest["source_revision"], "archive_sha256": archive_sha256,
                     "manifest_sha256": sha(canonical(manifest)),
                     "source_manifest_sha256": manifest["source_manifest_sha256"],
                     "dependency_lock_sha256": manifest["dependency_lock_sha256"],
                     "toolchain": manifest["toolchain"], "libraries": manifest["libraries"]}}








def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build_parser = sub.add_parser("build", help="Export an exact Git revision and qualify all declared libraries")
    build_parser.add_argument("--repo", type=Path, default=DEFAULT_REPO)
    build_parser.add_argument("--revision", default="HEAD")
    build_parser.add_argument("--out-dir", type=Path, required=True)
    build_parser.add_argument("--jobs", type=int, default=32,
                              help="Lean/Lake worker-pool size (default: 32)")
    build_parser.add_argument("--dependency-cache", type=Path)
    build_parser.add_argument("--source-only", action="store_true", help="Explicit unqualified development preview")
    build_parser.add_argument("--offline-bundle", action="store_true",
                              help="Also create the offline source/artifact bundle from the same build")
    verify_parser = sub.add_parser("verify", help="Verify an archive or installed source tree")
    verify_parser.add_argument("--archive", type=Path)
    verify_parser.add_argument("--build-archive", type=Path,
                               help="Verify a native Lake build asset's trusted SHA-256")
    verify_parser.add_argument("--sha256")
    verify_parser.add_argument("--directory", type=Path)
    verify_parser.add_argument("--manifest-sha256", help="Trusted installed-manifest digest from atlas.lock.json")
    verify_parser.add_argument("--allow-source-only", action="store_true")
    install_parser = sub.add_parser("install", help="Verify and atomically install into a content-addressed cache")
    install_parser.add_argument("--archive", type=Path, required=True)
    install_parser.add_argument("--sha256", required=True)
    install_parser.add_argument("--into", type=Path, required=True)
    install_parser.add_argument("--allow-source-only", action="store_true")
    args = parser.parse_args()
    try:
        if args.command == "build":
            if args.jobs < 1:
                raise PackageError("--jobs must be positive")
            snapshot = GitSnapshot(args.repo, args.revision)
            print(f"Packaging {snapshot.revision}: {', '.join(snapshot.libraries)}",
                  file=sys.stderr, flush=True)
            result = build(snapshot, args.out_dir, source_only=args.source_only,
                           jobs=args.jobs, dependency_cache=args.dependency_cache,
                           offline_bundle=args.offline_bundle)
        elif args.command == "verify":
            if args.directory and not args.archive and not args.build_archive:
                result = verify_directory(args.directory, args.manifest_sha256)
                result = {k: result[k] for k in ("source_revision", "libraries", "qualification")}
            elif args.archive and args.sha256 and not args.directory and not args.build_archive:
                manifest, _ = read_archive(args.archive, args.sha256,
                                           allow_source_only=args.allow_source_only)
                result = {"source_revision": manifest["source_revision"],
                          "libraries": manifest["libraries"], "qualification": manifest["qualification"]}
            elif args.build_archive and args.sha256 and not args.directory and not args.archive:
                result = verify_build_archive(args.build_archive, args.sha256)
            else:
                raise PackageError("Use --directory OR --archive/--build-archive with --sha256")
        elif args.command == "install":
            result = install(args.archive, args.sha256, args.into,
                             allow_source_only=args.allow_source_only)
    except (PackageError, OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError,
            tarfile.TarError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    print(canonical(result).decode(), end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
