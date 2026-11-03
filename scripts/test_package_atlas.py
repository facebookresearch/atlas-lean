"""Release transport regressions. Pure Python fixtures; no network or Lean."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import tomllib
import unittest
from unittest.mock import patch

import package_atlas as p


CONFIG = """name = "atlas"
version = "0.1.0"
defaultTargets = ["MathlibExt"]
testDriver = "MathlibExtTest"
[[lean_lib]]
name = "MathlibExt"
globs = ["MathlibExt.+"]
[[lean_lib]]
name = "MathlibExtTest"
globs = ["MathlibExtTest.+"]
[[lean_lib]]
name = "CSLibExt"
globs = ["CSLibExt.+"]
[[lean_lib]]
name = "CSLibExtTest"
globs = ["CSLibExtTest.+"]
[[lean_lib]]
name = "WantedExt"
globs = ["WantedExt.+"]
"""


class MemorySnapshot:
    revision = "a" * 40

    def __init__(self):
        self.data = {
            "lakefile.toml": CONFIG.encode(),
            "lean-toolchain": b"leanprover/lean4:v4.35.0\n",
            "lake-manifest.json": p.canonical({"name": "atlas", "packages": [],
                                              "packagesDir": ".lake/packages", "version": "1.3.0"}),
            "LICENSE": b"Fixture license\n",
            "MathlibExt/Basic.lean": b"/- Original header -/\nmodule\npublic def answer : Nat := 42\n",
            "MathlibExtTest/Basic.lean": b"import MathlibExt.Basic\nexample : answer = 42 := rfl\n",
            "CSLibExt/Basic.lean": b"import MathlibExt.Basic\n",
            "CSLibExtTest/Basic.lean": b"import CSLibExt.Basic\n",
            "WantedExt/Basic.lean": b"module\npublic def wish : Prop := True\n",
        }
        self.refresh()

    def refresh(self):
        self.config = tomllib.loads(self.data["lakefile.toml"].decode())
        self.libraries = p.libraries_of(self.config)
        self.files = {name: {"mode": "100644", "bytes": len(data),
                             "git_blob": hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()}
                      for name, data in self.data.items()}

    def read(self, path):
        return self.data[path]

    def export(self, destination):
        for name, data in self.data.items():
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        for library in self.libraries:
            (destination / library).mkdir(exist_ok=True)


class Transport(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.snapshot = MemorySnapshot()
        self.result = p.build(self.snapshot, self.root / "release", source_only=True)

    def tearDown(self):
        self.temporary.cleanup()

    def install(self):
        return p.install(self.result["archive"], self.result["archive_sha256"],
                         self.root / "cache", allow_source_only=True)

    def qualified_result(self, name, *, offline_bundle=False):
        def qualify(snapshot, package, jobs, dependency_cache, log):
            artifact = package / ".lake/build/lib/lean/MathlibExt/Basic.olean"
            artifact.parent.mkdir(parents=True)
            artifact.write_bytes(b"fixture artifact")
            log.write_text("fixture qualification passed\n")
            return {"status": "passed"}

        def lake_pack(command, package, env, log):
            self.assertEqual(command, ["lake", "pack"])
            with tarfile.open(package / ".lake/atlas-fixture.tar.gz", "w:gz") as archive:
                archive.add(package / ".lake/build", arcname="build")

        with patch.object(p, "qualify", side_effect=qualify) as qualified, \
                patch.object(p, "run_logged", side_effect=lake_pack) as native, \
                patch.object(p, "pack", wraps=p.pack) as offline:
            result = p.build(self.snapshot, self.root / name, offline_bundle=offline_bundle)
        return result, qualified, native, offline

    def test_qualified_build_defaults_to_one_native_archive_and_32_workers(self):
        result, qualified, native, offline = self.qualified_result("native-only")
        qualified.assert_called_once()
        self.assertEqual(qualified.call_args.args[2], 32)
        native.assert_called_once()
        offline.assert_not_called()
        self.assertNotIn("archive", result)
        self.assertEqual(len(list((self.root / "native-only").rglob("*.tar.gz"))), 1)
        self.assertEqual(p.digest_file(result["build_manifest"]), result["manifest_sha256"])
        p.validate_manifest(json.loads(Path(result["build_manifest"]).read_text()))

    def test_offline_bundle_is_opt_in_and_uses_the_same_qualified_build(self):
        result, qualified, native, offline = self.qualified_result("both", offline_bundle=True)
        qualified.assert_called_once()
        native.assert_called_once()
        offline.assert_called_once()
        self.assertEqual(len(list((self.root / "both").rglob("*.tar.gz"))), 2)
        manifest, _ = p.read_archive(result["archive"], result["archive_sha256"])
        self.assertEqual(manifest["qualification"]["build_workers"], 32)
        artifact = next(row for row in manifest["files"] if row["kind"] == "artifact")
        self.assertEqual(artifact["sha256"], hashlib.sha256(b"fixture artifact").hexdigest())

    def test_native_build_asset_verification_rejects_tampering(self):
        result, _, _, _ = self.qualified_result("asset-check")
        archive = Path(result["lake_build_archive"])
        expected = result["lake_build_archive_sha256"]
        self.assertTrue(p.verify_build_archive(archive, expected)["verified"])
        with archive.open("ab") as output:
            output.write(b"tampered")
        with self.assertRaisesRegex(p.PackageError, "SHA-256"):
            p.verify_build_archive(archive, expected)

    def test_published_descriptor_uses_portable_asset_names(self):
        result, _, _, _ = self.qualified_result("portable", offline_bundle=True)
        descriptor = Path(result["build_manifest"].removesuffix(".manifest.json") + ".json")
        published = json.loads(descriptor.read_text())
        for field in ("build_manifest", "lake_build_archive", "archive"):
            self.assertEqual(published[field], Path(result[field]).name)
            self.assertTrue(Path(result[field]).is_absolute())
        self.assertEqual(published["manifest_sha256"], result["manifest_sha256"])

    def test_all_libraries_and_both_test_suites_are_preserved(self):
        manifest, _ = p.read_archive(self.result["archive"], self.result["archive_sha256"],
                                     allow_source_only=True)
        self.assertEqual(manifest["libraries"], self.snapshot.libraries)
        paths = {r["path"] for r in manifest["files"]}
        self.assertIn("MathlibExtTest/Basic.lean", paths)
        self.assertIn("CSLibExtTest/Basic.lean", paths)
        self.assertIn("WantedExt/Basic.lean", paths)
        self.assertEqual(manifest["qualification"]["status"], "not_run")

    def test_source_archive_is_reproducible(self):
        second = p.build(self.snapshot, self.root / "second", source_only=True)
        self.assertEqual(self.result["archive_sha256"], second["archive_sha256"])

    def test_unbuilt_source_cannot_install_as_a_qualified_release(self):
        with self.assertRaisesRegex(p.PackageError, "not qualified"):
            p.install(self.result["archive"], self.result["archive_sha256"], self.root / "strict")
        self.assertFalse((self.root / "strict" / self.result["archive_sha256"]).exists())

    def test_checksum_rejection_precedes_extraction(self):
        with self.assertRaisesRegex(p.PackageError, "SHA-256"):
            p.install(self.result["archive"], "0" * 64, self.root / "bad", allow_source_only=True)
        self.assertFalse((self.root / "bad" / ("0" * 64)).exists())

    def test_reinstall_is_idempotent_and_does_not_modify_package(self):
        first = self.install()
        path = Path(first["package_path"])
        before = (path / "MathlibExt/Basic.lean").stat().st_mtime_ns
        second = self.install()
        self.assertEqual(first, second)
        self.assertEqual(before, (path / "MathlibExt/Basic.lean").stat().st_mtime_ns)
        self.assertEqual(first["lock"]["archive_sha256"], self.result["archive_sha256"])

    def test_trusted_lock_catches_manifest_and_source_tampering(self):
        installed = self.install()
        path = Path(installed["package_path"])
        source = path / "MathlibExt/Basic.lean"
        source.chmod(0o644)
        source.write_bytes(source.read_bytes().replace(b"42", b"99"))
        manifest_path = path / p.MANIFEST
        manifest = json.loads(manifest_path.read_text())
        for row in manifest["files"]:
            if row["path"] == "MathlibExt/Basic.lean":
                row["sha256"] = p.digest_file(source)
        manifest["source_manifest_sha256"] = p.sha(p.canonical(
            [r for r in manifest["files"] if r["kind"] == "source"]))
        manifest_path.write_bytes(p.canonical(manifest))
        with self.assertRaisesRegex(p.PackageError, "trusted lock"):
            p.verify_directory(path, installed["lock"]["manifest_sha256"])

    def test_extra_source_and_shadowing_lakefile_are_rejected(self):
        path = Path(self.install()["package_path"])
        extra = path / "MathlibExt/Extra.lean"
        extra.write_text("axiom extra : False\n")
        with self.assertRaisesRegex(p.PackageError, "Unexpected source"):
            p.verify_directory(path)
        extra.unlink()
        (path / "lakefile.lean").write_text("import Lake\n")
        with self.assertRaisesRegex(p.PackageError, "Unexpected top-level"):
            p.verify_directory(path)

    def test_traversal_and_links_are_rejected_even_with_a_matching_archive_digest(self):
        for name, kind in (("../outside", tarfile.REGTYPE),
                           ("atlas/symlink", tarfile.SYMTYPE),
                           ("atlas/hardlink", tarfile.LNKTYPE)):
            with self.subTest(name=name):
                archive = self.root / "hostile.tar.gz"
                with tarfile.open(archive, "w:gz") as tar:
                    info = tarfile.TarInfo(name)
                    info.type = kind
                    info.linkname = "/outside"
                    info.size = 1 if kind == tarfile.REGTYPE else 0
                    tar.addfile(info, io.BytesIO(b"x") if info.size else None)
                with self.assertRaises(p.PackageError):
                    p.install(archive, p.digest_file(archive), self.root / "hostile",
                              allow_source_only=True)
                self.assertFalse((self.root / "outside").exists())

    def test_failed_build_does_not_publish_an_archive(self):
        with patch.object(p, "qualify", side_effect=p.PackageError("fixture compiler failure")):
            with self.assertRaisesRegex(p.PackageError, "compiler failure"):
                p.build(self.snapshot, self.root / "failed")
        self.assertFalse(list((self.root / "failed").glob("*.tar.gz")))

    def test_build_cannot_publish_sources_modified_by_qualification(self):
        def modified(snapshot, package, *args):
            (package / "MathlibExt/Basic.lean").write_text("public def changed : Nat := 99\n")
            return {"status": "passed"}
        with patch.object(p, "qualify", side_effect=modified):
            with self.assertRaisesRegex(p.PackageError, "Source changed during qualification"):
                p.build(self.snapshot, self.root / "modified")
        self.assertFalse(list((self.root / "modified").glob("*.tar.gz")))


    def test_output_cannot_be_overwritten(self):
        with self.assertRaisesRegex(p.PackageError, "already exists"):
            p.build(self.snapshot, self.root / "release", source_only=True)





    def test_glob_cannot_pull_archived_sources_into_a_library(self):
        config = tomllib.loads(CONFIG)
        config["lean_lib"][0]["globs"] = ["v1.+"]
        with self.assertRaisesRegex(p.PackageError, "escapes"):
            p.libraries_of(config)


if __name__ == "__main__":
    unittest.main()
