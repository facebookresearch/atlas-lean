"""Public-reference gate tests, using synthetic references only."""

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_public_references as gate


def private_ref(prefix="D"):
    return prefix + "123456789"


class Patterns(unittest.TestCase):
    def test_reference_families(self):
        for prefix in "DTPSNL":
            with self.subTest(prefix=prefix):
                self.assertTrue(gate.scan(private_ref(prefix), "text"))

    def test_public_references_and_identifiers(self):
        text = (
            "RFC 9113, arXiv:2601.01234, DOI 10.1000/xyz; PR #4321; D P T P123"
        )
        self.assertEqual(gate.scan(text, "text"), [])
        self.assertEqual(
            gate.scan("type_" + private_ref() + "_suffix", "text"), []
        )

    def test_private_hosts_paths_and_session(self):
        samples = [
            "https://example." + "internalmeta" + ".com/a/123",
            "https://" + "fburl" + ".com/example",
            "devvm" + "12345.example.com",
            "/".join(["", "home", "example", "private", "file.txt"]),
            "/".join(["", "tmp", "example", "lanes", "result.txt"]),
            "session_id: "
            + "-".join(("01234567", "89ab", "cdef", "0123", "456789abcdef")),
            "F" + "10.EXAMPLE.LEAF",
            "ABC-" + "U01.T02",
            "XYZ-" + "01.L02",
        ]
        for text in samples:
            with self.subTest(text=text):
                self.assertTrue(gate.scan(text, "text"))

    def test_short_reference_boundary_and_runner_path(self):
        for prefix in "DTP":
            self.assertTrue(gate.scan(prefix + "12345", "text"))
            self.assertEqual(gate.scan(prefix + "1234", "text"), [])
        self.assertEqual(
            gate.scan("/".join(["", "home", "runner", "work"]), "text"), []
        )
        self.assertTrue(gate.scan("fbcode" + "/example/source.py", "text"))

    def test_signature_headers_are_public_content(self):
        raw = (
            "author Example <author@example.com>\n"
            "committer Example <author@example.com>\n"
            "gpgsig "
            + private_ref()
            + "\n "
            + private_ref("P")
            + "\n\nOrdinary message\n"
        ).encode()
        self.assertEqual(len(gate.scan_commit(raw, "a" * 40)), 2)

    def test_mergetag_signature_markers_are_not_control(self):
        for ending in (" -----END PGP SIGNATURE-----\n", ""):
            with self.subTest(ending=ending):
                raw = (
                    "mergetag object "
                    + "a" * 40
                    + "\n tagger "
                    + private_ref("T")
                    + " <author@example.com>\n \n"
                    + " -----BEGIN PGP SIGNATURE-----\n "
                    + private_ref()
                    + "\n"
                    + ending
                    + "author "
                    + private_ref("P")
                    + " <author@example.com>\n\nOrdinary message\n"
                ).encode()
                self.assertEqual(len(gate.scan_commit(raw, "a" * 40)), 3)

    def test_mergetag_crlf_signature_markers_are_not_control(self):
        raw = (
            "mergetag object "
            + "a" * 40
            + "\n \n -----BEGIN PGP SIGNATURE-----\r\n "
            + private_ref()
            + "\r\n -----END PGP SIGNATURE-----\r\n"
            + "author "
            + private_ref("T")
            + " <author@example.com>\n\nOrdinary message\n"
        ).encode()
        self.assertEqual(len(gate.scan_commit(raw, "a" * 40)), 2)

    def test_mergetag_signature_marker_in_text_is_not_control(self):
        for prefix in ("mergetag ", " tagger ", " tag "):
            with self.subTest(prefix=prefix):
                raw = (
                    "mergetag object "
                    + "a" * 40
                    + "\n"
                    + prefix
                    + "-----BEGIN PGP SIGNATURE----- "
                    + private_ref()
                    + "\n\nOrdinary message\n"
                ).encode()
                self.assertEqual(len(gate.scan_commit(raw, "a" * 40)), 1)

    def test_line_number_work_is_linear(self):
        class CountedText(str):
            visited = 0

            def count(self, substring, start=0, end=None):
                end = len(self) if end is None else end
                self.visited += end - start
                return super().count(substring, start, end)

        text = CountedText((private_ref() + "\n") * 50)
        findings = gate.scan(text, "fixture")
        self.assertEqual([f["line"] for f in findings], list(range(1, 51)))
        self.assertLessEqual(text.visited, len(text))

    def test_report_budget_and_location_bound(self):
        with patch.object(gate, "MAX_FINDINGS", 2, create=True):
            for count in (0, 2, 3):
                with self.subTest(count=count):
                    findings = gate.scan(
                        (private_ref() + "\n") * count, "safe/" * 1000
                    )
                    self.assertEqual(len(findings), min(count, 2))
                    self.assertEqual(findings.truncated, count > 2)
                    self.assertTrue(
                        all(len(f["location"]) <= 240 for f in findings)
                    )

    def test_domain_like_prefixes_and_whole_location_redaction(self):
        prefix = "a." * 2000
        self.assertEqual(gate.scan(prefix, "fixture"), [])
        host = prefix + "internalmeta" + ".com"
        findings = gate.scan(host, host)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["location"], "[redacted]")

    def test_reports_never_echo_matches_or_unsafe_locations(self):
        secret = private_ref()
        findings = gate.scan("first\n" + secret, secret + ".md")
        self.assertEqual(findings[0]["line"], 2)
        self.assertNotIn(secret, json.dumps(findings))


class Repository(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="public-check-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.run_git("init", "-q")
        self.run_git("config", "user.name", "Example Author")
        self.run_git("config", "user.email", "author@example.com")
        self.run_git("config", "commit.gpgsign", "false")
        self.commit("Initial tree")
        self.base = self.head()

    def run_git(self, *args):
        return (
            subprocess.check_output(
                ["git", "-C", str(self.root), *args],
                stderr=subprocess.DEVNULL,
                env={
                    **os.environ,
                    "GIT_CONFIG_NOSYSTEM": "1",
                    "GIT_CONFIG_GLOBAL": os.devnull,
                },
            )
            .decode()
            .strip()
        )

    def head(self):
        return self.run_git("rev-parse", "HEAD")

    def commit(self, message):
        self.run_git("add", "--all")
        self.run_git("commit", "-q", "--allow-empty", "-m", message)

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def check(self, metadata=None):
        return gate.check_range(self.root, self.base, self.head(), metadata)

    def test_real_clean_range(self):
        self.write("notes.md", "See RFC 9113 and PR #12.\n")
        self.commit("Add reference")
        result = self.check(
            {"title": "Public change", "body": "Public evidence"}
        )
        self.assertEqual((result["commits"], result["files"]), (1, 1))
        self.assertEqual(result["findings"], [])

    def test_full_ancestor_message_not_only_tip_subject(self):
        self.commit(
            "A clean subject\n\nPrivate provenance: " + private_ref("T")
        )
        self.commit("Another clean subject")
        result = self.check()
        self.assertEqual(result["commits"], 2)
        self.assertTrue(result["findings"])
        self.assertTrue(result["findings"][0]["location"].startswith("commit "))

    def test_intermediate_file_versions_cannot_be_hidden_at_tip(self):
        self.write("notes.md", private_ref())
        self.commit("Add notes")
        self.write("notes.md", "Clean final text")
        self.commit("Revise notes")
        self.write("removed.md", private_ref("P"))
        self.commit("Add temporary notes")
        (self.root / "removed.md").unlink()
        self.commit("Remove temporary notes")
        result = self.check()
        self.assertEqual((result["commits"], result["files"]), (4, 2))
        self.assertEqual(result["blobs"], 3)
        self.assertEqual(len(result["findings"]), 2)

    def test_commit_identity_headers_are_public_content(self):
        self.run_git(
            "config", "user.email", "author@" + "devvm" + "12345.example.com"
        )
        self.commit("Ordinary change")
        self.assertEqual(len(self.check()["findings"]), 2)

    def test_signature_markers_in_identities_are_not_control(self):
        marker = "-----BEGIN PGP SIGNATURE-----"
        for name in (
            private_ref() + " " + marker,
            marker + " " + private_ref(),
        ):
            with self.subTest(name=name):
                self.base = self.head()
                self.run_git("config", "user.name", name)
                self.commit("Ordinary change")
                self.assertEqual(len(self.check()["findings"]), 2)

    def test_carriage_return_in_identity_is_not_a_header_break(self):
        self.run_git("config", "user.name", "Example\r" + private_ref())
        self.commit("Ordinary change")
        self.run_git("fsck", "--strict")
        self.assertIn(
            b"\r", gate.git(self.root, "cat-file", "commit", self.head())
        )
        self.assertEqual(len(self.check()["findings"]), 2)

    def test_signature_shaped_headers_cannot_hide_references(self):
        self.write("notes.md", "Public notes\n")
        self.commit("Side change")
        side = self.head()
        tree = self.run_git("rev-parse", "HEAD^{tree}")
        identity = "Example <author@example.com> 1700000000 +0000"
        for field in ("mergetag", "gpgsig", "gpgsig-sha256", "x-provenance"):
            for ending in ("", "\n-----END PGP SIGNATURE-----"):
                with self.subTest(field=field, closed=bool(ending)):
                    value = (
                        "-----BEGIN PGP SIGNATURE-----\n"
                        + private_ref()
                        + ending
                    )
                    if field == "mergetag":
                        value = (
                            f"object {side}\ntype commit\ntag release\n"
                            f"tagger {identity}\n\nNotes\n{value}"
                        )
                    raw = (
                        f"tree {tree}\nparent {self.base}\nparent {side}\n"
                        f"author {identity}\ncommitter {identity}\n"
                        + field
                        + " "
                        + value.replace("\n", "\n ")
                        + "\n\nMerge release\n"
                    ).encode()
                    sha = (
                        gate.git(
                            self.root,
                            "hash-object",
                            "-t",
                            "commit",
                            "-w",
                            "--stdin",
                            input_data=raw,
                        )
                        .decode()
                        .strip()
                    )
                    self.run_git("update-ref", "HEAD", sha)
                    self.run_git("fsck", "--strict")
                    self.assertEqual(len(self.check()["findings"]), 1)

    def test_merge_side_history_is_scanned(self):
        original = self.run_git("branch", "--show-current")
        self.run_git("checkout", "-q", "-b", "side")
        self.write("notes.md", private_ref())
        self.commit("Add side notes")
        self.write("notes.md", "Clean final text")
        self.commit("Revise side notes")
        self.run_git("checkout", "-q", original)
        self.run_git("merge", "-q", "--no-ff", "side", "-m", "Merge notes")
        self.assertEqual(len(self.check()["findings"]), 1)

    def test_merge_from_base_does_not_reintroduce_base_files(self):
        original = self.run_git("branch", "--show-current")
        self.run_git("checkout", "-q", "-b", "topic")
        self.write("topic.md", "Topic text")
        self.commit("Add topic")
        self.run_git("checkout", "-q", original)
        self.write("legacy.md", private_ref())
        self.commit("Add base file")
        self.base = self.head()
        self.run_git("checkout", "-q", "topic")
        self.run_git("merge", "-q", "--no-ff", original, "-m", "Merge base")
        self.commit("Continue topic")
        result = self.check()
        self.assertEqual(result["findings"], [])
        self.assertEqual(result["blobs"], 1)

    def test_copying_a_base_blob_still_checks_the_new_filename(self):
        self.write("legacy.md", private_ref())
        self.commit("Add base file")
        self.base = self.head()
        self.write(private_ref("T") + ".md", private_ref())
        self.commit("Copy notes")
        result = self.check()
        self.assertEqual(len(result["findings"]), 1)
        self.assertEqual(result["blobs"], 0)

    def test_base_advance_after_a_merge_does_not_reintroduce_old_content(self):
        original = self.run_git("branch", "--show-current")
        self.run_git("checkout", "-q", "-b", "topic")
        self.write("topic.md", "Topic text")
        self.commit("Add topic")
        self.run_git("checkout", "-q", original)
        self.write("old.dat", private_ref())
        self.commit("Add base file")
        self.run_git("checkout", "-q", "topic")
        self.run_git("merge", "-q", "--no-ff", original, "-m", "Merge base")
        self.run_git("checkout", "-q", original)
        (self.root / "old.dat").unlink()
        self.commit("Remove old base file")
        self.base = self.head()
        self.run_git("checkout", "-q", "topic")
        result = self.check()
        self.assertEqual(result["findings"], [])
        self.assertEqual(result["blobs"], 1)

    def test_branch_planning_slug_is_checked(self):
        result = self.check({"branch": "example/f" + "17-g05-t02-notes"})
        self.assertEqual(len(result["findings"]), 1)

    def test_branch_tracking_ids_are_case_insensitive(self):
        for prefix in "DTPSNL":
            digits = "12345" if prefix in "DTP" else "123456"
            for letter in (prefix, prefix.lower()):
                for separator in ("-", "_"):
                    branch = separator.join(("topic", letter + digits, "fix"))
                    with self.subTest(branch=branch):
                        result = self.check({"branch": branch})
                        self.assertEqual(len(result["findings"]), 1)
                        self.assertEqual(
                            result["findings"][0]["rule"], "internal-reference"
                        )

    def test_branch_normalization_does_not_change_other_text(self):
        for prefix in "dtpsnl":
            text = prefix + "123456789"
            self.assertEqual(gate.scan(text, "file"), [])
            self.assertEqual(
                self.check({"title": text, "body": text})["findings"], []
            )
        for branch in (
            "d" + "1234-fix",
            "s" + "12345-fix",
            "modeld" + "12345x",
        ):
            self.assertEqual(self.check({"branch": branch})["findings"], [])

    def test_full_file_not_only_added_lines(self):
        self.write("notes.md", private_ref("P") + "\nold\n")
        self.commit("Add old file")
        self.base = self.head()
        self.write("notes.md", private_ref("P") + "\nnew\n")
        self.commit("Update final line")
        self.assertTrue(self.check()["findings"])

    def test_deleted_files_do_not_block_removal(self):
        self.write("notes.md", private_ref())
        self.commit("Add old file")
        self.base = self.head()
        (self.root / "notes.md").unlink()
        self.commit("Remove old file")
        result = self.check()
        self.assertEqual((result["files"], result["findings"]), (0, []))

    def test_filename_and_metadata_are_checked(self):
        self.write(private_ref() + ".md", "Ordinary contents")
        self.commit("Add file")
        result = self.check(
            {"title": private_ref("T"), "branch": private_ref("P")}
        )
        self.assertEqual(len(result["findings"]), 3)

    def test_symlink_is_read_as_data_not_followed(self):
        (self.root / "link").symlink_to(private_ref() + ".txt")
        self.commit("Add link")
        self.assertTrue(self.check()["findings"])

    def test_untrusted_filename_is_not_a_pathspec(self):
        self.write("[abc].md", "Ordinary text")
        self.write("a.md", private_ref())
        self.commit("Add fixtures")
        self.base = self.head()
        self.write("[abc].md", "New ordinary text")
        self.commit("Update literal bracket filename")
        self.assertEqual(self.check()["findings"], [])

    def test_complete_range_beyond_api_commit_cap(self):
        for _ in range(251):
            self.commit("Ordinary commit")
        result = self.check()
        self.assertEqual(result["commits"], 251)
        self.assertEqual(result["findings"], [])

    def test_missing_object_and_invalid_revision_fail_closed(self):
        for head in ("HEAD", "0" * 40):
            with self.subTest(head=head), self.assertRaises(
                gate.IncompleteScan
            ):
                gate.check_range(self.root, self.base, head)

    def test_size_bound_is_not_a_silent_skip(self):
        self.write("notes.md", "Large file")
        self.commit("Add file")
        with patch.object(gate, "MAX_BLOB_BYTES", 2):
            with self.assertRaises(gate.IncompleteScan):
                self.check()

    def test_submodule_pointer_is_not_complete_content(self):
        self.run_git(
            "update-index",
            "--add",
            "--cacheinfo",
            "160000," + self.base + ",module",
        )
        self.run_git("commit", "-q", "-m", "Add external module")
        with self.assertRaises(gate.IncompleteScan):
            self.check()

    def test_lfs_pointer_is_not_full_file_coverage(self):
        self.write("large.dat", "version https://git-lfs.github.com/spec/v1\n")
        self.commit("Add external content pointer")
        with self.assertRaises(gate.IncompleteScan):
            self.check()

    def test_lfs_pointer_variants_are_not_full_coverage(self):
        for version in (
            "https://git-lfs.github.com/spec/v1",
            "https://hawser.github.com/spec/v1",
            "http://git-media.io/v/2",
        ):
            for ending in ("\n", "\r\n"):
                for prefix in ("", "\n", "\t", "\u00a0"):
                    with self.subTest(
                        version=version, ending=ending, prefix=prefix
                    ):
                        self.base = self.head()
                        self.write(
                            "large.dat",
                            prefix
                            + ending.join(
                                (
                                    "version " + version,
                                    "oid sha256:" + "0" * 64,
                                    "size 1",
                                    "",
                                )
                            ),
                        )
                        self.commit("Add external content pointer")
                        with self.assertRaises(gate.IncompleteScan):
                            self.check()

    def test_finding_budget_is_shared_across_inputs(self):
        self.run_git("config", "user.name", private_ref())
        self.write(private_ref("P") + ".txt", private_ref())
        self.write("second.txt", private_ref("P"))
        self.commit("A change with " + private_ref("T"))
        with patch.object(gate, "MAX_FINDINGS", 2, create=True):
            result = self.check({"title": private_ref()})
        self.assertEqual(len(result["findings"]), 2)
        self.assertTrue(result["findings_truncated"])

    def test_reporting_limit_does_not_skip_input_validation(self):
        self.write(private_ref() + ".txt", private_ref())
        self.write("large.dat", "version https://git-lfs.github.com/spec/v1\n")
        self.commit("Add inputs")
        with patch.object(gate, "MAX_FINDINGS", 1, create=True):
            with self.assertRaises(gate.IncompleteScan):
                self.check()

    def test_truncated_empty_report_still_fails(self):
        self.write("notes.md", private_ref())
        self.commit("Add notes")
        out = io.StringIO()
        with patch.object(
            gate, "MAX_FINDINGS", 0, create=True
        ), contextlib.redirect_stdout(out):
            result = gate.main(
                [
                    "--repo-root",
                    str(self.root),
                    "--base",
                    self.base,
                    "--head",
                    self.head(),
                ]
            )
        self.assertEqual(result, 1)
        report = json.loads(out.getvalue())
        self.assertEqual(report["findings"], [])
        self.assertTrue(report["findings_truncated"])

    def test_exit_codes_and_no_secret_in_output(self):
        self.write("notes.md", private_ref())
        self.commit("Add file")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            status = gate.main(
                [
                    "--repo-root",
                    str(self.root),
                    "--base",
                    self.base,
                    "--head",
                    self.head(),
                ]
            )
        self.assertEqual(status, 1)
        self.assertNotIn(private_ref(), out.getvalue())
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(
                gate.main(["--base", "not-a-hash", "--head", self.head()]), 2
            )


class RemoteSnapshot(unittest.TestCase):
    def test_old_event_head_is_rejected(self):
        snapshot = {
            "base": {"sha": "a" * 40},
            "head": {"sha": "b" * 40, "ref": "topic"},
            "title": "Title",
            "body": "",
            "commits": 1,
        }
        with patch.object(gate, "get_pr", return_value=snapshot), patch.object(
            gate, "git"
        ) as reader:
            with self.assertRaises(gate.IncompleteScan):
                gate.check_pr(
                    Path.cwd(), "example/repository", 1, "unused", "c" * 40
                )
            reader.assert_not_called()

    def test_changed_metadata_fails_closed(self):
        snapshot = {
            "base": {"sha": "a" * 40},
            "head": {"sha": "b" * 40, "ref": "topic"},
            "title": "Title",
            "body": "Body",
            "commits": 1,
        }
        changed = {**snapshot, "body": private_ref()}
        with patch.object(
            gate, "get_pr", side_effect=[snapshot, changed]
        ), patch.object(
            gate, "git", return_value=("b" * 40 + "\n").encode()
        ), patch.object(
            gate, "check_range", return_value={"commits": 1}
        ):
            with self.assertRaises(gate.IncompleteScan):
                gate.check_pr(Path.cwd(), "example/repository", 1, "unused")

    def test_commit_count_mismatch_is_not_success(self):
        snapshot = {
            "base": {"sha": "a" * 40},
            "head": {"sha": "b" * 40, "ref": "topic"},
            "title": "Title",
            "body": "",
            "commits": 870,
        }
        with patch.object(gate, "get_pr", return_value=snapshot), patch.object(
            gate, "git", return_value=("b" * 40 + "\n").encode()
        ), patch.object(gate, "check_range", return_value={"commits": 250}):
            with self.assertRaises(gate.IncompleteScan):
                gate.check_pr(Path.cwd(), "example/repository", 1, "unused")

    def test_head_changed_before_scan(self):
        snapshot = {
            "base": {"sha": "a" * 40},
            "head": {"sha": "b" * 40, "ref": "topic"},
            "title": "Title",
            "body": "",
            "commits": 1,
        }
        with patch.object(gate, "get_pr", return_value=snapshot), patch.object(
            gate, "git", return_value=("c" * 40 + "\n").encode()
        ):
            with self.assertRaises(gate.IncompleteScan):
                gate.check_pr(Path.cwd(), "example/repository", 1, "unused")


if __name__ == "__main__":
    unittest.main()
