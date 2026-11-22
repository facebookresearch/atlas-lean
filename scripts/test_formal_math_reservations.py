#!/usr/bin/env python3
"""Reservation admission/publication regressions; local git fixtures, no network or Lean."""
import json
import os
from pathlib import Path
import unittest

import check_formal_math_sync as c
import sync_formal_math as s
import test_formal_math_sync as t

PATH = "MathlibExt/Reserved.lean"
BODY = "module\n\ndef reservedValue : Nat := 97\n"
PIN = "b" * 40


class ReservationGuardTest(unittest.TestCase):
    setUp = t.BaseGuardTest.setUp
    tearDown = t.BaseGuardTest.tearDown
    commit = t.BaseGuardTest.commit
    save = t.BaseGuardTest.save
    run_check = t.BaseGuardTest.run_check
    event = t.BaseGuardTest.event
    labeled_pr = t.BaseGuardTest.labeled_pr

    def reservation(self):
        return {"path": PATH, "disposition": "reserved", "upstream_commit": PIN,
                "upstream_sha256": c.sha256(BODY)}

    def enroll(self, labeled=True):
        self.manifest["upstream"]["commit"] = PIN
        self.manifest["rows"].append(self.reservation())
        self.save()
        self.commit("reserve source for a later contribution")
        self.labeled_pr(*(["formal-math-sync"] if labeled else []))
        return self.run_check()

    def row(self):
        return next(r for r in self.manifest["rows"] if r["path"] == PATH)

    def publish(self, disposition="identical", body=BODY):
        text = c.META + "\n" + body
        row = self.row()
        row.update(disposition=disposition, published_sha256=c.sha256(text))
        if disposition == "attributed":
            text = c.META + "\n" + t.NOTICE + "\n" + body
            row.update(notice=t.NOTICE, published_sha256=c.sha256(text))
        if disposition == "diverged":
            row.update(rationale="Adapt this module's mathematical documentation", backport="not-needed")
        t.write(self.root, PATH, text)
        self.save()
        self.commit("publish the reserved contribution")
        return self.run_check()

    def assert_blocked(self, expected):
        code, output = self.run_check()
        self.assertEqual(code, 1, output)
        self.assertIn(expected, output)

    def test_labeled_sync_enrolls_absent_source(self):
        code, output = self.enroll()
        self.assertEqual(code, 0, output)
        self.assertFalse((self.root / PATH).exists())
        self.assertNotIn("published_sha256", self.row())

    def test_unlabeled_sync_cannot_enroll(self):
        code, output = self.enroll(labeled=False)
        self.assertEqual(code, 1)
        self.assertIn("without the 'formal-math-sync' label", output)

    def test_same_pin_cannot_enroll_even_with_sync_label(self):
        row = self.reservation()
        row["upstream_commit"] = self.manifest["upstream"]["commit"]
        self.manifest["rows"].append(row)
        self.save()
        self.commit("try to enroll without a sync")
        self.labeled_pr("formal-math-sync")
        self.assert_blocked("new reserved row while the upstream pin is unchanged")

    def test_enrollment_commit_must_be_new_sync_pin(self):
        self.enroll()
        self.row()["upstream_commit"] = "c" * 40
        self.save()
        self.commit("forge reservation snapshot")
        self.assert_blocked("reserved source changed upstream_commit")

    def test_new_reservation_with_wrong_sync_commit_fails(self):
        self.manifest["upstream"]["commit"] = PIN
        row = self.reservation()
        row["upstream_commit"] = "c" * 40
        self.manifest["rows"].append(row)
        self.save()
        self.commit("enroll a different snapshot")
        self.labeled_pr("formal-math-sync")
        self.assert_blocked("new reservation must name the sync's upstream commit")

    def test_identical_publication_keeps_source_identity(self):
        self.assertEqual(self.enroll()[0], 0)
        code, output = self.publish()
        self.assertEqual(code, 0, output)
        self.assertEqual(self.row()["upstream_sha256"], c.sha256(BODY))
        self.assertEqual(self.row()["upstream_commit"], PIN)

    def test_attributed_publication_uses_existing_notice_and_body_checks(self):
        self.assertEqual(self.enroll()[0], 0)
        code, output = self.publish("attributed")
        self.assertEqual(code, 0, output)
        t.write(self.root, PATH, c.META + "\n" + BODY)
        self.assert_blocked("synced file changed")

    def test_real_divergence_publication_keeps_source_identity(self):
        self.assertEqual(self.enroll()[0], 0)
        code, output = self.publish("diverged", BODY + "\n/-! Additional mathematical API documentation. -/\n")
        self.assertEqual(code, 0, output)
        self.assertEqual(self.row()["upstream_sha256"], c.sha256(BODY))
        self.row().pop("rationale")
        self.save()
        self.assert_blocked("diverged row has no rationale")

    def test_native_divergence_writer_promotes_without_losing_source_binding(self):
        self.assertEqual(self.enroll()[0], 0)
        t.write(self.root, PATH, c.META + "\n" + BODY + "\n/-! A mathematical API explanation. -/\n")
        code, output = self.run_check(None, "--record-divergence", PATH, "--rationale",
                                      "Document the exact public API", "--backport", "not-needed")
        self.assertEqual(code, 0, output)
        self.manifest = json.loads((self.root / c.MANIFEST).read_text())
        self.assertEqual(self.row()["upstream_commit"], PIN)
        self.assertEqual(self.row()["upstream_sha256"], c.sha256(BODY))
        self.commit("record and publish the documented module")
        code, output = self.run_check()
        self.assertEqual(code, 0, output)

    def test_reservation_requires_valid_commit_and_source_hash(self):
        self.assertEqual(self.enroll()[0], 0)
        for field, malformed in [("upstream_commit", "short"), ("upstream_sha256", "bad")]:
            value = self.row()[field]
            with self.subTest(field=field, case="missing"):
                self.row().pop(field)
                self.save()
                self.assert_blocked("reserved row has no " + field)
            with self.subTest(field=field, case="malformed"):
                self.row()[field] = malformed
                self.save()
                self.assert_blocked(field + " is not")
            self.row()[field] = value

    def test_rehashed_wrong_body_cannot_be_identical_publication(self):
        self.assertEqual(self.enroll()[0], 0)
        code, output = self.publish(body=BODY + "def invented : Nat := 99\n")
        self.assertEqual(code, 1)
        self.assertIn("body after the header does not hash to upstream_sha256", output)

    def test_source_hash_change_cannot_make_wrong_body_pass(self):
        self.assertEqual(self.enroll()[0], 0)
        new_body = BODY + "def invented : Nat := 99\n"
        self.row()["upstream_sha256"] = c.sha256(new_body)
        code, output = self.publish(body=new_body)
        self.assertEqual(code, 1)
        self.assertIn("reserved source changed upstream_sha256", output)

    def test_hash_drift_fails_even_with_another_labeled_repin(self):
        self.assertEqual(self.enroll()[0], 0)
        self.manifest["upstream"]["commit"] = "c" * 40
        self.row()["upstream_sha256"] = "d" * 64
        self.save()
        self.commit("try to rewrite enrollment during another sync")
        self.assert_blocked("reserved source changed upstream_sha256")

    def test_unchanged_reservation_survives_another_real_sync(self):
        self.assertEqual(self.enroll()[0], 0)
        self.manifest["upstream"]["commit"] = "c" * 40
        self.save()
        self.commit("sync unrelated content")
        code, output = self.run_check()
        self.assertEqual(code, 0, output)

    def test_peer_repro_manual_diverged_promotion_at_wrong_pin_is_rejected(self):
        self.assertEqual(self.enroll()[0], 0)
        self.manifest["upstream"]["commit"] = "c" * 40
        code, output = self.publish("diverged", BODY + "\n/-! Mathematical documentation. -/\n")
        self.assertEqual(code, 1, output)
        self.assertIn("reservation publication requires its recorded upstream pin", output)
        self.assertEqual(self.row()["upstream_commit"], PIN)
        self.assertEqual(self.row()["upstream_sha256"], c.sha256(BODY))

    def test_peer_repro_alternate_unregistered_meta_body_copy_is_rejected(self):
        self.assertEqual(self.enroll()[0], 0)
        t.write(self.root, "MathlibExt/Alternate.lean", c.META + "\n" + BODY)
        self.commit("copy reserved source under an unenrolled path")
        self.assert_blocked("exact source-body copy of reserved " + PATH)

    def test_alternate_attributed_body_copy_is_rejected(self):
        self.assertEqual(self.enroll()[0], 0)
        t.write(self.root, "MathlibExt/Alternate.lean", c.META + "\n" + t.NOTICE + "\n" + BODY)
        self.commit("copy source with an attribution wrapper")
        self.assert_blocked("exact source-body copy of reserved " + PATH)

    def test_alternate_raw_source_header_copy_is_rejected(self):
        self.assertEqual(self.enroll()[0], 0)
        t.write(self.root, "MathlibExt/Alternate.lean", t.UPSTREAM.replace(t.BODY, BODY))
        self.commit("copy the raw source header and body")
        self.assert_blocked("exact source-body copy of reserved " + PATH)

    def test_alternate_retained_legal_header_copy_is_rejected(self):
        self.manifest["upstream"]["commit"] = PIN
        source = t.THIRD_PARTY + BODY
        row = self.reservation()
        row["upstream_sha256"] = c.sha256(source)
        self.manifest["rows"].append(row)
        self.save()
        self.commit("reserve an exact source with retained copyright")
        self.labeled_pr("formal-math-sync")
        self.assertEqual(self.run_check()[0], 0)
        t.write(self.root, "MathlibExt/Alternate.lean", source)
        self.commit("copy source with its retained legal header")
        self.assert_blocked("exact source-body copy of reserved " + PATH)

    def test_copy_guard_preserves_existing_unregistered_baseline_path(self):
        t.write(self.root, "WantedExt/PreviouslyPublished.lean", c.META + "\n" + BODY)
        self.commit("publish independent baseline content")
        code, output = self.enroll()
        self.assertEqual(code, 0, output)

    def test_copy_guard_preserves_legitimately_registered_new_path(self):
        self.assertEqual(self.enroll()[0], 0)
        alias = "MathlibExt/RegisteredAlias.lean"
        text = c.META + "\n" + BODY
        t.write(self.root, alias, text)
        self.manifest["rows"].append({"path": alias, "disposition": "diverged",
                                      "published_sha256": c.sha256(text), "upstream_commit": PIN,
                                      "upstream_sha256": c.sha256(BODY),
                                      "rationale": "Reviewed copy of the source at a compatibility path",
                                      "backport": "not-needed"})
        self.save()
        self.commit("publish a separately recorded compatibility path")
        code, output = self.run_check()
        self.assertEqual(code, 0, output)

    def test_copy_guard_leaves_unrelated_new_content_unchanged(self):
        self.assertEqual(self.enroll()[0], 0)
        t.write(self.root, "WantedExt/Independent.lean", t.FRESH)
        self.commit("add unrelated original content")
        code, output = self.run_check()
        self.assertEqual(code, 0, output)

    def test_base_reservation_copy_remains_protected_after_its_row_is_promoted(self):
        self.assertEqual(self.enroll()[0], 0)
        # A notice changes the published SHA, so the existing whole-file copy guard alone
        # cannot identify the alternate Meta-header copy.
        self.row().update(disposition="attributed", notice=t.NOTICE,
                          published_sha256=c.sha256(c.META + "\n" + t.NOTICE + "\n" + BODY))
        t.write(self.root, PATH, c.META + "\n" + t.NOTICE + "\n" + BODY)
        t.write(self.root, "MathlibExt/Alternate.lean", c.META + "\n" + BODY)
        self.save()
        self.commit("publish the reserved path with an unregistered alternate copy")
        self.assert_blocked("exact source-body copy of reserved " + PATH)

    def test_published_row_cannot_be_replaced_with_reservation(self):
        self.enroll()
        row = next(r for r in self.manifest["rows"] if r["path"] == "MathlibExt/Identical.lean")
        (self.root / row["path"]).unlink()
        row.clear()
        row.update(path="MathlibExt/Identical.lean", disposition="reserved", upstream_commit=PIN,
                   upstream_sha256=c.sha256(t.BODY))
        self.manifest["upstream"]["commit"] = "c" * 40
        self.save()
        self.commit("hide previously published provenance")
        self.assert_blocked("published provenance cannot become a reservation")

    def test_reservation_cannot_record_publication_or_extra_fields(self):
        self.assertEqual(self.enroll()[0], 0)
        for field, value in [("published_sha256", "d" * 64), ("notice", t.NOTICE), ("future_path", PATH)]:
            with self.subTest(field=field):
                self.row()[field] = value
                self.save()
                self.assert_blocked("reserved row has publication fields or unknown fields")
                self.row().pop(field)

    def test_absent_reservation_cannot_be_retired(self):
        self.assertEqual(self.enroll()[0], 0)
        code, output = self.run_check(None, "--retire", PATH)
        self.assertEqual(code, 1)
        self.assertIn("never been published", output)
        self.row()["disposition"] = "retired"
        self.save()
        self.commit("invent a retirement")
        self.assert_blocked("a reservation may only become identical, attributed or diverged")

    def test_present_file_requires_publication_promotion(self):
        self.assertEqual(self.enroll()[0], 0)
        t.write(self.root, PATH, c.META + "\n" + BODY)
        self.assert_blocked("reserved source, but the path exists")

    def test_existing_unreserved_synced_addition_still_fails(self):
        self.assertEqual(self.enroll()[0], 0)
        t.write(self.root, "MathlibExt/Unenrolled.lean", c.META + "\n" + BODY)
        self.manifest["rows"].append({"path": "MathlibExt/Unenrolled.lean", "disposition": "identical",
                                      "published_sha256": c.sha256(c.META + "\n" + BODY),
                                      "upstream_sha256": c.sha256(BODY)})
        self.save()
        self.commit("try to import an unenrolled source")
        self.assert_blocked("new synced row while the upstream pin is unchanged")

    def test_reserved_row_cannot_disappear(self):
        self.assertEqual(self.enroll()[0], 0)
        self.manifest["rows"] = [r for r in self.manifest["rows"] if r["path"] != PATH]
        self.save()
        self.commit("drop enrollment")
        self.assert_blocked("row removed or renamed")

    def test_enrollment_cannot_hide_a_dropped_existing_row(self):
        self.manifest["rows"] = [r for r in self.manifest["rows"] if r["path"] != "WantedExt/Retired.lean"]
        code, output = self.enroll()
        self.assertEqual(code, 1)
        self.assertIn("WantedExt/Retired.lean: row removed or renamed", output)

    def test_reservation_cannot_be_promoted_to_an_unreviewed_older_version(self):
        self.assertEqual(self.enroll()[0], 0)
        code, output = self.publish("behind")
        self.assertEqual(code, 1)
        self.assertIn("a reservation may only become identical, attributed or diverged", output)

    def test_symlinked_reservation_path_is_rejected(self):
        self.assertEqual(self.enroll()[0], 0)
        os.symlink(self.root / "MathlibExt/Identical.lean", self.root / PATH)
        self.assert_blocked("symlinked path")


class ReservationSyncTest(unittest.TestCase):
    setUp = t.SyncTest.setUp
    tearDown = t.SyncTest.tearDown
    rows = t.SyncTest.rows

    def initialize(self, source=t.UPSTREAM.replace(t.BODY, BODY)):
        code, output = t.quiet(s.main, ["--formal-math", str(self.fm), "--commit", self.first,
                                       "--atlas", str(self.atlas), "--rationales", str(self.rationales)])
        self.assertEqual(code, 0, output)
        t.write(self.fm, PATH, source)
        t.run_git(self.fm, "add", "-A")
        t.run_git(self.fm, "commit", "-qm", "new source snapshot")
        self.source_pin = t.run_git(self.fm, "rev-parse", "HEAD")
        self.paths = self.atlas.parent / "reserve-paths.json"
        self.paths.write_text(json.dumps([PATH]))

    def sync(self, reserve=False):
        args = ["--formal-math", str(self.fm), "--commit", "HEAD", "--atlas", str(self.atlas),
                "--rationales", str(self.rationales)]
        if reserve:
            args += ["--reserve-paths", str(self.paths)]
        return t.quiet(s.main, args)

    def test_source_enrollment_and_same_snapshot_publication_end_to_end(self):
        self.initialize()
        code, output = self.sync(reserve=True)
        self.assertEqual(code, 0, output)
        reserved = self.rows()[PATH]
        self.assertEqual(reserved, {"path": PATH, "disposition": "reserved", "upstream_commit": self.source_pin,
                                    "upstream_sha256": c.sha256(BODY)})
        self.assertIn("Reserved source (not published)", output)
        self.assertEqual(c.check(self.atlas, self.atlas / c.MANIFEST)[0], [])
        self.assertEqual(self.sync()[0], 0)
        self.assertEqual(self.rows()[PATH], reserved)
        t.write(self.atlas, PATH, c.META + "\n" + BODY)
        code, output = self.sync()
        self.assertEqual(code, 0, output)
        self.assertEqual(self.rows()[PATH]["disposition"], "identical")
        self.assertEqual(self.rows()[PATH]["upstream_commit"], reserved["upstream_commit"])
        self.assertEqual(self.rows()[PATH]["upstream_sha256"], reserved["upstream_sha256"])
        self.assertEqual(c.check(self.atlas, self.atlas / c.MANIFEST)[0], [])

    def test_hashes_come_from_git_snapshot_not_dirty_checkout(self):
        self.initialize()
        t.write(self.fm, PATH, t.UPSTREAM.replace(t.BODY, "def dirty : Nat := 1\n"))
        code, output = self.sync(reserve=True)
        self.assertEqual(code, 0, output)
        self.assertEqual(self.rows()[PATH]["upstream_sha256"], c.sha256(BODY))

    def test_third_party_header_is_hash_bound_and_retained(self):
        source = t.THIRD_PARTY + BODY
        self.initialize(source)
        self.assertEqual(self.sync(reserve=True)[0], 0)
        self.assertEqual(self.rows()[PATH]["upstream_sha256"], c.sha256(source))
        t.write(self.atlas, PATH, source)
        code, output = self.sync()
        self.assertEqual(code, 0, output)
        self.assertEqual(self.rows()[PATH]["header"], "upstream")
        self.assertEqual(c.check(self.atlas, self.atlas / c.MANIFEST)[0], [])

    def test_unchanged_pin_cannot_enroll_new_source(self):
        self.initialize()
        self.assertEqual(self.sync()[0], 0)
        with self.assertRaisesRegex(SystemExit, "without moving the upstream pin"):
            self.sync(reserve=True)
        self.assertNotIn(PATH, self.rows())

    def test_reservation_source_must_exist_as_regular_lean_blob(self):
        self.initialize()
        self.paths.write_text(json.dumps(["MathlibExt/Absent.lean"]))
        with self.assertRaisesRegex(SystemExit, "no regular Lean source file"):
            self.sync(reserve=True)
        self.assertNotIn(PATH, self.rows())

    def test_present_publication_cannot_be_reserved(self):
        self.initialize()
        t.write(self.atlas, PATH, c.META + "\n" + BODY)
        with self.assertRaisesRegex(SystemExit, "already present"):
            self.sync(reserve=True)

    def test_hash_input_instead_of_path_list_is_rejected(self):
        self.initialize()
        self.paths.write_text(json.dumps({PATH: "d" * 64}))
        with self.assertRaisesRegex(SystemExit, "JSON list of unique source paths"):
            self.sync(reserve=True)

    def test_duplicate_and_escaping_reservation_inputs_fail_closed(self):
        self.initialize()
        self.paths.write_text(json.dumps([PATH, PATH]))
        with self.assertRaisesRegex(SystemExit, "JSON list of unique source paths"):
            self.sync(reserve=True)
        self.paths.write_text(json.dumps(["MathlibExt/../outside.lean"]))
        with self.assertRaisesRegex(SystemExit, "escaping path"):
            self.sync(reserve=True)

    def test_reserved_publication_must_use_bound_snapshot(self):
        self.initialize()
        self.assertEqual(self.sync(reserve=True)[0], 0)
        t.write(self.fm, PATH, t.UPSTREAM.replace(t.BODY, BODY + "def newer : Nat := 3\n"))
        t.run_git(self.fm, "add", "-A")
        t.run_git(self.fm, "commit", "-qm", "later source change")
        t.write(self.atlas, PATH, c.META + "\n" + BODY)
        with self.assertRaisesRegex(SystemExit, "exact reserved source snapshot"):
            self.sync()


if __name__ == "__main__":
    unittest.main()
