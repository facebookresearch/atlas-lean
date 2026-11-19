"""Public-reference gate tests, using synthetic references only."""

import contextlib
import gc
import io
import json
import os
from pathlib import Path
import string
import subprocess
import sys
import tempfile
import tracemalloc
import unittest
from unittest.mock import patch

import check_public_references as gate


def private_ref(prefix="D"):
    return prefix + "123456789"


def roadmap_ref(*segments):
    return ".".join(("EXAMPLE", *segments))


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

    def test_dotted_roadmap_labels(self):
        for segments in (
            ("AREA", "TOPIC", "LEAF"),
            ("HW", "DEVICE", "L1"),
            ("G", "TOPIC", "L1"),
        ):
            label = roadmap_ref(*segments)
            with self.subTest(segments=segments):
                findings = gate.scan("First line\n" + label, "text")
                self.assertEqual(len(findings), 1)
                self.assertEqual(
                    findings[0]["rule"], "private-roadmap-reference"
                )
                self.assertEqual(findings[0]["line"], 2)
                self.assertNotIn(label, json.dumps(findings))
        for text in (
            "Nat.Prime.two",
            "Real.pi",
            "e.g.",
            "U.S.A.",
            "v1.2.3",
            "ISO.8601",
            "README.md",
            "A.B.C",
            "COM.EXAMPLE.API",
        ):
            self.assertEqual(gate.scan(text, "text"), [])

    def test_lesson_references_in_text(self):
        for separator in ("/", "_", "-"):
            for leaf in ("s98l97", "s98.l97"):
                reference = "f" + "99" + separator + leaf
                for value in (reference, reference.upper()):
                    findings = gate.scan(
                        "Based on `" + value + "-example`.", "PR body"
                    )
                    self.assertEqual(len(findings), 1)
                    self.assertEqual(
                        findings[0]["rule"], "private-planning-reference"
                    )
        self.assertTrue(gate.scan("S" + "98.L97", "text"))
        for value in (
            "F16 jets",
            "S13 lemma",
            "Section 13.L",
            "s1.l2",
            "sl01",
            "f16-sweep",
            "COM.EXAMPLE.API",
        ):
            self.assertEqual(gate.scan(value, "text"), [])

    def test_windows_personal_workspace_paths(self) -> None:
        for separator in ("\\", "\\\\", "/"):
            for users in ("Users", "users", "USERS"):
                value = (
                    "C:"
                    + separator
                    + separator.join((users, "example", "work", "notes.txt"))
                )
                with self.subTest(separator=separator, users=users):
                    findings = gate.scan("First line\n" + value, value)
                    self.assertEqual(len(findings), 1)
                    self.assertEqual(findings[0]["rule"], "personal-workspace")
                    self.assertEqual(findings[0]["line"], 2)
                    self.assertEqual(findings[0]["location"], "[redacted]")
                    self.assertNotIn(value, json.dumps(findings))
        for value in (
            "C:" + "\\".join(("", "Users", "runner", "work", "repo")),
            "/home/runner/work/repo",
            "Users/example/work/notes.txt",
            "C:" + "\\".join(("", "UsersShared", "example", "notes.txt")),
        ):
            self.assertEqual(gate.scan(value, "text"), [])

    def test_spaced_and_unicode_personal_profiles(self) -> None:
        for name in (
            "Example Person",
            "Example  Person",
            "Example'Profile",
            "Example`Profile",
            "Example\u00a0Profile",
            "Example\u2003Profile",
            "\u00a0Example",
            " Example",
            "Zoë Example",
            "名字",
        ):
            for separator in ("\\", "\\\\", "/"):
                value = (
                    "C:"
                    + separator
                    + separator.join(("Users", name, "work", "notes.txt"))
                )
                with self.subTest(name=name, separator=separator):
                    findings = gate.scan(value, "text")
                    self.assertEqual(len(findings), 1)
                    self.assertEqual(findings[0]["rule"], "personal-workspace")

    def test_personal_profile_directory_is_enough(self) -> None:
        for ending in ("", "'notes.txt", "`notes.txt", "\u00a0notes.txt"):
            value = "C:" + "\\".join(("", "Users", "example", ending))
            with self.subTest(ending=ending):
                self.assertEqual(len(gate.scan(value, "text")), 1)
        for invalid in (
            '"',
            "\n",
            "\r",
            "\t",
            "\x85",
            "\u2028",
            "\u2029",
            "<",
            ">",
            "|",
            ":",
            "*",
            "?",
        ):
            value = "C:" + "\\".join(
                ("", "Users", "Example" + invalid + "Profile", "notes.txt")
            )
            # An invalid character ends the name; the profile before it is
            # still a terminal profile path, reported once on its own line.
            with self.subTest(invalid=invalid):
                findings = gate.scan(value, "text")
                self.assertEqual(len(findings), 1)
                self.assertEqual(findings[0]["line"], 1)
                self.assertEqual(findings[0]["rule"], "personal-workspace")

    def test_terminal_personal_profiles(self) -> None:
        roots = []
        for separator in ("\\", "\\\\", "/"):
            roots.append("C:" + separator + "Users" + separator)
        home, data = "/home/", "/".join(["", "data", "users", ""])
        roots += [home, data, "/" + home + "/", home.replace("/", "\\")]
        names = (
            "Example",
            "Example Person",
            "Example'Profile",
            "Example\u00a0Profile",
            "Zo\u00eb Example",
            "\u540d\u5b57",
            "runnerExample",
            "runner Smith",
            "runneradmin-extra",
        )
        wrappers = (
            ("", ""),
            ('"', '"'),
            ("'", "'"),
            ("`", "`"),
            ("(", ")"),
            ("See ", "."),
            ("See ", " for details"),
            ("", "\n"),
            ("", "\r\nnext"),
            ("", "\tnext"),
            ("", "\x85next"),
            ("", "\u2028next"),
        )
        for root in roots:
            for name in names:
                for before, after in wrappers:
                    text = "First line\n" + before + root + name + after
                    with self.subTest(root=root, name=name, after=after):
                        findings = gate.scan(text, "text")
                        self.assertEqual(len(findings), 1)
                        self.assertEqual(findings[0]["line"], 2)
                        self.assertEqual(
                            findings[0]["rule"], "personal-workspace"
                        )
                        self.assertNotIn(name, json.dumps(findings))

    def test_terminal_ci_prefixed_names_are_reported(self) -> None:
        home = "/home/"
        windows = "C:" + "\\".join(["", "Users", ""])
        names = (
            "runner.Example",
            "runner'Profile",
            "runner`Profile",
            "runneradmin.Example",
            "runner,Example",
            "runner;Example",
            "runner)Example",
            "runner .Example",
            "runneradmin'Example",
        )
        for name in names:
            for text in (
                home + name,
                "'" + home + name + "'",
                '"' + windows + name + '"',
                windows + name + "\n",
                "See " + home + name + " here.",
            ):
                with self.subTest(text=text):
                    findings = gate.scan(text, "text")
                    self.assertEqual(len(findings), 1)
                    self.assertEqual(findings[0]["rule"], "personal-workspace")

    def test_quoted_terminal_profiles_keep_their_punctuation(self):
        roots = (
            "/home/",
            "/".join(["", "data", "users", ""]),
            "C:" + "\\".join(["", "Users", ""]),
            "C:" + "\\\\".join(["", "Users", ""]),
        )
        names = (
            ".Example",
            "!Example",
            ";Example",
            ")Example",
            "runner. Example",
            "runner' Profile",
            "runneradmin, Example",
            " Example",
            # Inside quotes these are whole names, not the exact accounts.
            "runner!",
            "runner'",
            "runneradmin)",
            "runner.",
            "runner ",
            "...",
            ". ",
            ".. ",
        )
        for quote in ('"', "'", "`"):
            for root in roots:
                for name in names:
                    if quote in name:
                        continue
                    text = "Path " + quote + root + name + quote + " here."
                    with self.subTest(text=text):
                        findings = gate.scan(text, "text")
                        self.assertEqual(len(findings), 1)
                        self.assertEqual(
                            findings[0]["rule"], "personal-workspace"
                        )
                # Punctuation after the closing quote stays outside the name.
                for name in ("runner", "runneradmin"):
                    for tail in ("", ".", "!", ",", ")"):
                        text = quote + root + name + quote + tail
                        with self.subTest(text=text):
                            self.assertEqual(gate.scan(text, "text"), [])
                # Empty or blank, "." and "..", and a quote after the root.
                for name in ("", " ", ".", "..", "'Example", "`Example"):
                    text = quote + root + name + quote
                    with self.subTest(text=text):
                        self.assertEqual(gate.scan(text, "text"), [])

    def test_literal_values_use_the_whole_terminal_name(self):
        for root in (
            "docs/home/",
            "/home/",
            "/".join(["", "data", "users", ""]),
            "C:" + "\\".join(["", "Users", ""]),
        ):
            for name in (
                "runner!",
                "runner.",
                "runner. Example",
                "runner' Profile",
                "runneradmin)",
                ". ",
                ".Example",
                "Example",
            ):
                with self.subTest(value=root + name):
                    findings = gate.scan(
                        root + name, "filename", rules=gate.LITERAL_RULES
                    )
                    self.assertEqual(len(findings), 1)
            for name in ("runner", "runneradmin", "", " ", ".", "..", "'x"):
                with self.subTest(value=root + name):
                    self.assertEqual(
                        gate.scan(
                            root + name, "filename", rules=gate.LITERAL_RULES
                        ),
                        [],
                    )
            self.assertEqual(
                gate.scan(root + "runner/x", "f", rules=gate.LITERAL_RULES), []
            )

    def test_quoted_and_literal_names_keep_every_punctuation_mark(self):
        # Only separators, line breaks and the matching quote end a quoted
        # or literal name; Windows-invalid characters are data there.
        roots = ("/home/", "/".join(["", "data", "users", ""]))
        for mark in string.punctuation:
            if mark in "/\\":
                continue
            for core in ("runner", "runneradmin"):
                for name in (core + mark, core + mark + "x"):
                    for root in roots:
                        for quote in ('"', "'", "`"):
                            if quote == mark:
                                continue
                            text = quote + root + name + quote
                            with self.subTest(text=text):
                                self.assertEqual(len(gate.scan(text, "t")), 1)
                        value = "docs" + root + name
                        with self.subTest(value=value):
                            findings = gate.scan(
                                value, "f", rules=gate.LITERAL_RULES
                            )
                            self.assertEqual(len(findings), 1)
                    # The same names before a further path component.
                    nested = "/home/" + name + "/leaf.txt"
                    for quote in ('"', "'", "`"):
                        if quote != mark:
                            text = quote + nested + quote
                            with self.subTest(text=text):
                                self.assertEqual(len(gate.scan(text, "t")), 1)
                    with self.subTest(value="docs" + nested):
                        findings = gate.scan(
                            "docs" + nested, "f", rules=gate.LITERAL_RULES
                        )
                        self.assertEqual(len(findings), 1)
                # The exact account before a further component stays clean.
                for quote in ('"', "'", "`"):
                    text = quote + "/home/" + core + "/x" + mark + quote
                    if quote != mark:
                        with self.subTest(text=text):
                            self.assertEqual(gate.scan(text, "t"), [])
                value = "docs/home/" + core + "/x" + mark
                with self.subTest(value=value):
                    self.assertEqual(
                        gate.scan(value, "f", rules=gate.LITERAL_RULES), []
                    )

    def test_quoted_terminal_and_separator_forms_agree(self):
        # A quote right after the root is a documented text boundary, so
        # names here start with anything except a quote.
        starts = ("", ".", "!", ";", ")", ",", "-", "_", "(")
        cores = ("runner", "runneradmin", "Example", "Zo\u00eb", "\u540d")
        joins = ("", ".", "'", ",", ";", "!", ")", "-", "_", " ", ". ", "' ")
        tails = ("Example", "Profile")
        names = {
            start + core + join + tail
            for start in starts
            for core in cores
            for join in joins
            for tail in tails
        }
        names |= {start + "runner" for start in starts if start}
        names |= {start + "runneradmin" for start in starts if start}
        # Exact accounts with legal suffix punctuation are other names.
        names |= {
            core + suffix
            for core in ("runner", "runneradmin")
            for suffix in ("!", "'", ")", ";", ",", "-", "_", ".", " ")
        }
        for quote in ('"', "'", "`"):
            for separator in ("\\", "\\\\", "/"):
                root = "C:" + separator + "Users" + separator
                for name in sorted(names):
                    if quote in name:
                        continue
                    for form in (
                        quote + root + name + quote,
                        quote + root + name + separator + quote,
                    ):
                        findings = gate.scan(form, "text")
                        if len(findings) != 1:
                            self.fail(f"expected one finding for {form!r}")
            for name in ("runner", "runneradmin"):
                for form in (
                    '"' + root + name + '"',
                    '"' + root + name + separator + '"',
                ):
                    with self.subTest(form=form):
                        self.assertEqual(gate.scan(form, "text"), [])

    def test_terminal_ci_accounts_and_bare_roots_stay_clean(self) -> None:
        roots = ["C:\\Users\\", "C:\\\\Users\\\\", "C:/Users/", "/home/"]
        endings = (
            "",
            '"',
            "'",
            "`",
            ".",
            ",",
            ")",
            ".)",
            "!",
            "?",
            ":",
            "\t",
            "\n",
            "  \n",
            "/",
            ". Next sentence",
            ", and more",
        )
        for root in roots:
            for name in ("runner", "runneradmin"):
                for ending in endings:
                    for before in ("", '"', "'", "`", "("):
                        text = before + root + name + ending
                        with self.subTest(text=text):
                            self.assertEqual(gate.scan(text, "text"), [])
        home, data = "/home/", "/".join(["", "data", "users", ""])
        texts = (
            home,
            "C:\\Users\\",
            "Files under " + home + " are cleaned.",
            "See " + home + ".",
            "Roots (e.g. " + home + ") differ.",
            "The " + home.rstrip("/") + " and " + data.rstrip("/") + " trees.",
            "Standard roots include `" + home + "` and `" + data + "`.",
            "root = '" + home + "' + username",
            '"C:\\Users\\"',
        )
        for text in texts:
            with self.subTest(text=text):
                self.assertEqual(gate.scan(text, "text"), [])

    def test_separate_root_literals_are_not_profiles(self) -> None:
        texts = (
            "Standard roots include `/home/` and `/tmp/`.",
            "Standard roots include '/home/' and '/tmp/'.",
            "root = '/home/' + username + '/work'",
            "root = '/home/ ' + username + '/work'",
        )
        for text in texts:
            with self.subTest(text=text):
                self.assertEqual(gate.scan(text, "text"), [])

    def test_windows_ci_accounts_and_spaced_profiles(self) -> None:
        for separator in ("\\", "\\\\", "/"):
            for name in (
                "runner",
                "runneradmin",
                "runner Smith",
                "runneradmin Example",
                "runneradmin-extra",
            ):
                value = (
                    "C:"
                    + separator
                    + separator.join(("Users", name, "work", "notes.txt"))
                )
                with self.subTest(separator=separator, name=name):
                    self.assertEqual(
                        bool(gate.scan(value, "text")),
                        name not in ("runner", "runneradmin"),
                    )

    def test_windows_internal_workspace_layouts(self) -> None:
        layouts = (
            (("fbcode", "example", "file.py"), "internal-source-path"),
            (("fbsource", "example", "file.py"), "internal-source-path"),
            (
                ("", "tmp", "example", "worktrees", "file.py"),
                "temporary-workspace",
            ),
            (
                ("", "var", "tmp", "example", "lanes", "file.py"),
                "temporary-workspace",
            ),
        )
        for separator in ("\\", "\\\\", "/"):
            for parts, rule in layouts:
                value = separator.join(parts)
                with self.subTest(parts=parts, separator=separator):
                    findings = gate.scan(value, "text")
                    self.assertEqual(len(findings), 1)
                    self.assertEqual(findings[0]["rule"], rule)
            for value in (
                "notfbsource" + separator + "example",
                separator.join(("tmp", "example", "worktrees", "file.py")),
            ):
                self.assertEqual(gate.scan(value, "text"), [])

    def test_workspace_separator_runs(self) -> None:
        for separator in ("\\", "/"):
            self.assertEqual(
                gate.scan(separator * 100000 + "plain", "text"), []
            )

    def test_short_reference_boundary_and_runner_path(self):
        for prefix in "DTP":
            self.assertTrue(gate.scan(prefix + "12345", "text"))
            self.assertEqual(gate.scan(prefix + "1234", "text"), [])
        self.assertEqual(
            gate.scan("/".join(["", "home", "runner", "work"]), "text"), []
        )
        self.assertTrue(gate.scan("fbcode" + "/example/source.py", "text"))

    def test_internal_source_path_prefixes(self):
        for root in ("fbcode", "fbsource"):
            for prefix in (
                "",
                "/",
                "./",
                "../",
                "../../",
                "/opt/work/",
                "file:///",
                "~/",
            ):
                with self.subTest(root=root, prefix=prefix):
                    findings = gate.scan(
                        prefix + root + "/example/source.py", "text"
                    )
                    self.assertEqual(
                        [f["rule"] for f in findings], ["internal-source-path"]
                    )
            for prefix in ("my", "other_"):
                self.assertEqual(
                    gate.scan(prefix + root + "/example/source.py", "text"), []
                )

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


# Public citations (verbatim from public sources) and synthetic references.
PUBLIC_DOIS = (
    "https://doi.org/10.1017/S0308210500015080",
    "https://doi.org/10.1137/S0895480198349014",
    "https://doi.org/10.1112/S0024609305004261",
    "doi:10.1142/S0129054103001820",
)
PUBLIC_PII_URL = (
    "https://www.sciencedirect.com/science/article/pii/S0001870810002471"
)
REVIEWED = gate.REVIEWED_CITATIONS[0]
VALID_CITATIONS = PUBLIC_DOIS + (PUBLIC_PII_URL, REVIEWED)


def synthetic_pii(issn7="1234567", corrupt=False):
    """A clearly synthetic publisher-PII shape with a computed ISSN check."""
    total = sum(int(c) * w for c, w in zip(issn7, range(8, 1, -1)))
    check = (11 - total % 11) % 11
    digit = "X" if check == 10 else str(check)
    if corrupt:
        digit = "1" if digit == "0" else "0"
    return "S" + issn7 + digit + "2600001" + "0"


def supported_refs():
    """The suite's supported numeric forms: 9 digits, and each floor."""
    refs = [prefix + "123456789" for prefix in "DTPSNL"]
    refs += [prefix + "12345" for prefix in "DTP"]
    refs += [prefix + "123456" for prefix in "SNL"]
    return refs


class CitationSlots(unittest.TestCase):
    def assert_detected(self, text, ref):
        start = text.index(ref)
        self.assertEqual(text.count(ref), 1)
        self.assertIn(
            (start, start + len(ref)), gate.reference_spans(text, 0), text
        )
        self.assertTrue(gate.scan(text, "text", citation_start=0))

    def test_valid_citations_are_exempt_only_in_citation_scope(self):
        for citation in VALID_CITATIONS:
            for text in (citation, citation + ".", "(" + citation + ")"):
                with self.subTest(text=text):
                    self.assertEqual(
                        gate.scan(text, "text", citation_start=0), []
                    )
                    self.assertTrue(gate.scan(text, "text"))

    def test_inserted_supported_references_stay_detected(self):
        doi, url = PUBLIC_DOIS[0], PUBLIC_PII_URL
        stem = REVIEWED.rsplit(" ", 1)[0]
        for ref in supported_refs():
            placements = {
                "inside DOI slot": "doi:10.1017/" + ref,
                "inside https DOI slot": "https://doi.org/10.1017/" + ref,
                "inside PII URL slot": url.rsplit("/", 1)[0] + "/" + ref,
                "before citation": ref + " " + doi,
                "after citation": doi + " " + ref,
                "slash after DOI": doi + "/" + ref,
                "dot after DOI": doi + "." + ref,
                "comma after DOI": doi + "," + ref,
                "DOI query": doi + "?ref=" + ref,
                "DOI fragment": doi + "#" + ref,
                "PII URL query": url + "?ref=" + ref,
                "PII URL fragment": url + "#" + ref,
                "PII URL subpath": url + "/" + ref,
                "after reviewed citation": REVIEWED + " " + ref,
                "reviewed citation, other number": stem + " " + ref,
                "citation-shaped wrapper": "J. Stat. Mech. (2010) " + ref,
            }
            for name, text in placements.items():
                with self.subTest(ref=ref, placement=name):
                    self.assert_detected(text, ref)

    def test_aliases_and_invalid_slots_stay_strict(self):
        pii = synthetic_pii()
        # The synthetic PII is a valid slot in the recognized forms ...
        for text in (
            "doi:10.1017/" + pii,
            "https://doi.org/10.1017/" + pii,
            "https://www.sciencedirect.com/science/article/pii/" + pii,
        ):
            self.assertEqual(gate.scan(text, "text", citation_start=0), [])
        # ... so only the alias, prefix, context, or ISSN makes these strict.
        texts = (
            "https://dx.doi.org/10.1017/" + pii,
            "http://doi.org/10.1017/" + pii,
            "DOI:10.1017/" + pii,
            "doi.org/10.1017/" + pii,
            "https://doi.org/10.9999/" + pii,
            "/srv/cache/10.1017/" + pii,
            "http://www.sciencedirect.com/science/article/pii/" + pii,
            "https://sciencedirect.com/science/article/pii/" + pii,
            "doi:10.1017/" + synthetic_pii(issn7="0000000"),
            "doi:10.1017/" + synthetic_pii(corrupt=True),
        )
        for text in texts:
            ref = text[text.rindex("S") :]
            with self.subTest(text=text):
                self.assert_detected(text, ref)

    def test_other_rules_still_apply_next_to_citations(self):
        host = "https://example." + "internalfb" + ".com/x"
        findings = gate.scan(
            PUBLIC_DOIS[0] + " " + host, "text", citation_start=0
        )
        self.assertEqual([f["rule"] for f in findings], ["private-host"])

    def test_citation_start_limits_exemptions(self):
        text = PUBLIC_DOIS[0] + "\n\n" + PUBLIC_DOIS[0]
        start = text.index("S")
        self.assertEqual(
            gate.reference_spans(text, text.index("\n\n") + 2),
            [(start, start + 17)],
        )

    def test_reviewed_citation_constant_is_readable(self):
        self.assertEqual(
            REVIEWED,
            "D. Cimasoni, *A generalized Kac-Ward formula*, J. Stat. Mech. (2010) P07023",
        )

    def test_long_citation_heavy_input_is_bounded(self):
        unit = PUBLIC_DOIS[0] + ", " + PUBLIC_PII_URL + "; " + REVIEWED + "\n"
        text = unit * 20000
        self.assertEqual(gate.scan(text, "text", citation_start=0), [])
        self.assertEqual(
            len(gate.scan(text + private_ref(), "text", citation_start=0)), 1
        )


# Public university URLs quoted verbatim from repository references.
PUBLIC_URLS = (
    "https://www.math.cmu.edu/users/mubayi/papers/no-singleton.pdf",
    "https://users.math.msu.edu/users/meierfra/Preprints/Nflfsg/nflfsg.pdf",
)


class PublicUrlPaths(unittest.TestCase):
    def rules(self, text, scope=0):
        return [
            f["rule"] for f in gate.scan(text, "text", citation_start=scope)
        ]

    def test_public_url_paths_are_not_filesystem_paths(self):
        for url in PUBLIC_URLS:
            for text in (
                url,
                url + ".",
                "(" + url + ")",
                "<" + url + ">",
                "See " + url + " and " + url,
            ):
                with self.subTest(text=text):
                    self.assertEqual(self.rules(text), [])
                    self.assertTrue(self.rules(text, scope=None))
        self.assertEqual(self.rules("HTTPS://example.edu/home/alice/x.pdf"), [])
        self.assertEqual(
            self.rules("https://example.edu/tmp/alice/state/x.txt"), []
        )

    def test_filesystem_paths_stay_detected(self):
        bare = {
            "/".join(["", "Users", "alice", "work", "x"]): "personal-workspace",
            "/".join(["", "home", "alice", "x"]): "personal-workspace",
            "/".join(["", "data", "users", "alice", "x"]): "personal-workspace",
            "\\".join(["C:", "Users", "alice", "x"]): "personal-workspace",
            "/".join(["", "tmp", "w", "lanes", "x"]): "temporary-workspace",
        }
        url = "https://example.edu"
        for path, rule in bare.items():
            forward = path.replace("\\", "/").removeprefix("C:")
            cases = (
                path,
                "file://" + forward,
                url + "/view?file=" + forward,
                url + "/view#" + forward,
                url + "/C:" + forward,
                url + "/a" + path.replace("/", "\\").removeprefix("C:"),
                url + "/x " + path,
            )
            for text in cases:
                with self.subTest(text=text):
                    self.assertIn(rule, self.rules(text))
                    self.assertNotIn(
                        "alice",
                        json.dumps(gate.scan(text, "text", citation_start=0)),
                    )
        two = "https://example.edu/users/alice/x " + "/".join(
            ["", "home", "bob", "x"]
        )
        self.assertEqual(self.rules(two), ["personal-workspace"])

    def test_other_rules_still_apply_inside_url_paths(self):
        base = "https://www.math.cmu.edu/users/"
        cases = {
            base + private_ref() + "/x.pdf": "internal-reference",
            "/".join(
                ["https://example." + "internalfb" + ".com", "users", "a"]
            ): "private-host",
            "https://example.edu/"
            + "fbcode"
            + "/a/b.py": "internal-source-path",
        }
        for text, rule in cases.items():
            with self.subTest(rule=rule):
                self.assertEqual(self.rules(text), [rule])

    def test_local_and_nonpublic_url_authorities_stay_strict(self):
        home = "/".join(["", "home", "alice", "x"])
        hosts = (
            "localhost",
            "LocalHost",
            "localhost.",
            "localhost:8080",
            "a.b.localhost",
            "user:pw@localhost",
            "user@www.math.cmu.edu",
            "127.0.0.1",
            "127.0.0.1:8000",
            "127.1",
            "2130706433",
            "0x7f000001",
            "10.0.0.5",
            "192.168.1.10",
            "[::1]",
            "[::1]:8080",
            "[0:0:0:0:0:0:0:1]",
            "example.local",
            "Example.Local.",
            "box.internal",
            "printer.lan",
            "host.home.arpa",
            "devbox",
            "exa_mple.edu",
            "%6c%6fcalhost",
            "example.edu:http",
            "-bad-.edu",
            "1.0.0.127.in-addr.arpa",
            "xn--bcher-kva.example",
            "host.alt",
            "HOST.ALT",
            "host.alt.",
            "example.com",
            "www.example.com",
            "docs.example.net",
            "assets.example.org",
            "EXAMPLE.ORG:443",
            "a.b.Example.Net.",
        )
        for host in hosts:
            for scheme in ("http://", "HTTPS://"):
                text = scheme + host + home
                with self.subTest(text=text):
                    self.assertIn("personal-workspace", self.rules(text))

    def test_drive_bearing_and_hostless_url_paths_stay_strict(self):
        tail = "/".join(["Users", "Example", "work", "notes.txt"])
        home = "/".join(["", "home", "Example", "private.txt"])
        texts = (
            "https://example.edu/C:/" + tail,
            "https://example.edu/C:/./" + tail,
            "https://example.edu/C:/folder/../" + tail,
            "https://example.edu/docs/C:/./" + tail,
            "https://example.edu/c%3A/" + tail,
            "https://example.edu/C|/" + tail,
            "https://@" + home,
            "https://:" + home,
            "https://:443" + home,
            "https://user@" + home,
            "https://." + home,
            "https://.." + home,
        )
        for text in texts:
            with self.subTest(text=text):
                self.assertIn("personal-workspace", self.rules(text))

    def test_authority_length_bound_is_the_dns_maximum(self):
        host = ".".join(["a" * 63, "b" * 63, "c" * 63, "d" * 57, "edu"])
        self.assertEqual(len(host), 253)
        longest = host + ".:65535"
        self.assertEqual(len(longest), gate.MAX_AUTHORITY_CHARS)
        self.assertTrue(gate.public_authority(longest))
        self.assertFalse(gate.public_authority("x" + host))
        self.assertFalse(gate.public_authority(host + ":65536"))
        home = "/".join(["", "home", "alice", "x"])
        self.assertEqual(self.rules("https://" + longest + home), [])
        self.assertIn(
            "personal-workspace", self.rules("https://x" + longest + home)
        )

    def test_long_rejected_authorities_are_not_cached(self):
        gate._public_authority.cache_clear()
        home = "/".join(["", "home", "alice", "x"])
        for index in range(12):
            authority = str(index) + "a" * (1 << 20) + ".edu"
            self.assertFalse(gate.public_authority(authority))
            self.assertIn(
                "personal-workspace", self.rules("https://" + authority + home)
            )
        self.assertEqual(gate._public_authority.cache_info().currsize, 0)

    def test_scanning_many_long_authorities_retains_no_memory(self):
        home = "/".join(["", "home", "alice", "x"])
        gate._public_authority.cache_clear()
        gc.collect()
        tracemalloc.start()
        try:
            before = tracemalloc.get_traced_memory()[0]
            for index in range(12):
                text = "https://" + str(index) + "b" * (1 << 20) + ".edu" + home
                self.assertEqual(len(self.rules(text)), 1)
                del text
            gc.collect()
            retained = tracemalloc.get_traced_memory()[0] - before
        finally:
            tracemalloc.stop()
        self.assertLess(retained, 256 * 1024)
        self.assertLessEqual(gate._public_authority.cache_info().currsize, 0)

    def test_reviewed_url_boundary_counterexamples(self):
        home = "/".join(["", "home", "Example", "private.txt"])
        drive = "/".join(["", "Users", "Example", "work", "notes.txt"])
        strict = (
            "https://example.edu:65536" + home,
            "https://example.edu:99999" + home,
            "https://example.edu.." + home,
            "https://example.edu...:443" + home,
            "https://example.edu/%43:" + drive,
            "https://example.edu/%43%3A" + drive,
            "https://example.edu/%63%3a" + drive,
            "https://example.edu/C%7C" + drive,
        )
        for text in strict:
            with self.subTest(text=text):
                self.assertIn("personal-workspace", self.rules(text))
        exempt = (
            "https://example.edu:443" + home,
            "https://example.edu:65535" + home,
            "https://example.edu." + home,
            "https://example.edu.:443" + home,
            "https://example.edu/%2E/notes" + home,
        )
        for text in exempt:
            with self.subTest(text=text):
                self.assertEqual(self.rules(text), [])

    def test_public_url_authority_forms(self):
        for host in (
            "www.math.cmu.edu",
            "Www.Math.Cmu.Edu",
            "www.math.cmu.edu.",
            "www.math.cmu.edu:443",
            "xn--bcher-kva.ch",
            # Special-use suffixes match whole labels only.
            "notexample.com",
            "example.com.au",
            "alt.edu",
            "example.community",
        ):
            url = PUBLIC_URLS[0].replace("www.math.cmu.edu", host)
            with self.subTest(host=host):
                self.assertEqual(self.rules(url), [])

    def test_terminal_profile_url_paths(self):
        url = "https://www.math.cmu.edu/users/mubayi"
        for text in (
            url,
            url + ".",
            "(" + url + ")",
            "'" + url + "'",
            '"' + url + '"',
            "`" + url + "`",
            "<" + url + ">",
            "See " + url + " for the paper",
        ):
            with self.subTest(text=text):
                self.assertEqual(self.rules(text), [])
        home = "/".join(["", "home", "Example"])
        for text in (
            "https://www.example.com" + "/".join(["", "users", "Example"]),
            "https://host.alt" + "/".join(["", "users", "Example"]),
            "https://example.edu/view?file=" + home,
            "https://example.edu/view#" + home,
            "http://localhost" + home,
        ):
            with self.subTest(text=text):
                self.assertIn("personal-workspace", self.rules(text))

    def test_control_characters_end_url_paths(self):
        url = "https://www.math.cmu.edu/users/mubayi"
        home = "/".join(["", "home", "Example", "private.txt"])
        controls = [*range(0x00, 0x20), 0x7F, *range(0x80, 0xA0)]
        for code in controls:
            c = chr(code)
            for text in (
                url + c + home,
                "https://www.math.cmu.edu/" + c + home,
                "https://www.math.cmu.edu/pub" + c + "lic" + home,
                url + c + c + home,
                url + c + " " + home,
                "https://www.math" + c + "cmu.edu" + home,
                "https://www.math.cmu.edu/x?q" + c + "=" + home,
            ):
                with self.subTest(code=hex(code), text=ascii(text)):
                    self.assertIn("personal-workspace", self.rules(text))
            with self.subTest(code=hex(code), case="prefix before control"):
                # A path wholly inside the URL before the control keeps its
                # exemption; only text from the control on is outside it.
                self.assertEqual(self.rules(url + home + c + "tail"), [])
                # A later drive-letter path no longer voids that prefix; it
                # is checked as text after the control.
                drive = "/".join(["", "C:", "Users", "Example", "x.txt"])
                self.assertEqual(
                    self.rules(url + home + c + drive), ["personal-workspace"]
                )
        # Not controls: unchanged URL-path behavior.
        for text in (
            url + "\ufffd" + home,
            url + "\u200b" + home,
            url + "\u202e" + home,
            url + "%00" + home,
            url + "%7F" + home,
            url + home,
        ):
            with self.subTest(text=ascii(text)):
                self.assertEqual(self.rules(text), [])
        lone = (url.encode() + b"\x80" + home.encode()).decode(
            "utf-8", errors="replace"
        )
        self.assertEqual(self.rules(lone), [])
        # Literal contexts never had the URL-path exemption.
        self.assertIn(
            "personal-workspace",
            [
                f["rule"]
                for f in gate.scan(url + home, "x", rules=gate.LITERAL_RULES)
            ],
        )

    def test_url_heavy_input_is_bounded(self):
        text = "\n".join(PUBLIC_URLS) * 20000
        self.assertEqual(gate.scan(text, "text", citation_start=0), [])
        tail = "\n" + "/".join(["", "home", "alice", "x"])
        self.assertEqual(self.rules(text + tail), ["personal-workspace"])


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

    def test_windows_workspace_in_a_commit_and_blob(self) -> None:
        value = "C:" + "\\".join(("", "Users", "example", "notes.txt"))
        self.write("notes.md", value)
        self.commit("Private workspace\n\n" + value)
        findings = self.check()["findings"]
        self.assertEqual(len(findings), 2)
        self.assertTrue(
            all(f["rule"] == "personal-workspace" for f in findings)
        )
        self.assertNotIn(value, json.dumps(findings))

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

    def test_merge_from_base_does_not_reintroduce_base_filenames(self):
        original = self.run_git("branch", "--show-current")
        self.run_git("checkout", "-q", "-b", "topic")
        self.write("topic.md", "Topic text")
        self.commit("Add topic")
        self.run_git("checkout", "-q", original)
        self.write(private_ref() + ".md", "Base text")
        self.commit("Add base file")
        self.base = self.head()
        self.run_git("checkout", "-q", "topic")
        self.run_git("merge", "-q", "--no-ff", original, "-m", "Merge base")
        result = self.check()
        self.assertEqual(result["findings"], [])
        self.assertEqual(result["blobs"], 1)

    def test_base_advance_does_not_reintroduce_old_filenames(self):
        original = self.run_git("branch", "--show-current")
        self.run_git("checkout", "-q", "-b", "topic")
        self.write("topic.md", "Topic text")
        self.commit("Add topic")
        self.run_git("checkout", "-q", original)
        name = private_ref() + ".md"
        self.write(name, "Base text")
        self.commit("Add base file")
        self.run_git("checkout", "-q", "topic")
        self.run_git("merge", "-q", "--no-ff", original, "-m", "Merge base")
        self.run_git("checkout", "-q", original)
        (self.root / name).unlink()
        self.commit("Remove old base file")
        self.base = self.head()
        self.run_git("checkout", "-q", "topic")
        result = self.check()
        self.assertEqual(result["findings"], [])
        self.assertEqual(result["blobs"], 1)

    def test_merge_created_filename_using_a_base_blob_is_checked(self):
        self.write("legacy.md", "Base text")
        self.commit("Add base file")
        self.base = self.head()
        original = self.run_git("branch", "--show-current")
        self.run_git("checkout", "-q", "-b", "side")
        self.write("side.md", "Side text")
        self.commit("Add side file")
        self.run_git("checkout", "-q", original)
        self.write("topic.md", "Topic text")
        self.commit("Add topic")
        self.run_git("merge", "-q", "--no-ff", "--no-commit", "side")
        self.write(private_ref() + ".md", "Base text")
        self.commit("Merge side")
        result = self.check()
        self.assertEqual(len(result["findings"]), 1)
        self.assertEqual(result["blobs"], 2)
        self.assertIn(self.head(), result["findings"][0]["location"])

    def test_merge_inherits_filename_from_scanned_side_history(self):
        original = self.run_git("branch", "--show-current")
        self.run_git("checkout", "-q", "-b", "side")
        self.write(private_ref() + ".md", "Side text")
        self.commit("Add side file")
        side = self.head()
        self.run_git("checkout", "-q", original)
        self.write("topic.md", "Topic text")
        self.commit("Add topic")
        self.run_git("merge", "-q", "--no-ff", "side", "-m", "Merge side")
        result = self.check()
        self.assertEqual(len(result["findings"]), 1)
        self.assertIn(side, result["findings"][0]["location"])

    def test_restoring_a_deleted_base_filename_is_checked(self):
        name = private_ref() + ".md"
        self.write(name, "Base text")
        self.commit("Add base file")
        (self.root / name).unlink()
        self.commit("Remove base file")
        self.base = self.head()
        self.write(name, "Base text")
        self.commit("Restore file")
        result = self.check()
        self.assertEqual(len(result["findings"]), 1)
        self.assertEqual(result["blobs"], 1)

    def test_octopus_merge_checks_only_new_filename_origins(self):
        original = self.run_git("branch", "--show-current")
        self.run_git("checkout", "-q", "-b", "topic")
        self.write("topic.md", "Topic text")
        self.commit("Add topic")
        self.run_git("checkout", "-q", original)
        self.run_git("checkout", "-q", "-b", "side")
        self.write("side.md", "Side text")
        self.commit("Add side")
        self.run_git("checkout", "-q", original)
        self.write(private_ref() + ".md", "Base text")
        self.commit("Add base file")
        self.base = self.head()
        self.run_git("checkout", "-q", "topic")
        self.run_git("merge", "-q", "--no-ff", "--no-commit", original, "side")
        self.write(private_ref("P") + ".md", "Base text")
        self.commit("Merge base and side")
        self.assertEqual(
            len(self.run_git("show", "-s", "--format=%P").split()), 3
        )
        result = self.check()
        self.assertEqual(len(result["findings"]), 1)
        self.assertIn(self.head(), result["findings"][0]["location"])
        self.assertEqual(result["blobs"], 2)

    def test_merge_deletion_does_not_scan_the_deleted_filename(self):
        name = private_ref() + ".md"
        self.write(name, "Base text")
        self.commit("Add base file")
        self.base = self.head()
        original = self.run_git("branch", "--show-current")
        self.run_git("checkout", "-q", "-b", "side")
        self.write("side.md", "Side text")
        self.commit("Add side")
        self.run_git("checkout", "-q", original)
        self.write("topic.md", "Topic text")
        self.commit("Add topic")
        self.run_git("merge", "-q", "--no-ff", "--no-commit", "side")
        (self.root / name).unlink()
        self.commit("Merge and remove old file")
        self.assertEqual(self.check()["findings"], [])

    def test_incomplete_combined_filename_diff_fails_closed(self):
        original = self.run_git("branch", "--show-current")
        self.run_git("checkout", "-q", "-b", "side")
        self.write("notes.md", "Public text")
        self.commit("Add notes")
        self.run_git("checkout", "-q", original)
        self.run_git("merge", "-q", "--no-ff", "side", "-m", "Merge notes")
        read_git = gate.git

        def truncated(root, *args, **kwargs):
            if "--name-only" in args:
                return b"unterminated"
            return read_git(root, *args, **kwargs)

        with patch.object(gate, "git", side_effect=truncated):
            with self.assertRaises(gate.IncompleteScan):
                self.check()

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

    def test_roadmap_label_in_intermediate_blob(self):
        label = roadmap_ref("AREA", "TOPIC", "LEAF")
        self.write("notes.md", "Discharges roadmap leaf `" + label + "`.\n")
        self.commit("Add notes")
        self.write("notes.md", "Public final description.\n")
        self.commit("Clarify description")
        result = self.check()
        self.assertEqual(
            (result["commits"], result["files"], result["blobs"]), (2, 1, 2)
        )
        self.assertEqual(len(result["findings"]), 1)
        self.assertEqual(
            result["findings"][0]["rule"], "private-roadmap-reference"
        )
        self.assertNotIn(label, json.dumps(result))

    def test_branch_planning_separators_and_raw_dotted_case(self):
        for separator in ("-", "_"):
            branch = "feature/" + separator.join(
                ("f" + "10", "example", "leaf")
            )
            self.assertEqual(len(self.check({"branch": branch})["findings"]), 1)
        lesson_branch = "feature/f" + "99" + "/s98l97-example"
        self.assertEqual(
            len(self.check({"branch": lesson_branch})["findings"]), 1
        )
        label = roadmap_ref("HW", "DEVICE", "L1")
        self.assertEqual(len(self.check({"branch": label})["findings"]), 1)
        for branch in (
            label.lower(),
            "release.v1.x",
            "feature.release.v1.x",
            "feature/f2/fix-typo",
            "popgen/f2/form-relations",
            "deps/f12/x/y",
            "release/f1/v2-fix",
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

    def test_citations_in_commit_message_only_not_headers(self):
        self.commit("Cite " + PUBLIC_DOIS[0] + "\n\nSee " + REVIEWED)
        self.assertEqual(self.check()["findings"], [])
        self.base = self.head()
        self.run_git("config", "user.name", "Example " + PUBLIC_DOIS[0])
        self.commit("Ordinary change")
        findings = self.check()["findings"]
        raw = gate.git(self.root, "cat-file", "commit", self.head()).decode()
        lines = raw.split("\n")
        expected = [
            i + 1
            for i, line in enumerate(lines)
            if line.startswith(("author ", "committer "))
        ]
        self.assertEqual(sorted(f["line"] for f in findings), expected)
        self.assertTrue(
            all(f["location"].startswith("commit ") for f in findings)
        )

    def test_citations_in_signature_shaped_headers_stay_strict(self):
        tree = self.run_git("rev-parse", "HEAD^{tree}")
        identity = "Example <author@example.com> 1700000000 +0000"
        for field in ("gpgsig", "x-provenance"):
            with self.subTest(field=field):
                value = (
                    "-----BEGIN PGP SIGNATURE-----\n"
                    + PUBLIC_DOIS[0]
                    + "\n-----END PGP SIGNATURE-----"
                )
                raw = (
                    f"tree {tree}\nparent {self.base}\n"
                    f"author {identity}\ncommitter {identity}\n"
                    + field
                    + " "
                    + value.replace("\n", "\n ")
                    + "\n\nOrdinary change\n"
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
                findings = gate.check_range(self.root, self.base, sha)[
                    "findings"
                ]
                self.assertEqual([f["line"] for f in findings], [6])

    def test_citations_in_regular_and_executable_files_are_exempt(self):
        self.write("refs.md", "\n".join(VALID_CITATIONS) + "\n")
        self.write("tool.sh", "# " + PUBLIC_DOIS[1] + "\n")
        os.chmod(self.root / "tool.sh", 0o755)
        self.commit("Add references")
        self.assertEqual(self.check()["findings"], [])

    def test_symlink_targets_stay_strict_in_either_order(self):
        for regular, link in (("a.md", "z-link"), ("z.md", "a-link")):
            with self.subTest(regular=regular, link=link):
                self.base = self.head()
                self.write(regular, PUBLIC_DOIS[0])
                (self.root / link).symlink_to(PUBLIC_DOIS[0])
                self.commit("Add regular file and link with one blob")
                result = self.check()
                self.assertEqual(result["blobs"], 1)
                self.assertEqual(len(result["findings"]), 1)
                self.assertEqual(
                    result["findings"][0]["rule"], "internal-reference"
                )
                self.assertTrue(
                    result["findings"][0]["location"].startswith(link + " @ ")
                )
                for name in (regular, link):
                    (self.root / name).unlink()
                self.commit("Remove fixtures")

    def test_base_citation_bytes_reused_as_symlink_target_stay_strict(self):
        for case in ("add link", "regular to link", "executable to link"):
            with self.subTest(case=case):
                name = case.split()[0] + ".md"
                self.write(name, PUBLIC_DOIS[0])
                if case.startswith("executable"):
                    os.chmod(self.root / name, 0o755)
                self.commit("Add citation file")
                self.assertEqual(self.check()["findings"], [])
                self.base = self.head()
                link = name + "-link" if case == "add link" else name
                if link == name:
                    (self.root / name).unlink()
                (self.root / link).symlink_to(PUBLIC_DOIS[0])
                self.commit("Point a link at the citation text")
                result = self.check()
                self.assertEqual(result["blobs"], 1)
                self.assertEqual(len(result["findings"]), 1)
                self.assertTrue(
                    result["findings"][0]["location"].startswith(link + " @ ")
                )
                for path in {name, link}:
                    if (self.root / path).is_symlink() or (
                        self.root / path
                    ).exists():
                        (self.root / path).unlink()
                self.commit("Remove fixtures")
                self.base = self.head()

    def test_inherited_base_symlink_through_merge_is_excluded(self):
        fork = self.head()
        (self.root / "link").symlink_to(PUBLIC_DOIS[0])
        self.commit("Base adds a link")
        base = self.head()
        self.run_git("checkout", "-q", "-b", "topic", fork)
        self.write("topic.md", "Public topic text\n")
        self.commit("Topic change")
        self.run_git("merge", "-q", "--no-edit", base)
        self.assertTrue((self.root / "link").is_symlink())
        result = gate.check_range(self.root, base, self.head())
        self.assertEqual(result["commits"], 2)
        self.assertEqual(result["findings"], [])

    def test_citation_filenames_and_branches_stay_strict(self):
        self.write("refs/10.1017/" + synthetic_pii() + ".md", "Public notes\n")
        self.commit("Add notes")
        self.assertEqual(len(self.check()["findings"]), 1)
        self.base = self.head()
        self.assertEqual(
            len(self.check({"branch": "fix/" + PUBLIC_DOIS[0]})["findings"]), 1
        )
        self.assertEqual(
            self.check({"title": PUBLIC_DOIS[0], "body": REVIEWED})["findings"],
            [],
        )

    def test_cli_terminal_profiles_in_every_scope(self):
        profile = "/".join(["", "home", "Example"])
        for text in (
            profile,
            '"C:' + "\\".join(["", "Users", "Example"]) + '"',
        ):
            with self.subTest(text=text):
                self.base = self.head()
                self.write("notes.md", "See " + text + "\n")
                self.commit("Add notes\n\nSee " + text)
                metadata = self.root / "pr.json"
                metadata.write_text(json.dumps({"title": text, "body": text}))
                run = subprocess.run(
                    [
                        sys.executable,
                        gate.__file__,
                        "--repo-root",
                        str(self.root),
                        "--base",
                        self.base,
                        "--head",
                        self.head(),
                        "--metadata",
                        str(metadata),
                    ],
                    capture_output=True,
                    text=True,
                )
                metadata.unlink()
                self.assertEqual(run.returncode, 1, run.stdout)
                report = json.loads(run.stdout)
                self.assertEqual(len(report["findings"]), 4)
                self.assertNotIn("Example", run.stdout + run.stderr)

    def test_terminal_profiles_in_strict_contexts(self):
        self.write("/".join(["docs", "home", "Example"]), "Clean text\n")
        (self.root / "link").symlink_to("/".join(["", "home", "Example"]))
        self.run_git("config", "user.name", "/".join(["", "home", "Example"]))
        self.commit("Add strict-context fixtures")
        findings = self.check(
            {"branch": "fix" + "/".join(["", "home", "Example"])}
        )
        locations = [f["location"] for f in findings["findings"]]
        self.assertTrue(any(l.startswith("filename") for l in locations))
        self.assertTrue(any(l.startswith("link @ ") for l in locations))
        self.assertTrue(
            any(
                l.endswith("header") or l.startswith("commit ")
                for l in locations
            )
        )
        self.assertTrue(any(l == "PR branch" for l in locations))
        self.assertTrue(
            all(f["rule"] == "personal-workspace" for f in findings["findings"])
        )

    def test_literal_contexts_report_ci_prefixed_names(self):
        home = "/".join(["", "home", ""])
        self.write("docs" + home + "runner!", "Clean text\n")
        self.write("docs" + home + "runner", "Clean text\n")
        (self.root / "link").symlink_to(home + "runner. Example")
        (self.root / "ci-link").symlink_to(home + "runner")
        self.run_git("config", "user.name", home + "runner!")
        self.commit("Add literal-context fixtures")
        findings = self.check({"branch": "fix" + home + "runner!"})
        locations = sorted(f["location"] for f in findings["findings"])
        # Git uses the configured name for both author and committer.
        self.assertEqual(len(locations), 5, locations)
        self.assertTrue(locations[0].startswith("PR branch"))
        self.assertTrue(locations[1].startswith("commit "))
        self.assertEqual(locations[1], locations[2])
        self.assertTrue(locations[3].startswith("filename in commit "))
        self.assertTrue(locations[4].startswith("link @ "))
        header = [
            f for f in findings["findings"] if f["location"] == locations[1]
        ]
        self.assertEqual(sorted(f["line"] for f in header), [3, 4])
        self.assertTrue(
            all(f["rule"] == "personal-workspace" for f in findings["findings"])
        )

    def test_literal_filenames_keep_windows_invalid_characters(self):
        home = "/".join(["docs", "home", ""])
        for mark in ("?", ":", "|", "<", ">", "*", '"'):
            self.write(home + "runner" + mark + "private", "Clean text\n")
            self.write(home + "runner" + mark + "x/leaf.txt", "Clean text\n")
        self.write(home + "runner", "Clean text\n")
        # The exact account before a further component stays clean.
        self.write("docs/data/users/runner/leaf.txt", "Clean text\n")
        self.commit("Add literal-name fixtures")
        findings = self.check()["findings"]
        self.assertEqual(len(findings), 14, findings)
        self.assertTrue(
            all(f["location"].startswith("filename in ") for f in findings)
        )

    def test_tagger_identity_needs_a_supported_tag_header(self):
        home = "/".join(["", "home", ""])
        z = "0" * 40
        plain = (
            "author A <a@example.invalid> 1 +0000\n"
            "committer C <c@example.invalid> 1 +0000\n"
        )
        exact = " tagger T <" + home + "runner> 1 +0000\n"
        start = "mergetag object " + z + "\n"
        shapes = {
            # name: (embedded tag lines, expected finding lines)
            "supported": (start + " type commit\n tag v1\n" + exact, []),
            "bad object": (
                "mergetag object x\n type commit\n tag v1\n" + exact,
                [7],
            ),
            "bad field before": (
                start + " x-bad y\n type commit\n tag v1\n" + exact,
                [8],
            ),
            "bad field after": (
                start + " type commit\n tag v1\n" + exact + " x-bad y\n",
                [7],
            ),
            "out of order": (start + " tag v1\n type commit\n" + exact, [7]),
            "duplicate type": (
                start + " type commit\n type commit\n tag v1\n" + exact,
                [8],
            ),
            "duplicate tag": (
                start + " type commit\n tag v1\n tag v2\n" + exact,
                [8],
            ),
            "duplicate tagger": (
                start + " type commit\n tag v1\n" + exact + exact,
                [7, 8],
            ),
            "missing tag": (start + " type commit\n" + exact, [6]),
        }
        for name, (lines, expected) in shapes.items():
            for closed in (True, False):
                body = lines + (" \n m\n" if closed else "x-after z\n")
                want = expected if closed or not name == "supported" else [7]
                raw = ("tree " + z + "\n" + plain + body + "\nMsg\n").encode()
                with self.subTest(shape=name, closed=closed):
                    findings = gate.scan_commit(raw, z, None, ("A", "C"))
                    self.assertEqual(sorted(f["line"] for f in findings), want)
        # Each mergetag starts a fresh decision: an unsupported block does
        # not taint the next supported one, nor the reverse.
        bad = "mergetag not-a-tag\n" + exact + " \n m\n"
        good = start + " type commit\n tag v1\n" + exact + " \n m\n"
        for blocks, expected in (
            (bad + good, [5]),
            (good + bad, [11]),
            (bad + bad, [5, 9]),
            (good + good, []),
        ):
            raw = ("tree " + z + "\n" + plain + blocks + "\nMsg\n").encode()
            with self.subTest(blocks=blocks):
                findings = gate.scan_commit(raw, z, None, ("A", "C"))
                self.assertEqual(sorted(f["line"] for f in findings), expected)

    def test_existing_names_stay_quiet_on_content_and_mode_edits(self):
        name = "D" + "12345.md"
        self.write(name, "Base text\n")
        os.symlink("target.txt", self.root / "link")
        self.commit("Base with a matching name")
        self.base = self.head()
        self.write(name, "Edited text\n")
        self.commit("Edit the existing file")
        os.chmod(self.root / name, 0o755)
        self.commit("Change its mode")
        self.assertEqual(self.check()["findings"], [])
        # Changed contents are still scanned, with a masked location.
        self.write(name, "Ticket " + "P" + "1234567\n")
        self.commit("Add a private reference")
        findings = self.check()["findings"]
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["location"], "[redacted]")
        # A retyped entry keeps its name; a strict symlink target is checked.
        (self.root / name).unlink()
        os.symlink("/".join(["", "home", "runner!"]), self.root / name)
        self.commit("Turn it into a symlink")
        findings = self.check()["findings"]
        self.assertEqual(
            sorted(f["rule"] for f in findings),
            ["internal-reference", "personal-workspace"],
        )
        self.assertTrue(all(f["location"] == "[redacted]" for f in findings))

    def test_new_destinations_still_get_name_checks(self):
        name = "D" + "12345.md"
        self.write(name, "Base text\n")
        self.commit("Base with a matching name")
        self.base = self.head()
        self.run_git("mv", name, "D" + "77777.md")
        self.commit("Rename")
        self.write("D" + "99999.md", "Base text\n")
        self.commit("Copy the same text to another matching name")
        findings = self.check()["findings"]
        self.assertEqual(len(findings), 2)
        self.assertTrue(
            all(f["location"].startswith("filename in ") for f in findings)
        )

    def test_merge_resolution_keeps_an_existing_name(self):
        name = "D" + "12345.md"
        self.write(name, "Base text\n")
        self.commit("Base with a matching name")
        self.base = self.head()
        self.run_git("checkout", "-q", "-b", "side")
        self.write(name, "Side text\n")
        self.commit("Side edit")
        self.run_git("checkout", "-q", "-")
        self.write(name, "Main text\n")
        self.commit("Main edit")
        subprocess.run(
            ["git", "-C", str(self.root), "merge", "-q", "side"],
            capture_output=True,
        )
        self.write(name, "Resolved text\n")
        self.commit("Resolve")
        self.assertEqual(
            len(self.run_git("log", "-1", "--format=%P").split()), 2
        )
        self.assertEqual(self.check()["findings"], [])

    def test_merge_restoring_an_entry_the_base_removed_is_checked(self):
        for kind in ("name", "link", "content"):
            with self.subTest(kind=kind):
                self.setUp()
                name = ("D" + "12345.md") if kind == "name" else "legacy"
                if kind == "link":
                    os.symlink(
                        "/".join(["", "home", "runner!"]), self.root / name
                    )
                else:
                    text = (
                        "T" + "54321\n" if kind == "content" else "Old text\n"
                    )
                    self.write(name, text)
                self.commit("Old base")
                self.run_git("checkout", "-q", "-b", "side")
                self.write("other.md", "New text\n")
                self.commit("Side change")
                self.run_git("checkout", "-q", "-")
                self.run_git("rm", "-q", name)
                self.commit("Base removes the entry")
                self.base = self.head()
                subprocess.run(
                    [
                        "git",
                        "-C",
                        str(self.root),
                        "merge",
                        "--no-ff",
                        "--no-commit",
                        "side",
                    ],
                    capture_output=True,
                )
                self.assertFalse(os.path.lexists(self.root / name))
                self.run_git(
                    "restore",
                    "--source=side",
                    "--staged",
                    "--worktree",
                    "--",
                    name,
                )
                self.commit("Restore it in the merge")
                findings = self.check()["findings"]
                self.assertEqual(len(findings), 1, findings)
                prefix = "filename in " if kind == "name" else name + " @ "
                self.assertTrue(findings[0]["location"].startswith(prefix))

    def test_side_edits_do_not_vouch_for_restored_entries(self):
        # A side commit that only changes the mode or public contents of an
        # entry, or flips it back, never checked that entry's name or old
        # bytes; restoring it after the base removed it is still checked.
        name = "D" + "12345.md"
        for edit in ("chmod", "content", "flip-back"):
            for removed in (True, False):
                with self.subTest(edit=edit, removed=removed):
                    self.setUp()
                    self.write(name, "T" + "54321\n")
                    self.commit("Old base")
                    self.run_git("checkout", "-q", "-b", "side")
                    if edit == "content":
                        self.write(name, "Public text\n")
                    else:
                        os.chmod(self.root / name, 0o755)
                    self.commit("Side edit")
                    if edit == "flip-back":
                        os.chmod(self.root / name, 0o644)
                        self.commit("Side flip back")
                    self.run_git("checkout", "-q", "-")
                    if removed:
                        self.run_git("rm", "-q", name)
                    else:
                        self.write("other.md", "Base text\n")
                    self.commit("Base change")
                    self.base = self.head()
                    subprocess.run(
                        [
                            "git",
                            "-C",
                            str(self.root),
                            "merge",
                            "--no-ff",
                            "--no-commit",
                            "side",
                        ],
                        capture_output=True,
                    )
                    self.run_git(
                        "restore",
                        "--source=side",
                        "--staged",
                        "--worktree",
                        "--",
                        name,
                    )
                    self.commit("Resolve to the side entry")
                    findings = self.check()["findings"]
                    if not removed:
                        self.assertEqual(findings, [])
                        continue
                    names = [
                        f
                        for f in findings
                        if f["location"].startswith("filename in ")
                    ]
                    self.assertEqual(len(names), 1, findings)
                    old_bytes = edit != "content"
                    contents = [f for f in findings if f not in names]
                    self.assertEqual(len(contents), int(old_bytes), findings)
                    for finding in contents:
                        self.assertEqual(finding["location"], "[redacted]")

    def test_restored_old_bytes_are_scanned_on_every_branch(self):
        old = "T" + "54321\n"

        def scenario(resolve, keep_in_base=None, one_parent=False):
            self.setUp()
            self.write("legacy.md", old)
            self.commit("Old base")
            self.run_git("checkout", "-q", "-b", "side")
            self.write("legacy.md", "Public text\n")
            self.commit("Side edits it clean")
            self.run_git("checkout", "-q", "-")
            self.run_git("rm", "-q", "legacy.md")
            if keep_in_base:
                self.write(keep_in_base, old)
            self.commit("Base removes the file")
            self.base = self.head()
            if one_parent:
                self.write("legacy.md", old)
                self.commit("Bring the old bytes back directly")
                return self.check()["findings"]
            subprocess.run(
                [
                    "git",
                    "-C",
                    str(self.root),
                    "merge",
                    "--no-ff",
                    "--no-commit",
                    "side",
                ],
                capture_output=True,
            )
            resolve()
            self.commit("Resolve the merge")
            self.assertEqual(
                len(self.run_git("log", "-1", "--format=%P").split()), 2
            )
            return self.check()["findings"]

        def old_bytes():
            self.write("legacy.md", old)
            self.run_git("add", "legacy.md")

        def old_bytes_executable():
            old_bytes()
            os.chmod(self.root / "legacy.md", 0o755)
            self.run_git("add", "legacy.md")

        for label, kwargs, expected in (
            ("merge resolves to old bytes", {"resolve": old_bytes}, 1),
            ("old bytes and mode", {"resolve": old_bytes_executable}, 1),
            ("one-parent restore", {"resolve": None, "one_parent": True}, 1),
            (
                "bytes still in base, same path",
                {"resolve": old_bytes, "keep_in_base": "legacy-copy.md"},
                0,
            ),
            (
                "bytes still in base, one parent",
                {
                    "resolve": None,
                    "keep_in_base": "kept.md",
                    "one_parent": True,
                },
                0,
            ),
        ):
            with self.subTest(label=label):
                findings = scenario(**kwargs)
                self.assertEqual(len(findings), expected, findings)
                for finding in findings:
                    self.assertEqual(finding["rule"], "internal-reference")
                    self.assertTrue(
                        finding["location"].startswith("legacy.md @ ")
                    )

    def test_an_older_base_ancestor_does_not_vouch_for_removed_entries(self):
        # A merge with an ancestor of the current base restores an entry the
        # base removed; that ancestor's tree is not current.
        self.write("legacy.md", "T" + "54321\n")
        self.commit("Old base")
        old = self.head()
        self.run_git("rm", "-q", "legacy.md")
        self.commit("Base removes the file")
        self.base = self.head()
        head = self.run_git(
            "commit-tree",
            old + "^{tree}",
            "-p",
            self.base,
            "-p",
            old,
            "-m",
            "Merge the old ancestor and keep its file",
        )
        self.run_git("update-ref", "HEAD", head)
        findings = self.check()["findings"]
        self.assertEqual(len(findings), 1, findings)
        self.assertTrue(findings[0]["location"].startswith("legacy.md @ "))
        # Control: a base-side commit that is not contained in the other
        # parent still vouches for its own current entries.
        self.setUp()
        self.write("legacy.md", "Public text\n")
        self.commit("Base file")
        self.base = self.head()
        self.run_git("checkout", "-q", "-b", "topic", self.base + "~1")
        self.write("topic.md", "Topic\n")
        self.commit("Topic work")
        self.run_git("merge", "-q", "--no-edit", self.base)
        self.assertEqual(self.check()["findings"], [])

    def test_merge_written_paths_need_current_bytes(self):
        # Topic forks first; old base P has private bytes; current base C
        # removes them; a merge with P writes those bytes at a new path.
        self.write("other.md", "Fork text\n")
        self.commit("Fork")
        fork = self.head()
        self.write("source.md", "T" + "54321\n")
        self.commit("Old base")
        old = self.head()
        for keep, expected in ((False, 1), (True, 0)):
            with self.subTest(current_keeps_bytes=keep):
                self.run_git("checkout", "-q", "-B", "main", old)
                self.run_git("rm", "-q", "source.md")
                if keep:
                    self.write("kept.md", "T" + "54321\n")
                self.commit("Current base")
                self.base = self.head()
                self.run_git("checkout", "-q", "-B", "topic", fork)
                self.write("topic.md", "Topic\n")
                self.commit("Topic work")
                subprocess.run(
                    [
                        "git",
                        "-C",
                        str(self.root),
                        "merge",
                        "--no-ff",
                        "--no-commit",
                        old,
                    ],
                    capture_output=True,
                )
                self.run_git("mv", "source.md", "new.md")
                self.commit("Merge the old base, moving its file")
                findings = self.check()["findings"]
                contents = [
                    f for f in findings if f["location"].startswith("new.md @ ")
                ]
                self.assertEqual(len(contents), expected, findings)

    def test_a_base_side_parent_vouches_only_for_its_exact_entries(self):
        # A topic keeps foo unchanged; a base-side parent holds the same
        # bytes only under another path, which the current base removed.
        data = "T" + "54321"
        for kept, alias, current, expected in (
            ("file", "file", False, 1),
            ("file", "link", False, 1),
            ("link", "link", False, 1),
            ("file", "file", True, 0),
            ("link", "link", True, 0),
        ):
            with self.subTest(kept=kept, alias=alias, current=current):
                self.setUp()
                if kept == "link":
                    os.symlink(data, self.root / "foo")
                else:
                    (self.root / "foo").write_bytes(data.encode())
                self.commit("A")
                a = self.head()
                self.run_git("checkout", "-q", "-b", "topic")
                self.write("topic.md", "Topic\n")
                self.commit("Q changes only topic.md")
                q = self.head()
                self.run_git("checkout", "-q", "-B", "main", a)
                self.run_git("rm", "-q", "foo")
                if alias == "link":
                    os.symlink(data, self.root / "source")
                else:
                    (self.root / "source").write_bytes(data.encode())
                self.commit("P moves the bytes to source")
                p = self.head()
                if not current:
                    self.run_git("rm", "-q", "source")
                    self.commit("C removes source")
                self.base = self.head()
                tree = self.run_git("rev-parse", q + "^{tree}")
                head = self.run_git(
                    "commit-tree", tree, "-p", q, "-p", p, "-m", "M keeps foo"
                )
                self.run_git("update-ref", "HEAD", head)
                findings = [
                    f
                    for f in self.check()["findings"]
                    if f["location"].startswith("foo @ ")
                ]
                self.assertEqual(len(findings), expected, findings)

    def test_eligible_parent_names_and_entries_are_separate(self):
        # Topic forks; old base P adds a matching name with public text;
        # current base C removes it; the merge with P keeps that path.
        name = "D" + "12345.md"
        for label, text, mode, expected in (
            ("exact entry", "Public text\n", 0o644, []),
            ("public edit", "Edited public text\n", 0o644, []),
            ("private edit", "T" + "54321\n", 0o644, ["[redacted]"]),
            ("mode change", "Public text\n", 0o755, []),
        ):
            with self.subTest(label=label):
                self.setUp()
                fork = self.head()
                self.write(name, "Public text\n")
                self.commit("P adds the file")
                old = self.head()
                self.run_git("rm", "-q", name)
                self.commit("C removes it")
                self.base = self.head()
                self.run_git("checkout", "-q", "-b", "topic", fork)
                self.write("topic.md", "Topic\n")
                self.commit("Topic work")
                self.run_git("merge", "-q", "--no-edit", old)
                if label != "exact entry":
                    self.write(name, text)
                    os.chmod(self.root / name, mode)
                    self.run_git("add", name)
                    self.run_git("commit", "-q", "--amend", "--no-edit")
                self.assertEqual(
                    len(self.run_git("log", "-1", "--format=%P").split()), 2
                )
                findings = self.check()["findings"]
                self.assertEqual([f["location"] for f in findings], expected)

    def test_historical_gitlinks_gain_no_acceptance(self):
        # A gitlink only an old base-side parent holds is refused when a
        # merge keeps it; the same gitlink in the current base is accepted.
        target = self.base

        blob = (
            subprocess.run(
                ["git", "-C", str(self.root), "hash-object", "-w", "--stdin"],
                input=b"Topic\n",
                capture_output=True,
                check=True,
            )
            .stdout.decode()
            .strip()
        )

        def commit(files, *parents):
            rows = "".join(
                (
                    f"100644 blob {blob}\t{name}\n"
                    if name.endswith(".md")
                    else f"160000 commit {target}\t{name}\n"
                )
                for name in sorted(files)
            )
            tree = (
                subprocess.run(
                    ["git", "-C", str(self.root), "mktree"],
                    input=rows.encode(),
                    capture_output=True,
                    check=True,
                )
                .stdout.decode()
                .strip()
            )
            args = ["commit-tree", tree, "-m", "Commit"]
            for parent in parents:
                args += ["-p", parent]
            return self.run_git(*args)

        fork = commit({"keep"}, target)
        old = commit({"keep", "legacy"}, fork)
        for current, refused in ((False, True), (True, False)):
            with self.subTest(current=current):
                self.base = commit(
                    {"keep", "legacy"} if current else {"keep"}, old
                )
                topic = commit({"keep", "topic.md"}, fork)
                head = commit({"keep", "legacy", "topic.md"}, topic, old)
                self.run_git("update-ref", "HEAD", head)
                if refused:
                    with self.assertRaises(gate.IncompleteScan):
                        self.check()
                else:
                    self.assertEqual(self.check()["findings"], [])

    def test_one_parent_executable_bit_on_base_history_bytes(self):
        # A topic makes an old base-history file executable after the
        # current base removed or cleaned it: no new content finding, and
        # the skip vouches for nothing later. Real changes stay checked.
        secret = "T" + "54321\n"

        def start(state):
            self.setUp()
            self.write("legacy.md", secret)
            self.commit("Old base")
            old = self.head()
            if state == "removed":
                self.run_git("rm", "-q", "legacy.md")
            elif state == "cleaned":
                self.write("legacy.md", "Current clean text\n")
            else:
                self.write("other.md", "Base text\n")
            self.commit("Current base")
            self.base = self.head()
            self.run_git("checkout", "-q", "-b", "topic", old)
            return old

        def chmod(mode=0o755, text=None):
            if text is not None:
                self.write("legacy.md", text)
            os.chmod(self.root / "legacy.md", mode)
            self.commit("Topic edit")

        for state in ("removed", "cleaned", "retained"):
            with self.subTest(case="executable only", state=state):
                start(state)
                chmod()
                result = self.check()
                self.assertEqual(result["findings"], [])
                self.assertEqual(result["blobs"], 0)
        with self.subTest(case="one byte plus chmod"):
            start("removed")
            chmod(text="T" + "54322\n")
            self.assertEqual(len(self.check()["findings"]), 1)
        with self.subTest(case="restore over cleaned bytes"):
            start("cleaned")
            self.run_git("checkout", "-q", "-B", "topic", self.base)
            self.write("legacy.md", secret)
            self.commit("Restore the old bytes")
            self.assertEqual(len(self.check()["findings"]), 1)
        with self.subTest(case="add back a removed path"):
            start("removed")
            self.run_git("checkout", "-q", "-B", "topic", self.base)
            self.write("legacy.md", secret)
            self.commit("Add it back")
            self.assertEqual(len(self.check()["findings"]), 1)
        for state, expected in (("removed", 1), ("retained", 0)):
            with self.subTest(case="copy stale bytes", state=state):
                start(state)
                self.write("copy.md", secret)
                self.commit("Copy the old bytes")
                self.assertEqual(len(self.check()["findings"]), expected)
        with self.subTest(case="old prose as a symlink target"):
            start("removed")
            self.write("prose.md", "/".join(["", "home", "runner!"]))
            self.commit("Prose")
            self.base = self.head()
            os.symlink("/".join(["", "home", "runner!"]), self.root / "link")
            self.commit("Link")
            self.assertEqual(len(self.check()["findings"]), 1)
        # Integrating the current base after the executable-only edit.
        with self.subTest(case="cleaned base merged in"):
            start("cleaned")
            chmod()
            self.run_git("merge", "-q", "--no-edit", self.base)
            self.assertEqual(
                (self.root / "legacy.md").read_text(), "Current clean text\n"
            )
            self.assertEqual(self.check()["findings"], [])
        for resolution, expected in (("delete", []), ("retain", 1)):
            with self.subTest(case="removed base merged in", res=resolution):
                start("removed")
                chmod()
                subprocess.run(
                    [
                        "git",
                        "-C",
                        str(self.root),
                        "merge",
                        "--no-edit",
                        self.base,
                    ],
                    capture_output=True,
                )
                if resolution == "delete":
                    self.run_git("rm", "-q", "legacy.md")
                else:
                    self.run_git("add", "legacy.md")
                self.run_git("commit", "-q", "--no-edit")
                self.assertEqual(
                    len(self.run_git("log", "-1", "--format=%P").split()), 2
                )
                findings = self.check()["findings"]
                if resolution == "delete":
                    self.assertEqual(findings, expected)
                else:
                    self.assertEqual(len(findings), expected, findings)
                    self.assertTrue(
                        findings[0]["location"].startswith("legacy.md @ ")
                    )

    def test_current_symlink_bytes_may_be_reused_as_file_contents(self):
        target = "T" + "54321"
        os.symlink(target, self.root / "current-link")
        self.commit("Base keeps a symlink")
        self.base = self.head()
        # The same bytes as an ordinary file are already present in the
        # current base, so no new content finding is due.
        (self.root / "copy.md").write_bytes(target.encode())
        self.commit("Reuse the bytes as a file")
        self.assertEqual(self.check()["findings"], [])
        # The reverse is still strict: current file bytes as a new symlink.
        home = "/".join(["", "home", "runner!"])
        (self.root / "prose.md").write_bytes(home.encode())
        self.commit("Base keeps the bytes as a file")
        self.base = self.head()
        os.symlink(home, self.root / "new-link")
        self.commit("Reuse the bytes as a symlink target")
        findings = self.check()["findings"]
        self.assertEqual(len(findings), 1)
        self.assertTrue(findings[0]["location"].startswith("new-link @ "))

    def test_merge_changes_to_unsupported_modes_fail_closed(self):
        # A merge keeps a gitlink from a side parent where the current base
        # has a regular file; a known target and name must not skip refusal.
        target = self.base

        def tree(files):
            rows = []
            for name, (mode, value) in sorted(files.items()):
                if mode == "160000":
                    rows.append(f"160000 commit {value}\t{name}\n")
                else:
                    blob = (
                        subprocess.run(
                            [
                                "git",
                                "-C",
                                str(self.root),
                                "hash-object",
                                "-w",
                                "--stdin",
                            ],
                            input=value.encode(),
                            capture_output=True,
                            check=True,
                        )
                        .stdout.decode()
                        .strip()
                    )
                    rows.append(f"{mode} blob {blob}\t{name}\n")
            return (
                subprocess.run(
                    ["git", "-C", str(self.root), "mktree"],
                    input="".join(rows).encode(),
                    capture_output=True,
                    check=True,
                )
                .stdout.decode()
                .strip()
            )

        def commit(files, *parents):
            args = ["commit-tree", tree(files), "-m", "Commit"]
            for parent in parents:
                args += ["-p", parent]
            return self.run_git(*args)

        for alias, name in ((True, "legacy"), (False, "legacy"), (True, "new")):
            with self.subTest(alias=alias, name=name):
                old = commit({name: ("160000", target)}, target)
                base_files = {}
                if name == "legacy":
                    base_files[name] = ("100644", "Clean text\n")
                if alias:
                    base_files["alias"] = ("160000", target)
                self.base = commit(base_files, old)
                side_files = {
                    name: ("160000", target),
                    "other.md": ("100644", "Side text\n"),
                }
                side = commit(side_files, old)
                head = commit({**base_files, **side_files}, self.base, side)
                self.run_git("update-ref", "HEAD", head)
                with self.assertRaises(gate.IncompleteScan):
                    self.check()
        # Control: a gitlink the current base already holds, kept unchanged
        # by the merge, is not a change and is accepted.
        old = commit({}, target)
        self.base = commit({"legacy": ("160000", target)}, old)
        side = commit({"other.md": ("100644", "Side text\n")}, old)
        head = commit(
            {
                "legacy": ("160000", target),
                "other.md": ("100644", "Side text\n"),
            },
            self.base,
            side,
        )
        self.run_git("update-ref", "HEAD", head)
        self.assertEqual(self.check()["findings"], [])

    def test_supported_tag_message_uses_message_rules(self):
        z = "0" * 40
        plain = (
            "author A <a@example.invalid> 1 +0000\n"
            "committer C <c@example.invalid> 1 +0000\n"
        )
        doi = "https://doi.org/10.1017/S0308210500015080"
        url = "https://www.math.cmu.edu/users/mubayi/papers/no-singleton.pdf"

        def tag(message, after=""):
            return (
                "mergetag object " + z + "\n type commit\n tag v1\n"
                " tagger T <t@example.invalid> 1 +0000\n \n "
                + message
                + "\n"
                + after
            )

        def lines(headers, body="Msg\n"):
            raw = ("tree " + z + "\n" + plain + headers + "\n" + body).encode()
            return sorted(
                f["line"] for f in gate.scan_commit(raw, z, None, ("A", "C"))
            )

        self.assertEqual(lines(tag(doi + " " + url)), [])
        self.assertEqual(lines(tag("first\n " + doi)), [])
        self.assertEqual(lines("", doi + " " + url + "\n"), [])
        strict = {
            "tag name": "mergetag object "
            + z
            + "\n type commit\n tag "
            + doi
            + "\n \n m\n",
            "unknown header": "x-meta " + doi + "\n",
            "unsupported tag": "mergetag not-a-tag\n \n " + doi + "\n",
            "signature": tag(
                "m",
                " -----BEGIN PGP SIGNATURE-----\n Comment: "
                + doi
                + "\n -----END PGP SIGNATURE-----\n",
            ),
            "after signature": tag(
                "m",
                " -----BEGIN PGP SIGNATURE-----\n x\n"
                " -----END PGP SIGNATURE-----\n " + doi + "\n",
            ),
            "later bad field": "mergetag object " + z + "\n type commit\n"
            " tag v1\n x-bad y\n \n " + doi + "\n",
            "neighbor token": tag(doi + " " + "P" + "1234567"),
        }
        for label, headers in strict.items():
            with self.subTest(label=label):
                self.assertEqual(len(lines(headers)), 1)

    def test_literal_filename_is_redacted_in_blob_locations(self):
        name = "/".join(["docs", "home", "runner!"])
        self.write(name, "Ticket " + "D" + "12345\n")
        self.commit("Add literal-name fixture")
        report = self.check()
        rules = sorted(f["rule"] for f in report["findings"])
        self.assertEqual(rules, ["internal-reference", "personal-workspace"])
        self.assertNotIn("runner", json.dumps(report))

    def test_header_values_are_literal(self):
        home = "/".join(["", "home", ""])
        mail = " <a@example.invalid> 1 +0000\n"

        def commit(headers, body="Msg\n"):
            return ("tree " + "0" * 40 + "\n" + headers + "\n" + body).encode()

        def tag(tagger, message):
            return (
                "mergetag object " + "0" * 40 + "\n type commit\n tag v1\n"
                " tagger " + tagger + mail + " \n " + message + "\n"
            )

        plain = "author A" + mail + "committer C" + mail
        cases = (
            # (headers, Git's author and committer names, body, lines)
            (
                "author " + home + "runner!" + mail + "committer C" + mail,
                (home + "runner!", "C"),
                "Msg\n",
                [2],
            ),
            (
                "author "
                + home
                + "runner. Example"
                + mail
                + "committer "
                + home
                + "runner!"
                + mail,
                (home + "runner. Example", home + "runner!"),
                "Msg\n",
                [2, 3],
            ),
            (
                "author " + home + "Example" + mail + "committer C" + mail,
                (home + "Example", "C"),
                "Msg\n",
                [2],
            ),
            (
                "author "
                + home
                + "runner"
                + mail
                + "committer "
                + home
                + "runneradmin"
                + mail,
                (home + "runner", home + "runneradmin"),
                "Msg\n",
                [],
            ),
            (
                plain + tag(home + "runner!", "Tag message"),
                ("A", "C"),
                "Msg\n",
                [7],
            ),
            (
                plain + tag(home + "runner", "See " + home + "runner. ok"),
                ("A", "C"),
                "Msg\n",
                [],
            ),
            (
                plain + "x-unknown " + home + "runner!\n",
                ("A", "C"),
                "Msg\n",
                [4],
            ),
            (plain, ("A", "C"), "See " + home + "runner. Next.\n", []),
            # The email slot of an identity line is literal too.
            (
                "author Example <"
                + home
                + "runner!> 1 +0000\ncommitter C"
                + mail,
                ("Example", "C"),
                "Msg\n",
                [2],
            ),
            (
                "author Example <"
                + home
                + "runner> 1 +0000\ncommitter C"
                + mail,
                ("Example", "C"),
                "Msg\n",
                [],
            ),
            # The email slot ends at its ">"; other punctuation is data.
            (
                "author Example <"
                + home
                + "runner?x> 1 +0000\ncommitter C"
                + mail,
                ("Example", "C"),
                "Msg\n",
                [2],
            ),
            # An embedded tag message is prose; its signature is opaque data,
            # like a top-level signature.
            (
                plain
                + tag("T", "See " + home + "runner!")
                + " -----BEGIN PGP SIGNATURE-----\n Comment: "
                + home
                + "runner!\n abcd\n -----END PGP SIGNATURE-----\n",
                ("A", "C"),
                "Msg\n",
                [11],
            ),
            (
                plain
                + "gpgsig -----BEGIN PGP SIGNATURE-----\n Comment: "
                + home
                + "runner!\n -----END PGP SIGNATURE-----\n",
                ("A", "C"),
                "Msg\n",
                [5],
            ),
            # Only a supported embedded tag has a tagger identity; in any
            # other shape the tagger line is whole literal data.
            (
                plain
                + "mergetag not-a-tag\n tagger T <"
                + home
                + "runner> 1 +0000 >\n \n m\n",
                ("A", "C"),
                "Msg\n",
                [5],
            ),
            (
                plain
                + "mergetag object "
                + "0" * 40
                + "\n type commit\n tag v1\n tagger T <"
                + home
                + "runner> 1 +0000\n x-extra y\n \n m\n",
                ("A", "C"),
                "Msg\n",
                [7],
            ),
            (
                plain
                + "mergetag object "
                + "0" * 40
                + "\n type commit\n tag v1\n tagger T <"
                + home
                + "runner> 1 +0000\n \n m\n",
                ("A", "C"),
                "Msg\n",
                [],
            ),
            # Only a supported embedded tag header grants prose to its message.
            (
                plain + "mergetag not-a-tag\n \n " + home + "runner!\n",
                ("A", "C"),
                "Msg\n",
                [6],
            ),
            (
                plain
                + "mergetag object "
                + "0" * 40
                + "\n tag v1\n type commit\n \n "
                + home
                + "runner!\n",
                ("A", "C"),
                "Msg\n",
                [8],
            ),
            (
                plain
                + "mergetag object "
                + "0" * 40
                + "\n type commit\n tag v1\n x-extra y\n \n "
                + home
                + "runner!\n",
                ("A", "C"),
                "Msg\n",
                [9],
            ),
            # Header keys and lines without a space are covered too.
            (
                plain + "x-profile" + home + "runner!\n",
                ("A", "C"),
                "Msg\n",
                [4],
            ),
            (
                plain + "x-profile" + home + "runner! opaque\n",
                ("A", "C"),
                "Msg\n",
                [4],
            ),
        )
        for headers, identity, body, lines in cases:
            with self.subTest(headers=headers, body=body):
                findings = gate.scan_commit(
                    commit(headers, body), "0" * 40, None, identity
                )
                self.assertEqual(sorted(f["line"] for f in findings), lines)
                for finding in findings:
                    self.assertEqual(finding["rule"], "personal-workspace")
        # Git's parsed names must agree with the raw identity lines.
        for headers, identity in (
            (plain, ("B", "C")),
            ("author NoBracket 1 +0000\ncommitter C" + mail, ("", "C")),
            ("committer C" + mail, ("A", "C")),
        ):
            with self.subTest(headers=headers):
                with self.assertRaises(gate.IncompleteScan):
                    gate.scan_commit(commit(headers), "0" * 40, None, identity)

    def test_cli_url_path_bypass_controls_in_every_scope(self):
        tail = "/".join(["Users", "Example", "work", "notes.txt"])
        home = "/".join(["", "home", "Example", "private.txt"])
        for text in (
            "https://example.edu/C:/./" + tail,
            "https://example.edu/C:/folder/../" + tail,
            "https://example.edu/%43%3A/" + tail,
            "https://example.edu:65536" + home,
            "https://@" + home,
            "https://:" + home,
            "http://localhost" + home,
            "https://host.alt" + home,
            "https://www.example.com" + home,
        ):
            with self.subTest(text=text):
                self.base = self.head()
                self.write("notes.md", text + "\n")
                self.commit("Cite " + text)
                metadata = self.root / "pr.json"
                metadata.write_text(json.dumps({"title": text, "body": text}))
                run = subprocess.run(
                    [
                        sys.executable,
                        gate.__file__,
                        "--repo-root",
                        str(self.root),
                        "--base",
                        self.base,
                        "--head",
                        self.head(),
                        "--metadata",
                        str(metadata),
                    ],
                    capture_output=True,
                    text=True,
                )
                metadata.unlink()
                self.assertEqual(run.returncode, 1, run.stdout)
                report = json.loads(run.stdout)
                self.assertEqual(len(report["findings"]), 4)
                self.assertNotIn("Example", run.stdout + run.stderr)

    def test_cli_control_characters_end_url_paths(self):
        url = "https://www.math.cmu.edu/users/mubayi"
        home = "/".join(["", "home", "Example", "private.txt"])
        for code in (0x00, 0x07, 0x1B, 0x7F, 0x85, 0x9B):
            with self.subTest(code=hex(code)):
                self.base = self.head()
                text = url + chr(code) + home
                self.write("notes.md", text + "\n")
                (self.root / "data.bin").write_bytes(
                    b"\x00BIN\x00" + text.encode() + b"\x00\n"
                )
                self.commit("Add notes")
                metadata = self.root / "pr.json"
                metadata.write_text(json.dumps({"title": text, "body": text}))
                run = subprocess.run(
                    [
                        sys.executable,
                        gate.__file__,
                        "--repo-root",
                        str(self.root),
                        "--base",
                        self.base,
                        "--head",
                        self.head(),
                        "--metadata",
                        str(metadata),
                    ],
                    capture_output=True,
                    text=True,
                )
                metadata.unlink()
                self.assertEqual(run.returncode, 1, run.stdout)
                report = json.loads(run.stdout)
                where = sorted(
                    f["location"].split(" @ ")[0] for f in report["findings"]
                )
                self.assertEqual(
                    where, ["PR body", "PR title", "data.bin", "notes.md"]
                )
                # A NUL makes the text file binary too; both are scanned.
                binary = 2 if code == 0 else 1
                self.assertEqual(report["binary_files"], binary)
                self.assertNotIn("Example", run.stdout + run.stderr)

    def test_cli_distinguishes_public_and_local_url_paths(self):
        home = "/".join(["", "home", "alice", "notes.pdf"])
        cases = (
            ("public.md", "https://www.math.cmu.edu" + home, 0),
            ("local.md", "http://localhost:8080" + home, 1),
            ("loopback.md", "http://[::1]" + home, 1),
        )
        for name, text, expected in cases:
            with self.subTest(name=name):
                self.base = self.head()
                self.write(name, text + "\n")
                self.commit("Add " + name)
                run = subprocess.run(
                    [
                        sys.executable,
                        gate.__file__,
                        "--repo-root",
                        str(self.root),
                        "--base",
                        self.base,
                        "--head",
                        self.head(),
                    ],
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(run.returncode, expected, run.stdout)
                self.assertNotIn("alice", run.stdout + run.stderr)
                self.assertNotIn("localhost", run.stdout + run.stderr)

    def test_public_url_paths_only_in_recognized_scopes(self):
        url = PUBLIC_URLS[0]
        self.write("refs.md", url + "\n")
        self.commit("Cite " + url)
        self.assertEqual(self.check()["findings"], [])
        self.assertEqual(
            self.check({"title": url, "body": url})["findings"], []
        )
        self.assertEqual(
            len(self.check({"branch": "fix/" + url})["findings"]), 1
        )
        self.base = self.head()
        (self.root / "link").symlink_to(url)
        self.commit("Add link")
        findings = self.check()["findings"]
        self.assertEqual([f["rule"] for f in findings], ["personal-workspace"])
        self.assertTrue(findings[0]["location"].startswith("link @ "))
        self.base = self.head()
        self.run_git("config", "user.name", "Example " + url)
        self.commit("Ordinary change")
        self.assertEqual(len(self.check()["findings"]), 2)

    def check_public(self, *public):
        return gate.check_range(self.root, self.base, self.head(), None, public)

    def test_public_tip_excludes_legacy_topic_history(self):
        self.write("notes.md", private_ref() + "\n")
        self.commit("Topic work\n\nProvenance " + private_ref("T"))
        published = self.head()
        self.write("notes.md", "Public notes\n")
        self.commit("Remove provenance from notes")
        self.assertTrue(self.check()["findings"])
        result = self.check_public(published)
        self.assertEqual((result["commits"], result["findings"]), (1, []))

    def test_merging_public_main_and_topic_does_not_rescan(self):
        fork = self.head()
        self.write("main.md", private_ref("P") + "\n")
        self.commit("Main legacy\n\nSee " + private_ref())
        main = self.head()
        self.run_git("checkout", "-q", "-b", "topic", fork)
        self.write(private_ref("T") + ".md", "Topic legacy\n")
        self.commit("Topic legacy")
        topic = self.head()
        self.run_git("merge", "-q", "--no-edit", main)
        self.base = fork
        self.assertTrue(self.check()["findings"])
        result = self.check_public(main, topic)
        self.assertEqual((result["commits"], result["findings"]), (1, []))
        self.assertEqual(self.check_public(main)["commits"], 2)
        self.assertTrue(self.check_public(main)["findings"])

    def published_removal(self):
        """Clean base, F adds a legacy file, public R removes it."""
        self.write("base.md", "Public base")
        self.commit("Clean base")
        self.base = self.head()
        self.write("legacy.md", private_ref())
        self.commit("Topic adds legacy file")
        added = self.head()
        (self.root / "legacy.md").unlink()
        self.commit("Topic removes legacy file")
        return added, self.head()

    def test_public_tip_side_parent_restoration_is_checked(self):
        added, removed = self.published_removal()
        self.run_git("checkout", "-q", "-b", "side", added)
        self.write("unrelated.md", "One unrelated change")
        self.commit("One unrelated local side commit")
        self.run_git("checkout", "-q", "-")
        self.assertEqual(self.head(), removed)
        self.run_git("merge", "-q", "--no-ff", "--no-commit", "side")
        self.write("legacy.md", private_ref())
        self.commit("Merge local side and keep legacy file")
        result = self.check_public(removed)
        self.assertEqual(result["commits"], 2)
        self.assertEqual(len(result["findings"]), 1)
        self.assertEqual(len(self.check()["findings"]), 1)

    def test_public_tip_direct_restoration_is_checked(self):
        _, removed = self.published_removal()
        self.write("legacy.md", private_ref())
        self.commit("Restore legacy file")
        result = self.check_public(removed)
        self.assertEqual((result["commits"], len(result["findings"])), (1, 1))

    def test_public_tip_names_are_not_re_reported_on_edit(self):
        legacy = private_ref() + ".md"
        self.write(legacy, "Old public text\n")
        self.write("cite-" + private_ref("P") + ".md", PUBLIC_DOIS[0])
        self.commit("Published files")
        published = self.head()
        self.write(legacy, "New public text\n")
        self.commit("Edit content only")
        result = self.check_public(published)
        self.assertEqual((result["commits"], result["findings"]), (1, []))
        # A symlink under a public name still has a strict target.
        link = "cite-" + private_ref("P") + ".md"
        (self.root / link).unlink()
        (self.root / link).symlink_to(PUBLIC_DOIS[0])
        self.commit("Turn the public citation file into a link")
        findings = self.check_public(published)["findings"]
        self.assertEqual(len(findings), 1)
        self.assertTrue(findings[0]["location"].startswith("[redacted]"))
        self.assertEqual(findings[0]["rule"], "internal-reference")
        # New and restored legacy names still block.
        published = self.head()
        self.write(private_ref("T") + ".md", "New file\n")
        self.commit("Add a new legacy name")
        self.assertEqual(len(self.check_public(published)["findings"]), 1)

    def test_restored_legacy_name_still_blocks(self):
        name = private_ref("T") + ".md"
        self.write(name, "Text\n")
        self.commit("Add legacy name")
        (self.root / name).unlink()
        self.commit("Remove legacy name")
        published = self.head()
        self.write(name, "Text\n")
        self.commit("Restore legacy name")
        findings = self.check_public(published)["findings"]
        self.assertEqual([f["location"][:10] for f in findings], ["filename i"])

    def side_graph(self, name, make, base_copy=None, side_commit=True):
        """Base, F adds an entry, public R removes it, local side keeps it."""
        self.write("base.md", "Public base")
        if base_copy is not None:
            self.write("base-copy.md", base_copy)
        self.commit("Clean base")
        self.base = self.head()
        make(name)
        self.commit("Topic adds entry")
        added = self.head()
        (self.root / name).unlink()
        self.commit("Topic removes entry")
        removed = self.head()
        source = added
        if side_commit:
            self.run_git("checkout", "-q", "-b", "side", added)
            self.write("unrelated.md", "One unrelated change")
            self.commit("One unrelated local side commit")
            self.run_git("checkout", "-q", "-")
            source = "side"
        self.assertEqual(self.head(), removed)
        self.run_git("merge", "-q", "--no-ff", "--no-commit", source)
        if not (self.root / name).is_symlink():
            make(name)
        self.commit("Merge and keep the entry")
        return removed

    def link_maker(self, target):
        def make(name):
            path = self.root / name
            if path.is_symlink() or path.exists():
                path.unlink()
            path.symlink_to(target)

        return make

    def text_maker(self, text):
        return lambda name: self.write(name, text)

    def test_side_parent_entries_are_new_relative_to_public_tips(self):
        prose = "Ordinary public prose"
        cases = {
            "filename": (private_ref("T") + ".md", self.text_maker(prose)),
            "symlink": ("legacy-link", self.link_maker(PUBLIC_DOIS[0])),
        }
        for kind, (name, make) in cases.items():
            for copy in (None, prose if kind == "filename" else PUBLIC_DOIS[0]):
                for side in (True, False):
                    with self.subTest(
                        kind=kind, base_copy=bool(copy), side=side
                    ):
                        self.setUp()
                        removed = self.side_graph(name, make, copy, side)
                        result = self.check_public(removed)
                        self.assertEqual(len(result["findings"]), 1, result)
                        # Without a side commit, F is an ancestor of R and
                        # the restore is an ordinary new commit.
                        self.assertTrue(self.check()["findings"])

    def test_public_history_boundary_controls(self):
        legacy = private_ref() + ".md"
        # Base entries stay behind the declared base boundary.
        self.write(legacy, "Base text\n")
        self.link_maker(PUBLIC_DOIS[0])("public-link")
        self.commit("Base with a legacy name and a public link")
        self.base = fork = self.head()
        self.run_git("checkout", "-q", "-b", "public-other", fork)
        (self.root / legacy).unlink()
        (self.root / "public-link").unlink()
        self.write("other.md", "Other public branch\n")
        self.commit("Public branch without the base entries")
        other = self.head()
        self.run_git("checkout", "-q", "-b", "work", fork)
        self.write("work.md", "Clean work\n")
        self.commit("Work on top of base")
        self.assertEqual(self.check_public(other)["findings"], [])
        # Entries a public side parent shares with the public tip (the base
        # link and name) are public; the removed blob it replaces is not kept.
        self.run_git("checkout", "-q", "-b", "topic", fork)
        self.write("legacy.md", private_ref("P") + "\n")
        self.commit("Topic adds a legacy blob")
        added = self.head()
        (self.root / "legacy.md").unlink()
        self.commit("Topic removes it")
        removed = self.head()
        self.run_git("checkout", "-q", "-b", "side", added)
        self.write("legacy.md", "Clean replacement\n")
        self.commit("Side changes the removed entry")
        self.base = fork
        result = self.check_public(removed)
        self.assertEqual((result["commits"], result["findings"]), (1, []))

    def test_two_public_tips_restore_from_other_tip_history(self):
        legacy = private_ref("T") + ".md"
        make_link = self.link_maker(PUBLIC_DOIS[0])
        self.write("base.md", "Public base\n")
        self.commit("Clean base")
        self.base = fork = self.head()
        self.run_git("checkout", "-q", "-b", "cleaned", fork)
        self.write(legacy, "Ordinary prose\n")
        make_link("legacy-link")
        self.commit("Add a legacy name and link")
        old = self.head()
        (self.root / legacy).unlink()
        (self.root / "legacy-link").unlink()
        self.commit("Remove them")
        cleaned = self.head()
        self.run_git("checkout", "-q", "-b", "main-line", fork)
        self.write("main.md", "Main work\n")
        self.commit("Main public work")
        main = self.head()
        # Negative control: merging the other public tip itself is public.
        self.run_git("checkout", "-q", "-b", "merge-tip", main)
        self.run_git("merge", "-q", "--no-edit", cleaned)
        self.assertEqual(self.check_public(main, cleaned)["findings"], [])
        # Positive: a normal merge of an older commit from that tip's history
        # restores entries neither current public tree contains.
        self.run_git("checkout", "-q", "-b", "merge-old", main)
        self.run_git("merge", "-q", "--no-edit", old)
        self.assertTrue((self.root / "legacy-link").is_symlink())
        findings = self.check_public(main, cleaned)["findings"]
        self.assertEqual(len(findings), 2)

    def test_direct_restores_of_names_and_links_block(self):
        cases = {
            private_ref("T") + ".md": self.text_maker("Ordinary prose"),
            "legacy-link": self.link_maker(PUBLIC_DOIS[0]),
        }
        for name, make in cases.items():
            with self.subTest(name=name):
                self.setUp()
                make(name)
                self.commit("Add entry")
                (self.root / name).unlink()
                self.commit("Remove entry")
                published = self.head()
                make(name)
                self.commit("Restore entry")
                findings = self.check_public(published)["findings"]
                self.assertEqual(len(findings), 1)

    def test_public_entries_and_renames_relative_to_public_tips(self):
        legacy = private_ref() + ".md"
        self.write(legacy, "Public text\n")
        self.write("clean.md", "Clean text\n")
        self.link_maker(PUBLIC_DOIS[0])("public-link")
        self.commit("Published entries")
        published = self.head()
        self.write("clean.md", "Edited clean text\n")
        self.commit("Ordinary edit")
        self.assertEqual(self.check_public(published)["findings"], [])
        self.run_git("mv", legacy, "renamed-clean.md")
        self.commit("Rename the legacy name away")
        self.assertEqual(self.check_public(published)["findings"], [])
        self.run_git("mv", "clean.md", private_ref("P") + ".md")
        self.commit("Rename to a new legacy name")
        findings = self.check_public(published)["findings"]
        self.assertEqual([f["location"][:10] for f in findings], ["filename i"])

    def test_new_findings_still_block_after_public_tips(self):
        self.write("cite.md", PUBLIC_DOIS[0])
        self.commit("Add public citation")
        published = self.head()
        self.assertEqual(self.check_public(published)["findings"], [])
        cases = (
            ("message", lambda: None, "New\n\nSee " + private_ref("T")),
            ("blob", lambda: self.write("n.md", private_ref()), "Add n"),
            ("path", lambda: self.write(private_ref("P") + ".md", "x"), "p"),
            (
                "symlink",
                lambda: (self.root / "link").symlink_to(PUBLIC_DOIS[0]),
                "Point a link at the public citation bytes",
            ),
        )
        for name, change, message in cases:
            with self.subTest(case=name):
                change()
                self.commit(message)
                findings = self.check_public(published)["findings"]
                self.assertEqual(len(findings), 1)
                published = self.head()

    def test_no_public_tips_keeps_default_range(self):
        self.write("notes.md", private_ref() + "\n")
        self.commit("First push " + private_ref("T"))
        self.assertEqual(self.check(), self.check_public())
        self.assertEqual(len(self.check()["findings"]), 2)

    def test_invalid_public_tips_fail_closed(self):
        self.write("notes.md", "Public notes\n")
        self.commit("Add notes")
        self.run_git("tag", "-a", "-m", "Release", "v1")
        tree = self.run_git("rev-parse", "HEAD^{tree}")
        blob = self.run_git("rev-parse", "HEAD:notes.md")
        tag = self.run_git("rev-parse", "v1")
        for tip in ("HEAD", "abc", "0" * 40, tree, blob, tag):
            with self.subTest(tip=tip), self.assertRaises(gate.IncompleteScan):
                self.check_public(tip)
        args = ["--repo-root", str(self.root), "--base", self.base]
        args += ["--head", self.head()]
        with contextlib.redirect_stdout(io.StringIO()):
            with contextlib.redirect_stderr(io.StringIO()) as err:
                self.assertEqual(gate.main(args + ["--public", tree]), 2)
                clean = {"findings": [], "findings_truncated": False}
                with (
                    patch.dict(os.environ, {"GH_TOKEN": "unused"}),
                    patch.object(gate, "check_pr", return_value=clean),
                ):
                    pr = ["--github-repository", "o/r", "--pr", "1"]
                    self.assertEqual(gate.main(pr), 0)
                    self.assertEqual(
                        gate.main(pr + ["--public", self.head()]), 2
                    )
                self.assertEqual(gate.main(args + ["--public", self.head()]), 0)
        self.assertNotIn(tree, err.getvalue())


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
