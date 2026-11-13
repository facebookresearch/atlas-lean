"""An article's statement is its declaration's own docstring, never source above it."""

from __future__ import annotations

import unittest

from scripts import generate_wiki as wiki


def doc(source: str) -> str | None:
    lines = source.strip("\n").splitlines()
    return wiki.docstring_before(lines, len(lines) - 1)


class DocstringBefore(unittest.TestCase):
    def test_docstring(self) -> None:
        self.assertEqual(doc("/-- A group. -/\ndef G := 1"), "A group.")

    def test_multiline_docstring_and_attribute(self) -> None:
        self.assertEqual(doc("/-- First line.\n\nSecond paragraph. -/\n@[simp]\ntheorem t : True := trivial"),
                         "First line.\n\nSecond paragraph.")

    def test_nested_comment_inside_docstring(self) -> None:
        self.assertEqual(doc("/-- Uses /- nested -/ text. -/\ndef G := 1"), "Uses /- nested -/ text.")

    def test_section_heading_is_not_a_docstring(self) -> None:
        # The scan used to run up from the heading to the earlier docstring, publishing the code between.
        source = "/-- Push budget. -/\ndef pushBound := 1\n\ntheorem p : True := trivial\n\n/-! ## Monotonicity -/\n\ntheorem eval_mono : True := trivial"
        self.assertIsNone(doc(source))

    def test_plain_comment_is_not_a_docstring(self) -> None:
        self.assertIsNone(doc("/-- Earlier. -/\ndef a := 1\n/- A remark. -/\ndef b := 2"))

    def test_multiline_heading_is_not_a_docstring(self) -> None:
        self.assertIsNone(doc("/-- Earlier. -/\ndef a := 1\n/-!\n## Section\n\nProse.\n-/\ndef b := 2"))

    def test_no_comment(self) -> None:
        self.assertIsNone(doc("def a := 1\n\ndef b := 2"))


class SafeMathMarkdown(unittest.TestCase):
    def test_plain_text_math_is_not_a_link(self) -> None:
        self.assertEqual(wiki.safe_math_markdown("⟨f,g⟩ = ∑ [x^{λ+δ}](a_δ f) [x^{λ+δ}](a_δ g)."),
                         "⟨f,g⟩ = ∑ [x^{λ+δ}]&#40;a_δ f) [x^{λ+δ}]&#40;a_δ g).")

    def test_links_stay_links(self) -> None:
        text = "See [the paper](https://arxiv.org/abs/1), [above](#proof) and [the group](../groups/group.md#def)."
        self.assertEqual(wiki.safe_math_markdown(text), text)

    def test_math_spans_are_left_to_the_math_renderer(self) -> None:
        self.assertEqual(wiki.safe_math_markdown("$[a](b) <c$"), "$[a](b) \\lt c$")


class Citations(unittest.TestCase):
    def _page(self, citations: list[str]) -> str:
        target = wiki.Target(
            book="MathlibExt", idx=0, title="Result", slug="result", location="Geometry", description="A result.",
            declaration="theorem", lean="Falconer.result", statement=True, proof=True, names=["Falconer.result"],
            citations=citations, module=("MathlibExt", "Geometry", "Falconer"), path=wiki.ROADMAP / "Geometry/result.md",
        )
        return wiki.render_target(target, None)

    def test_an_article_without_citations_lists_no_sources(self) -> None:
        page = self._page([])
        self.assertNotIn("## Sources", page)
        self.assertNotIn("origin:", page)

    def test_a_plain_text_citation_is_listed_without_an_origin(self) -> None:
        page = self._page(["W. Rudin, Principles of Mathematical Analysis, Theorem 3.4."])
        self.assertIn("## Sources\n\n- W. Rudin, Principles of Mathematical Analysis, Theorem 3.4.\n", page)
        self.assertNotIn("origin:", page)

    def test_a_linked_citation_makes_the_article_cited(self) -> None:
        page = self._page(["[O. Gorodetsky, *Rigidity of averages*](https://arxiv.org/abs/2608.05191)."])
        self.assertIn("origin: cited\n", page)

    def test_link_syntax_in_code_is_no_link(self) -> None:
        self.assertNotIn("origin:", self._page(["INTEGERS 25 (2025), Section 1 (definition of `S^[m](n)`)."]))

    def test_internal_ids_alone_are_no_citation(self) -> None:
        doc = ("A group.\n\nSource: concept `jis_sem_0d5596f0982681bcb579a894`; source statements "
               "`jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`.")
        self.assertEqual(wiki.split_docstring(doc), ("A group.", []))

    def test_a_citation_of_code_alone_stays(self) -> None:
        self.assertEqual(wiki.split_docstring("A group.\n\nSource: `Mathlib.GroupTheory.Sylow`."),
                         ("A group.", ["`Mathlib.GroupTheory.Sylow`."]))

    def test_a_citation_that_names_a_work_keeps_its_ids(self) -> None:
        citation = "Schork, lines 285-288 (concept `jis_sem_0d5596f0982681bcb579a894`)."
        self.assertEqual(wiki.split_docstring(f"A group.\n\nSource: {citation}"), ("A group.", [citation]))


if __name__ == "__main__":
    unittest.main()
