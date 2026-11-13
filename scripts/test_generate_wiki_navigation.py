"""Container navigation must survive regeneration without changing statements."""

from __future__ import annotations

import contextlib
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import generate_wiki as wiki


def _target(index: int, sections: tuple[str, str, str] = ("", "", ""), module: str = "MathlibExt/Geometry/Falconer") -> wiki.Target:
    return wiki.Target(
        book=module.split("/")[0], idx=index, title=f"Result {index}", slug=f"result-{index}", location="Geometry",
        description="", declaration="theorem", lean=f"Falconer.result{index}", statement=True, proof=True,
        names=[f"Falconer.result{index}"], module=tuple(module.split("/")), sections=sections,
    )


@contextlib.contextmanager
def _committed(folder: str, pages: dict[Path, str], labels: dict[Path, str] | None = None):
    """blueprint/pages.json as generating these pages under folder/roadmap writes it, read back by the generator."""
    roadmap, page_map = Path(folder) / "roadmap", Path(folder) / "pages.json"
    with patch.object(wiki, "ROADMAP", roadmap), patch.object(wiki, "PAGE_MAP", page_map):
        page_map.write_text(wiki.render_page_map(pages, labels))
        yield


TAXONOMY = {
    "schema": wiki.TAXONOMY_SCHEMA,
    "regions": {"Geometry & Topology": ["Geometry"], "Algebra & Number Theory": ["Algebra"]},
    "subjects": {
        "Geometry": {
            "title": "Geometry",
            "description": "Geometry studies shapes.",
            "fields": [
                {"slug": "convex", "title": "Convex geometry", "description": "Convex sets.", "subfields": []},
                {
                    "slug": "metric", "title": "Metric geometry", "description": "Distances.",
                    "subfields": [{"slug": "distance-sets", "title": "Distance sets", "description": "Distinct distances."}],
                },
            ],
        },
        "Algebra": {"title": "Algebra", "description": "Algebra studies operations.", "fields": []},
    },
    "placements": {
        "MathlibExt/Geometry/Falconer": {"to": "Geometry/metric/distance-sets", "title": "Falconer distance problem"},
        "WantedExt/Geometry/FalconerWanted": {"to": "Geometry/metric/distance-sets", "title": "Falconer distance problem"},
        "MathlibExt/Geometry/Sofa": {"to": "Geometry/convex", "title": "Moving sofa problem"},
        "CSLibExt/Geometry/Hull": {"to": "Geometry/convex", "title": "Convex hulls"},
    },
}


class NavigationTests(unittest.TestCase):
    def test_roadmap_root_lists_subjects_by_region(self):
        previous = "---\narticle_id: af_000000000000000000000001\n---\n# ATLAS roadmap\n"
        rendered = wiki.render_roadmap_root(TAXONOMY, ["Algebra", "Geometry"], previous)
        self.assertEqual(
            rendered,
            "---\narticle_id: af_000000000000000000000001\n---\n\n"
            "# ATLAS roadmap\n\n## Geometry & Topology\n\n- [Geometry](Geometry/README.md)\n\n"
            "## Algebra & Number Theory\n\n- [Algebra](Algebra/README.md)\n",
        )

    def test_a_subject_without_a_region_still_appears(self):
        taxonomy = {**TAXONOMY, "regions": {"Geometry & Topology": ["Geometry"]}}
        self.assertEqual(wiki.regions(taxonomy, ["Algebra", "Geometry"]),
                         {"Geometry & Topology": ["Geometry"], "Other subjects": ["Algebra"]})

    def test_the_taxonomy_places_modules_in_fields_and_subfields(self):
        targets = [_target(0), _target(1), _target(2, module="MathlibExt/Geometry/Sofa"), _target(3, module="MathlibExt/Geometry/Sofa")]
        tree = wiki.subject_tree("Geometry", targets, TAXONOMY)
        self.assertEqual(tree.title, "Geometry")
        self.assertEqual(tree.prose, "Geometry studies shapes.")
        self.assertEqual([field.title for field in tree.children], ["Convex geometry", "Metric geometry"])
        convex, metric = tree.children
        self.assertEqual([topic.title for topic in convex.children], ["Moving sofa problem"])
        (subfield,) = metric.children
        self.assertEqual((subfield.title, subfield.prose), ("Distance sets", "Distinct distances."))
        (topic,) = subfield.children
        self.assertEqual((topic.title, topic.navigation), ("Falconer distance problem", "module"))

    def test_a_statement_file_merges_into_the_development_with_its_title(self):
        targets = [_target(0), _target(1, module="WantedExt/Geometry/FalconerWanted"), _target(2)]
        tree = wiki.subject_tree("Geometry", targets, TAXONOMY)
        (topic,) = tree.children[0].children[0].children
        self.assertEqual([child.title for child in topic.children], ["Result 0", "Result 2", "Result 1"])

    def test_a_placed_directory_keeps_its_modules_as_pages(self):
        targets = [_target(0, module="CSLibExt/Geometry/Hull/Basic"), _target(1, module="CSLibExt/Geometry/Hull/Basic"),
                   _target(2, module="CSLibExt/Geometry/Hull/Graham"), _target(3, module="CSLibExt/Geometry/Hull/Graham")]
        targets[2].module_title = targets[3].module_title = "Graham scan"
        (field,) = wiki.subject_tree("Geometry", targets, TAXONOMY).children
        (topic,) = field.children
        self.assertEqual(topic.title, "Convex hulls")
        self.assertEqual([page.title for page in topic.children], ["Basic", "Graham scan"])

    def test_a_heading_titles_its_page_without_code_marks(self):
        self.assertEqual(wiki.page_title("Noncrossing partitions of `Fin n`"), "Noncrossing partitions of Fin n")
        self.assertEqual(wiki.page_title("Graphs on `Fin n`. Paths in `V`"), "Graphs on Fin n. Paths in V")
        self.assertEqual(wiki.page_title("A" * 90), "A" * 90)
        self.assertEqual(wiki.page_title("A" * 87 + " `x`"), "A" * 87 + " x")
        for heading in ("`MathlibExt.SetTheory.Tree.Basic`", "Facts about `Nat.Prime` numbers", "$\\kappa$-Suslin tree; Suslin tree",
                        "lower case", "", "A" * 91, "A" * 89 + " `x`"):
            self.assertIsNone(wiki.page_title(heading))

    def test_a_directory_takes_the_heading_of_its_umbrella_module(self):
        modules = ["Hull/Planar/A", "Hull/Planar/A", "Hull/Planar/B", "Hull/Planar/B", "Hull/Planar", "Hull/Graham", "Hull/Graham"]
        targets = [_target(index, module=f"CSLibExt/Geometry/{module}") for index, module in enumerate(modules)]
        with tempfile.TemporaryDirectory() as root:
            umbrella = Path(root, "CSLibExt/Geometry/Hull/Planar.lean")
            umbrella.parent.mkdir(parents=True)
            umbrella.write_text("module\n\n/-!\n# Planar convex hulls\n-/\n")
            with patch.object(wiki, "ROOT", Path(root)):
                (field,) = wiki.subject_tree("Geometry", targets, TAXONOMY).children
        (topic,) = field.children
        self.assertEqual([page.title for page in topic.children], ["Planar convex hulls", "Graham"])
        self.assertEqual([child.title for child in topic.children[0].children], ["Result 4", "A", "B"])

    def test_a_topic_titled_like_its_field_leads_the_field(self):
        placements = {**TAXONOMY["placements"], "MathlibExt/Geometry/Convexity": {"to": "Geometry/convex", "title": "Convex geometry"}}
        targets = [_target(index, module=f"MathlibExt/Geometry/{module}") for index, module in enumerate(["Convexity", "Convexity", "Sofa", "Sofa"])]
        (convex,) = wiki.subject_tree("Geometry", targets, {**TAXONOMY, "placements": placements}).children
        self.assertEqual([child.title for child in convex.children], ["Result 0", "Result 1", "Moving sofa problem"])

    def test_a_namesake_too_large_to_lead_its_field_stays_a_page(self):
        placements = {**TAXONOMY["placements"], "MathlibExt/Geometry/Convexity": {"to": "Geometry/convex", "title": "Convex geometry"}}
        modules = ["Convexity"] * 25 + ["Sofa", "Sofa"]
        targets = [_target(index, module=f"MathlibExt/Geometry/{module}") for index, module in enumerate(modules)]
        (convex,) = wiki.subject_tree("Geometry", targets, {**TAXONOMY, "placements": placements}).children
        self.assertEqual([child.title for child in convex.children], ["Convex geometry", "Moving sofa problem"])

    def test_a_namesake_from_several_modules_leads_as_a_page_per_module(self):
        placements = {**TAXONOMY["placements"], **{f"MathlibExt/Geometry/{name}": {"to": "Geometry/convex", "title": "Convex geometry"}
                                                   for name in ("ConvexA", "ConvexB")}}
        modules = ["ConvexA", "ConvexA", "ConvexB", "ConvexB", "Sofa", "Sofa"]
        targets = [_target(index, module=f"MathlibExt/Geometry/{module}") for index, module in enumerate(modules)]
        targets[0].module_title = targets[1].module_title = "Convex sets"
        targets[2].module_title = targets[3].module_title = "Convex functions"
        taxonomy = {**TAXONOMY, "placements": placements}
        (convex,) = wiki.subject_tree("Geometry", targets, taxonomy).children
        self.assertEqual([child.title for child in convex.children], ["Convex sets", "Convex functions", "Moving sofa problem"])
        # A module headed like the field leads it in turn.
        targets[0].module_title = targets[1].module_title = "Convex geometry"
        (convex,) = wiki.subject_tree("Geometry", targets, taxonomy).children
        self.assertEqual([child.title for child in convex.children], ["Result 0", "Result 1", "Convex functions", "Moving sofa problem"])

    def test_a_module_page_titled_like_its_topic_leads_the_topic(self):
        modules = ["Hull/Basic", "Hull/Basic", "Hull/Graham", "Hull/Graham"]
        targets = [_target(index, module=f"CSLibExt/Geometry/{module}") for index, module in enumerate(modules)]
        targets[0].module_title = targets[1].module_title = "Convex hulls"
        (field,) = wiki.subject_tree("Geometry", targets, TAXONOMY).children
        (topic,) = field.children
        self.assertEqual([child.title for child in topic.children], ["Result 0", "Result 1", "Graham"])

    def test_siblings_follow_the_siblings_their_articles_use(self):
        a, b, c = (wiki.Container(name, name.lower(), [_target(index)]) for index, name in enumerate("ABC"))
        a.children[0].depends.append(c.children[0])
        self.assertEqual([node.title for node in wiki.dependency_order([a, b, c])], ["B", "C", "A"])

    def test_a_single_article_a_page_uses_leads_and_the_others_follow_the_pages(self):
        page, unused, used = wiki.Container("P", "p", [_target(0)]), _target(2), _target(1)
        page.children[0].proof_depends.append(used)
        self.assertEqual([node.title for node in wiki.dependency_order([page, unused, used])], ["Result 1", "P", "Result 2"])

    def test_a_cycle_starts_with_the_sibling_that_uses_least_of_the_rest(self):
        a, b = wiki.Container("A", "a", [_target(0), _target(1)]), wiki.Container("B", "b", [_target(2)])
        a.children[0].depends.append(b.children[0])
        a.children[1].depends.append(b.children[0])
        b.children[0].depends.append(a.children[0])
        self.assertEqual([node.title for node in wiki.dependency_order([a, b])], ["B", "A"])

    def test_a_field_lists_a_topic_after_the_topics_it_uses(self):
        modules = ["CSLibExt/Geometry/Hull/Basic", "CSLibExt/Geometry/Hull/Basic", "MathlibExt/Geometry/Sofa", "MathlibExt/Geometry/Sofa"]
        targets = [_target(index, module=module) for index, module in enumerate(modules)]
        (field,) = wiki.subject_tree("Geometry", targets, TAXONOMY).children
        self.assertEqual([topic.title for topic in field.children], ["Convex hulls", "Moving sofa problem"])
        targets[0].depends.append(targets[3])
        (field,) = wiki.subject_tree("Geometry", targets, TAXONOMY).children
        self.assertEqual([topic.title for topic in field.children], ["Moving sofa problem", "Convex hulls"])

    def test_a_sibling_that_uses_a_cycle_follows_the_whole_cycle(self):
        a = wiki.Container("A", "a", [_target(0)])
        b, c = (wiki.Container(name, name.lower(), [_target(index), _target(index + 1)]) for index, name in ((1, "B"), (3, "C")))
        a.children[0].depends.append(c.children[0])
        for user, used in ((b, c), (c, b)):
            for mine, theirs in zip(user.children, used.children):
                mine.depends.append(theirs)
        self.assertEqual([node.title for node in wiki.dependency_order([a, b, c])], ["B", "C", "A"])

    def test_a_single_article_that_needs_a_sub_page_follows_the_pages(self):
        p, q = (wiki.Container(name, name.lower(), [_target(index)]) for index, name in enumerate("PQ"))
        s, t, u = _target(2), _target(3), _target(4)
        p.children[0].depends += [s, t, u]
        s.depends.append(q.children[0])
        t.depends.append(s)
        self.assertEqual([node.title for node in wiki.dependency_order([p, q, s, t, u])], ["Result 4", "P", "Q", "Result 2", "Result 3"])

    def test_a_namesake_article_that_uses_a_sibling_topic_follows_it(self):
        placements = {**TAXONOMY["placements"], "MathlibExt/Geometry/Convexity": {"to": "Geometry/convex", "title": "Convex geometry"}}
        targets = [_target(index, module=f"MathlibExt/Geometry/{module}") for index, module in enumerate(["Convexity", "Convexity", "Sofa", "Sofa"])]
        targets[1].depends.append(targets[2])
        (convex,) = wiki.subject_tree("Geometry", targets, {**TAXONOMY, "placements": placements}).children
        self.assertEqual([child.title for child in convex.children], ["Result 0", "Moving sofa problem", "Result 1"])

    def test_lists_in_dependency_order_number_their_parts(self):
        for directory in ("Hull", "Hull/Planar"):
            with self.subTest(directory=directory):
                targets = [_target(2 * index + half, module=f"CSLibExt/Geometry/{directory}/M{index:02d}") for index in range(21) for half in (0, 1)]
                (field,) = wiki.subject_tree("Geometry", targets, TAXONOMY).children
                (topic,) = field.children
                self.assertEqual([part.title for part in topic.children], ["Part 1 of 2", "Part 2 of 2"])
        placements = {f"MathlibExt/Geometry/T{index:02d}": {"to": "Geometry/convex", "title": f"Topic {index:02d}"} for index in range(21)}
        targets = [_target(2 * index + half, module=f"MathlibExt/Geometry/T{index:02d}") for index in range(21) for half in (0, 1)]
        (convex,) = wiki.subject_tree("Geometry", targets, {**TAXONOMY, "placements": placements}).children
        self.assertEqual([part.title for part in convex.children], ["Part 1 of 2", "Part 2 of 2"])
        nested = wiki.chunk("Geometry", "geometry", [_target(index) for index in range(401)], ranges=False)
        self.assertEqual(nested.children[0].children[0].title, "Part 1 of 20")

    def test_an_unplaced_module_is_listed_as_not_yet_classified(self):
        targets = [_target(0, module="MathlibExt/Geometry/NewTopic"), _target(1, module="MathlibExt/Geometry/NewTopic")]
        (field,) = wiki.subject_tree("Geometry", targets, TAXONOMY).children
        self.assertEqual(field.title, "Not yet classified")
        self.assertEqual([topic.title for topic in field.children], ["New Topic"])

    def test_a_module_with_one_article_is_that_article(self):
        tree = wiki.subject_tree("Geometry", [_target(0, module="MathlibExt/Geometry/Sofa")], TAXONOMY)
        (topic,) = tree.children[0].children
        self.assertIsInstance(topic, wiki.Target)

    def test_placement_prefers_the_longest_placed_path(self):
        placements = {"A/B": {"to": "S/f", "title": "Outer"}, "A/B/C": {"to": "S/g", "title": "Inner"}}
        self.assertEqual(wiki.placement(("A", "B", "C"), placements)[0], "A/B/C")
        self.assertEqual(wiki.placement(("A", "B", "D"), placements)[0], "A/B")
        self.assertIsNone(wiki.placement(("A", "E"), placements))

    def test_landing_page_is_navigation_not_generation_instructions(self):
        landing = (wiki.VAULT / "README.md").read_text(encoding="utf-8")
        self.assertIn("# ATLAS\n", landing)
        self.assertIn("(roadmap/README.md)", landing)
        self.assertIn("(coverage/README.md)", landing)
        for boilerplate in ("scripts/generate_wiki.py", "progress percentages", "docstring", "archived ATLAS v1"):
            with self.subTest(boilerplate=boilerplate):
                self.assertNotIn(boilerplate, landing)

    def test_chunk_marks_only_its_pagination_ranges_transparent(self):
        children = [wiki.Container(f"Topic {index}", str(index), []) for index in range(41)]
        root = wiki.chunk("Geometry", "geometry", children)
        self.assertIsNone(root.navigation)
        self.assertTrue(all(page.navigation == "transparent" for page in root.children))
        self.assertTrue(all(topic.navigation is None for page in root.children for topic in page.children))

    def test_regeneration_preserves_authored_mathematics_and_region(self):
        node = wiki.Container("Distance geometry", "distance", [], path=wiki.VAULT / "roadmap/example/README.md")
        previous = """---
article_id: af_000000000000000000000001
area: Metric geometry
---
# Distance geometry

## Mathematical overview

This section studies the distances determined by finite point configurations.

## Contents

- [Previous child](previous.md)
"""
        rendered = wiki.render_container(node, previous)
        self.assertIn("area: Metric geometry", rendered)
        self.assertIn("This section studies the distances", rendered)
        self.assertNotIn("previous.md", rendered)
        self.assertEqual(rendered.count("## Contents"), 1)

    def test_a_module_is_one_page_of_its_declarations(self):
        tree = wiki.subject_tree("Geometry", [_target(index) for index in range(26)], TAXONOMY)
        (module,) = tree.children[0].children[0].children
        self.assertEqual(module.navigation, "module")
        self.assertEqual([child.title for child in module.children], [f"Result {index}" for index in range(26)])

    def test_module_sections_follow_doc_headings_after_the_module_docstring(self):
        lines = [
            "/-! # Falconer", "## Background in the module docstring -/", "namespace Falconer",
            "/-- a -/", "theorem a : True := trivial",
            "/-! ## Thresholds -/", "/-- b -/", "theorem b : True := trivial",
            "/-! ## Admissibility -/", "/-- c -/", "theorem c : True := trivial", "end Falconer",
        ]
        labels = wiki.section_labels(lines)
        self.assertEqual([labels[4], labels[7], labels[10]], [
            ("", "", "Falconer"), ("Thresholds", "", "Falconer"), ("Admissibility", "", "Falconer"),
        ])
        items = [_target(index, labels[line]) for index, line in enumerate((4, 7, 10))]
        self.assertEqual(wiki.module_groups(items), ["", "Thresholds", "Admissibility"])

    def test_a_label_that_returns_to_none_does_not_group(self):
        items = [_target(0, ("", "Layers", "")), _target(1, ("", "", "")), _target(2, ("", "Paths", ""))]
        self.assertIsNone(wiki.module_groups(items))

    def test_module_page_lists_declarations_under_their_sections(self):
        items = [_target(0), _target(1), _target(2)]
        page = wiki.Container("Falconer", "falconer", items, navigation="module", groups=["", "Thresholds", "Thresholds"])
        wiki.assign_paths(page, wiki.ROADMAP / "Geometry/MathlibExt/falconer")
        self.assertEqual(
            wiki.render_container(page, None),
            "---\nnavigation: module\n---\n\n# Falconer\n\n- [Result 0](result-0.md)\n\n"
            "## Thresholds\n\n- [Result 1](result-1.md)\n- [Result 2](result-2.md)\n",
        )

    def test_articles_among_sub_pages_follow_them_and_a_leading_run_stays(self):
        children = [_target(5), wiki.Container("D", "d", [_target(0)]), _target(3), wiki.Container("B", "b", [_target(2)]), _target(1)]
        page = wiki.Container("Sum-free sets", "sum-free-sets", children)
        wiki.assign_paths(page, wiki.ROADMAP / "Combinatorics/sum-free-sets")
        self.assertEqual(
            wiki.render_container(page, None),
            "# Sum-free sets\n\n- [Result 5](result-5.md)\n- [D](d/README.md)\n- [B](b/README.md)\n"
            "- [Result 3](result-3.md)\n- [Result 1](result-1.md)\n",
        )

    def test_a_pagination_part_lists_its_children_alike_on_both_pages(self):
        part = wiki.Container("B to D", "part-01", [wiki.Container("B", "b", [_target(0)]), _target(1), wiki.Container("D", "d", [_target(2)])],
                              navigation="transparent")
        root = wiki.Container("Geometry", "geometry", [part])
        wiki.assign_paths(root, wiki.ROADMAP / "Geometry")
        self.assertIn("## [B to D](part-01/README.md)\n\n- [B](part-01/b/README.md)\n- [D](part-01/d/README.md)\n"
                      "- [Result 1](part-01/result-1.md)\n", wiki.render_container(root, None))
        self.assertIn("- [B](b/README.md)\n- [D](d/README.md)\n- [Result 1](result-1.md)\n", wiki.render_container(part, None))

    def test_pagination_parts_render_as_sections_of_the_parent_page(self):
        root = wiki.chunk("Geometry", "geometry", [_target(index) for index in range(41)])
        wiki.assign_paths(root, wiki.ROADMAP / "Geometry")
        rendered = wiki.render_container(root, None)
        self.assertIn("## [Result 0 to Result 19](part-01/README.md)\n\n- [Result 0](part-01/result-0.md)\n", rendered)
        self.assertIn("## [Part 3 of 3](part-03/README.md)\n\n- [Result 40](part-03/result-40.md)\n", rendered)

    def test_ids_are_found_by_lean_name_when_a_page_moves(self):
        with tempfile.TemporaryDirectory() as folder:
            roadmap = Path(folder) / "roadmap"
            old = roadmap / "Geometry/MathlibExt/falconer/part-01/result-0.md"
            with _committed(folder, {old: "---\narticle_id: af_000000000000000000000002\ndeclaration: theorem\nlean: Falconer.result0\n---\n# Result 0\n"}):
                self.assertEqual(wiki.ids_by_lean(), {"Falconer.result0": "af_000000000000000000000002"})


    def test_a_declaration_that_stays_in_its_folder_keeps_its_file_name(self):
        # first has no Lean name, so it goes by module and title; twin repeats second's Lean name.
        first, second, moved, renamed, twin = _target(0), _target(1), _target(2), _target(3), _target(1)
        first.lean = None
        for target in (first, second, moved, twin):
            target.slug = "hasse-bound"
        renamed.slug = "kraft"
        directory = wiki.ROADMAP / "AlgebraicGeometry/hasse-bound"
        kept = {wiki.page_key(first): directory / "hasse-bound-3.md", second.lean: directory / "hasse-bound.md",
                moved.lean: wiki.ROADMAP / "Elsewhere/hasse-bound-5.md", renamed.lean: directory / "hasse-bound-4.md"}
        page = wiki.Container("Hasse bound", "hasse-bound", [first, second, moved, renamed, twin])
        wiki.assign_paths(page, directory, kept)
        self.assertEqual([target.path.name for target in (first, second, moved, renamed, twin)],
                         ["hasse-bound-3.md", "hasse-bound.md", "hasse-bound-2.md", "kraft.md", "hasse-bound-4.md"])

    def test_no_page_takes_the_name_of_its_folder_page(self):
        index, readme = _target(0), _target(1)
        index.slug, readme.slug = "index", "readme"
        directory = wiki.ROADMAP / "NumberTheory/multiple-zeta-indices"
        page = wiki.Container("Multiple-zeta indices", "multiple-zeta-indices", [index, readme])
        wiki.assign_paths(page, directory, {index.lean: directory / "index.md"})
        self.assertEqual([index.path.name, readme.path.name], ["index-2.md", "readme-2.md"])

    def test_pages_are_found_by_lean_name(self):
        with tempfile.TemporaryDirectory() as folder:
            roadmap = Path(folder) / "roadmap"
            page = roadmap / "Geometry/MathlibExt/falconer/result-0-2.md"
            pages = {page: "---\ndeclaration: theorem\nlean: Falconer.result0\n---\n# Result 0\n", page.parent / "README.md": "# Falconer\n"}
            pages.update({page.parent / twice: "---\nlean: Falconer.result1\n---\n# Result 1\n" for twice in ("a.md", "b.md")})
            with _committed(folder, pages):
                self.assertEqual(wiki.pages_by_lean(), {"Falconer.result0": page})

    def test_a_page_is_found_again_by_its_lean_name_or_else_its_module_and_title(self):
        named, unnamed, twin = (_target(index, module=f"MathlibExt/{module}") for index, module in enumerate("ABC"))
        unnamed.lean = twin.lean = None
        twin.title = unnamed.title
        with tempfile.TemporaryDirectory() as folder:
            roadmap = Path(folder) / "roadmap"
            for target in (named, unnamed, twin):
                target.path = roadmap / f"Geometry/{target.slug}.md"
            with patch.object(wiki, "VAULT", Path(folder)), patch.object(wiki, "ROADMAP", roadmap):
                pages = {target.path: wiki.render_target(target, None) for target in (named, unnamed, twin)}
            with _committed(folder, pages, {target.path: wiki.page_key(target) for target in (unnamed, twin)}):
                self.assertEqual(wiki.pages_by_lean(), {wiki.page_key(target): target.path for target in (named, unnamed, twin)})

if __name__ == "__main__":
    unittest.main()
