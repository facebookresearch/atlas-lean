#!/usr/bin/env python3
"""Generate the ATLAS wiki under blueprint/.

    python scripts/generate_wiki.py          rewrite the generated pages
    python scripts/generate_wiki.py --check  fail if any generated page is stale

ATLAS v2, the root Lake package, comes first: every public MathlibExt, CSLibExt
and WantedExt declaration with a docstring becomes one article whose statement
is that docstring. Theorems are proved and definitions defined unless their
module contains `sorry`; `theorem_wanted` entries are stated results waiting
for a proof, and `def_wanted` entries stay unstated, because Autoform counts a
stated definition as defined.

Run it with a Python that has Autoform installed (see blueprint-pages.yml).

The archived v1 release follows as source tracks. Every target in
v1/Atlas/<Book>/report.json becomes one roadmap article: the
informal statement from the textbook, its source location, and the Lean
declaration that ATLAS v1 matched to it. Lean names and declaration keywords
come from Autoform's own source index, so `autoform check --lean-root .`
accepts exactly what this script asserts.

Status follows v1's own evaluation. A target that passed review is
`statement: formalized`; a theorem whose dependency chain is also sorry-free
(per `sorry_deps`) and rests only on Lean's standard axioms (per `#print axioms`;
so no sorryAx and no native_decide) is `proof: formalized`. Definitions need a sorry-free chain to be marked at all,
because Autoform counts a stated definition as proved. Graph edges come from
sources/v1/lean-dependencies.json (see scripts/extract_v1_lean_dependencies.py):
the targets a target's Lean statement or proof reaches, through helper
declarations if need be. Where sources/v1/book-dependencies/<Book>.json exists,
its verified edges, read from the source text itself, are added as well.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import textwrap
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

from autoform_cli.lean import index_project
from autoform_cli.status import DEFINITION_DECLARATIONS

ROOT = Path(__file__).resolve().parent.parent
V1 = ROOT / "v1"
VAULT = ROOT / "blueprint"
ROADMAP = VAULT / "roadmap"
SOURCES = VAULT / "sources"
REPOSITORY_URL = "https://github.com/facebookresearch/atlas-lean"
MAX_CHILDREN = 20  # `autoform audit` reports containers above 24.

# Book directory -> (subject directory, source title). Subject directories and
# titles match the Formal-Math wiki so the two maps line up.
BOOKS = {
    "AlgebraNotes": ("Algebra", "MIT RES.18-011 Algebra I Student Notes (Fall 2021)"),
    "AlgebraicCombinatorics": ("Combinatorics", "MIT 18.318 Topics in Algebraic Combinatorics (Spring 2006)"),
    "AlgebraicGeometryI": ("AlgebraicGeometry", "MIT 18.725 Algebraic Geometry (Fall 2015)"),
    "AlgebraicTopologyI": ("AlgebraicTopology", "MIT 18.905 Algebraic Topology I (Fall 2016)"),
    "AnAlgorithmistsToolkit": ("ComputerScience", "MIT 18.409 An Algorithmist's Toolkit (Fall 2009)"),
    "ArithmeticGeometry": ("ArithmeticGeometry", "MIT 18.782 Introduction to Arithmetic Geometry (Fall 2013)"),
    "BooleanFunctions": ("Combinatorics", "MIT 18.218 Analysis of Boolean Functions (Spring 2021)"),
    "Buildings": ("GroupTheory", "Paul Garrett, Buildings and Classical Groups"),
    "CombinatorialOptimization": ("Combinatorics", "MIT 18.433 Combinatorial Optimization (Fall 2003)"),
    "ComplexVariables": ("Analysis", "MIT 18.112 Functions of a Complex Variable (Fall 2008)"),
    "DifferentialAnalysis": ("Analysis", "MIT 18.155 Differential Analysis (Fall 2004)"),
    "DifferentialGeometry": ("Geometry", "MIT 18.950 Differential Geometry (Fall 2008)"),
    "EllipticCurves": ("NumberTheory", "MIT 18.783 Elliptic Curves (Spring 2021)"),
    "FourierAnalysis": ("Analysis", "MIT 18.103 Fourier Analysis (Fall 2013)"),
    "GeometryOfManifolds": ("Geometry", "MIT 18.966 Geometry of Manifolds (Spring 2007)"),
    "HighDimensionalStatistics": ("Probability", "MIT 18.S997 High-Dimensional Statistics (Spring 2015)"),
    "IntroductionToFunctionalAnalysis": ("Analysis", "MIT 18.102 Introduction to Functional Analysis (Spring 2021)"),
    "IntroductionToPartialDifferentialEquations": (
        "Analysis",
        "MIT 18.152 Introduction to Partial Differential Equations (Fall 2011)",
    ),
    "LieGroups": ("RepresentationTheory", "MIT 18.757 Representations of Lie Groups (Fall 2023)"),
    "NumberTheoryI": ("NumberTheory", "MIT 18.785 Number Theory I (Fall 2021)"),
    "ProbabilisticMethodsInCombinatorics": (
        "Combinatorics",
        "MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022)",
    ),
    "ProjectionTheory": ("Analysis", "MIT 18.156 Projection Theory (Spring 2025)"),
    "RealAnalysis": ("Analysis", "MIT 18.100A Real Analysis (Fall 2020)"),
    "TensorCategories": ("CategoryTheory", "MIT 18.769 Topics in Lie Theory: Tensor Categories (Spring 2009)"),
    "TheoryOfComputation": ("TheoryOfComputation", "MIT 18.404J Theory of Computation (Fall 2020)"),
    "TheoryOfProbability": ("Probability", "MIT 18.175 Theory of Probability (Spring 2014)"),
}

SUBJECTS = {
    "Computability": (
        "Computability",
        "Computability studies which mathematical processes can be carried out by algorithms and how such "
        "procedures are represented.",
    ),
    "Data": (
        "Data",
        "Data theory develops mathematical representations, transformations, and invariants for structured "
        "information.",
    ),
    "Dynamics": (
        "Dynamics",
        "Dynamics studies systems evolving through iteration or time, including recurrence, stability, and "
        "long-term behavior.",
    ),
    "FieldTheory": (
        "Field Theory",
        "Field theory studies extensions of fields, algebraic elements, automorphisms, and Galois-theoretic "
        "structure.",
    ),
    "GameTheory": (
        "Game Theory",
        "Game theory studies strategic and combinatorial interaction, equilibria, winning conditions, and optimal "
        "play.",
    ),
    "GraphTheory": (
        "Graph Theory",
        "Graph theory studies vertices and edges through connectivity, coloring, minors, flows, and extremal "
        "structure.",
    ),
    "InformationTheory": (
        "Information Theory",
        "Information theory quantifies information, uncertainty, compression, and transmission through entropy and "
        "coding.",
    ),
    "LinearAlgebra": (
        "Linear Algebra",
        "Linear algebra studies vector spaces, linear maps, matrices, duality, dimension, and spectral structure.",
    ),
    "Logic": (
        "Logic",
        "Logic studies formal languages, proof, models, semantics, consistency, and the foundations of mathematical "
        "reasoning.",
    ),
    "MeasureTheory": (
        "Measure Theory",
        "Measure theory provides the language of size and integration underlying probability and modern analysis.",
    ),
    "Order": (
        "Order",
        "Order theory studies comparison relations, lattices, intervals, monotonicity, and order-complete "
        "constructions.",
    ),
    "QuantumInformation": (
        "Quantum Information",
        "Quantum information studies states, channels, measurement, entanglement, communication, and quantum "
        "computation.",
    ),
    "RingTheory": (
        "Ring Theory",
        "Ring theory studies addition and multiplication through ideals, modules, localization, dimension, and "
        "homological structure.",
    ),
    "SetTheory": (
        "Set Theory",
        "Set theory studies membership, cardinality, ordinals, infinity, and foundational constructions for "
        "mathematics.",
    ),
    "Topology": (
        "Topology",
        "Topology studies continuity, open sets, compactness, connectedness, and invariants preserved by "
        "homeomorphism.",
    ),
    "Algebra": (
        "Algebra",
        "Algebra studies structures defined by operations and the laws, morphisms, and symmetries that organize them.",
    ),
    "AlgebraicGeometry": (
        "Algebraic Geometry",
        "Algebraic geometry studies spaces cut out by polynomial equations and translates between their "
        "geometric and algebraic invariants.",
    ),
    "AlgebraicTopology": (
        "Algebraic Topology",
        "Algebraic topology assigns computable invariants such as homology and homotopy to spaces and continuous maps.",
    ),
    "Analysis": (
        "Analysis",
        "Analysis studies limits, approximation, continuity, and infinite-dimensional spaces of functions and operators.",
    ),
    "ArithmeticGeometry": (
        "Arithmetic Geometry",
        "Arithmetic geometry approaches number-theoretic questions through varieties, schemes, and their "
        "arithmetic invariants.",
    ),
    "CategoryTheory": (
        "Category Theory",
        "Category theory organizes mathematical structures through morphisms, functors, universal properties, "
        "limits, and adjunctions.",
    ),
    "Combinatorics": (
        "Combinatorics",
        "Combinatorics studies finite and discrete configurations through counting, extremal structure, and "
        "constructive arguments.",
    ),
    "ComputerScience": (
        "Computer Science",
        "Computer science formalizes algorithms, programming-language structures, data abstractions, and "
        "correctness properties.",
    ),
    "Geometry": (
        "Geometry",
        "Geometry studies shapes, spaces, transformations, curvature, and the invariants preserved by geometric "
        "equivalence.",
    ),
    "GroupTheory": (
        "Group Theory",
        "Group theory studies symmetry through groups, actions, subgroups, quotients, and structural decompositions.",
    ),
    "NumberTheory": (
        "Number Theory",
        "Number theory studies integers, primes, Diophantine equations, arithmetic functions, and their analytic "
        "and algebraic structure.",
    ),
    "Probability": (
        "Probability",
        "Probability studies random phenomena through distributions, expectation, independence, concentration, "
        "and stochastic processes.",
    ),
    "RepresentationTheory": (
        "Representation Theory",
        "Representation theory studies symmetry by realizing groups and algebras as transformations of linear spaces.",
    ),
    "TheoryOfComputation": (
        "Theory of Computation",
        "The theory of computation studies automata, formal languages, complexity, reducibility, and limits of "
        "efficient algorithms.",
    ),
}

# Library -> (description, top-level directory -> subject when the names differ).
LIBRARIES = {
    "MathlibExt": ("Reusable, fully proved extensions to Mathlib.", {"ModelTheory": "Logic"}),
    "CSLibExt": (
        "Reusable, fully proved computer-science developments built on MathlibExt.",
        {
            "Algorithms": "ComputerScience",
            "Complexity": "TheoryOfComputation",
            "Foundations": "ComputerScience",
            "Languages": "ComputerScience",
            "Logics": "Logic",
        },
    ),
    "WantedExt": (
        "Established results whose Lean implementation or proof is deferred.",
        {"Complexity": "TheoryOfComputation", "ModelTheory": "Logic"},
    ),
}
V2_DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:private|protected|noncomputable|partial|unsafe|public|nonrec|scoped)\s+)*)"
    r"(?P<kw>theorem_wanted|def_wanted|theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\b"
    r"\s*(?P<name>[^\s:(\[{]*)"
)
WANTED = {"theorem_wanted": "theorem", "def_wanted": "def"}
BOLD_TITLE = re.compile(r"^\*\*(?P<title>[^*]+)\*\*")
KERNEL_AXIOMS = {"propext", "Classical.choice", "Quot.sound", "No axiom dependencies"}
KIND_DECLARATION = {"definition": "def", "construction": "def", "axiom": "axiom"}
NUMBERED_HEAD = re.compile(r"(?i)^(section|chapter|lecture|class meeting\s*#?|part)\s*(\d+)")
ARTICLE_ID = re.compile(r"^article_id: (af_[0-9a-f]{24})$", re.M)
BARE_NAME = re.compile(r"(?i)[a-z]+\.?")
MATH_SPAN = re.compile(
    r"(?s)(?<!\\)(?P<dollars>\${1,2}).*?(?<!\\)(?P=dollars)|\\\(.*?\\\)|\\\[.*?\\\]"
)


@dataclass
class Target:
    book: str
    idx: int
    title: str
    slug: str
    location: str
    description: str
    declaration: str
    lean: str | None
    statement: bool
    proof: bool
    names: list[str]
    source: tuple[str, Path] | None = None
    citations: list[str] = field(default_factory=list)
    module: tuple[str, ...] = ()
    path: Path = Path()
    depends: list[Target] = field(default_factory=list)
    proof_depends: list[Target] = field(default_factory=list)


@dataclass
class Container:
    title: str
    slug: str
    children: list[Container | Target]
    prose: str = ""
    path: Path = Path()


def slugify(text: str, limit: int = 48) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    return slug[:limit].rstrip("-") or "untitled"


def link_text(text: str) -> str:
    return text.replace("[", "\\[").replace("]", "\\]")


def chapter_of(location: str) -> str:
    head = re.sub(r"(?i)^section:\s*", "", location.split(",")[0].strip())
    match = NUMBERED_HEAD.match(head)
    if match:
        word = match.group(1).rstrip("# ").title()
        return f"{word} {match.group(2)}"
    return re.sub(r"(?i)\s+section$", "", head) or "Unplaced"


def section_of(location: str) -> str:
    return re.sub(r"(?i)\s+section$", "", location.strip()) or "Unplaced"


def groups(targets: list[Target], key) -> list[tuple[str, list[Target]]]:
    """Group in source order: a group sits where its first target does."""
    grouped: dict[str, list[Target]] = defaultdict(list)
    for target in targets:
        grouped[key(target)].append(target)
    return sorted(grouped.items(), key=lambda item: item[1][0].idx)


def chunk(title: str, slug: str, children: list) -> Container:
    """Nest children under parts so that no container exceeds MAX_CHILDREN."""
    if len(children) <= MAX_CHILDREN:
        return Container(title, slug, children)
    size = MAX_CHILDREN
    while -(-len(children) // size) > MAX_CHILDREN:
        size *= MAX_CHILDREN
    parts = [children[start : start + size] for start in range(0, len(children), size)]
    nested = []
    for number, part in enumerate(parts, 1):
        if isinstance(part[0], Container) and len(part) > 1:
            name = f"{part[0].title} to {part[-1].title}"
        else:
            name = f"Part {number} of {len(parts)}"
        nested.append(chunk(name, f"part-{number:02d}", part))
    return Container(title, slug, nested)


def chapter(title: str, targets: list[Target]) -> Container:
    if len(targets) <= MAX_CHILDREN:
        return Container(title, slugify(title), targets)
    sections = groups(targets, lambda target: section_of(target.location))
    if len(sections) == 1:
        return chunk(title, slugify(title), targets)
    return chunk(title, slugify(title), [chunk(name, slugify(name), items) for name, items in sections])


def disambiguate(targets: list[Target], rename) -> None:
    """Make titles unique within a book: by location first, then by ordinal."""
    counts: dict[str, int] = defaultdict(int)
    for target in targets:
        counts[target.title] += 1
    ordinals: dict[str, int] = defaultdict(int)
    for target in targets:
        if counts[target.title] > 1:
            if rename is not None and target.location not in target.title:
                target.title = rename(target)
            elif rename is None:
                ordinals[target.title] += 1
                target.title = f"{target.title} ({ordinals[target.title]})"


def safe_math_markdown(text: str) -> str:
    """Keep TeX comparisons from opening raw-HTML tags inside site cards."""

    return MATH_SPAN.sub(
        lambda span: re.sub(r"<(?=[A-Za-z_\\])", r"\\lt ", span.group()),
        text,
    )


def load_book(book: str, index, lean_dependencies: dict) -> tuple[list[Target], dict]:
    report = json.loads((V1 / "Atlas" / book / "report.json").read_text())
    details = sorted(report["statements"]["details"], key=lambda item: item["idx"])
    unresolved = []
    targets = []
    for item in details:
        names = [name.strip() for name in (item.get("lean_declaration") or "").split(",") if name.strip()]
        found = [index.find(name) for name in names]
        # Unqualified names such as `Place` recur across v1 books. Resolve the
        # name only when the global index selects this book's occurrence.
        resolved = bool(names) and all(item and item.path.parts[:3] == ("v1", "Atlas", book) for item in found)
        if names and not resolved:
            unresolved.append(item)
        if resolved:
            keywords = {declaration.keyword for declaration in found}
            declaration = sorted(keywords)[0] if len(keywords) == 1 else "theorem"
        else:
            declaration = KIND_DECLARATION.get(item["kind"], "theorem")
        is_data = declaration in DEFINITION_DECLARATIONS
        # `sorry_deps` sometimes says "None" while the compiled `#print axioms`
        # output lists sorryAx; the axioms win. Only Lean's standard axioms
        # count as kernel-checked, so native_decide proofs are not proved here.
        axioms = {name.strip() for name in (item.get("axioms") or "").split(",") if name.strip()}
        sorry_free = (item.get("sorry_deps") or "").startswith("None") and axioms <= KERNEL_AXIOMS
        statement = resolved and item["passed"] and (sorry_free or not is_data)
        name = " ".join(item["name"].split())
        # Brackets in link text stop `autoform render` placing the leaf.
        title = name.replace("[", "(").replace("]", ")")
        if BARE_NAME.fullmatch(name):
            title = f"{title} ({item['location'].strip()})"
        label = re.search(r"\(([^()]+)\)", name)
        targets.append(
            Target(
                book=book,
                idx=item["idx"],
                title=title,
                slug=f"{item['idx'] + 1:03d}-{slugify(label.group(1) if label else name, 40)}",
                location=item["location"].strip(),
                description=safe_math_markdown(item["description"].strip()),
                declaration=declaration,
                lean=", ".join(names) if resolved else None,
                statement=statement,
                proof=statement and not is_data and sorry_free,
                names=names,
            )
        )
    disambiguate(targets, lambda target: f"{target.title} ({target.location})")
    disambiguate(targets, None)
    # Dependency names are v1's own and unique within a book, so an edge does
    # not need the `lean:` link that a name collision elsewhere can withhold.
    by_name: dict[str, Target] = {}
    for target in targets:
        for name in target.names:
            by_name.setdefault(name, target)
    for target in targets:
        for name in target.names:
            entry = lean_dependencies.get(name, {})
            for bucket, kind in ((target.depends, "statement"), (target.proof_depends, "proof")):
                for dependency in entry.get(kind, []):
                    other = by_name.get(dependency)
                    if other is not None and other is not target and other not in target.depends + target.proof_depends:
                        bucket.append(other)
    book_edges = SOURCES / "v1" / "book-dependencies" / f"{book}.json"
    by_idx = {target.idx: target for target in targets}
    book_pairs = set()
    if book_edges.is_file():
        for edge in json.loads(book_edges.read_text())["edges"]:
            target, other = by_idx[edge["from"]], by_idx[edge["to"]]
            if other is target or other in target.depends + target.proof_depends:
                continue
            (target.depends if edge["kind"] == "statement" else target.proof_depends).append(other)
            book_pairs.add((target.idx, other.idx))
    summary = {
        "book_pairs": book_pairs,
        "targets": len(targets),
        "unmatched": [item for item in details if not item.get("lean_declaration")],
        "unresolved": unresolved,
    }
    return targets, summary


def without_comments(text: str) -> str:
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", " ", text, flags=re.S))


def docstring_before(lines: list[str], number: int) -> str | None:
    """The `/-- ... -/` docstring attached to the declaration on line `number`."""
    end = number - 1
    while end >= 0 and (not lines[end].strip() or lines[end].lstrip().startswith("@[")):
        end -= 1
    if end < 0 or not lines[end].rstrip().endswith("-/"):
        return None
    start = end
    while start >= 0 and "/--" not in lines[start]:
        start -= 1
    if start < 0:
        return None
    block = "\n".join(lines[start : end + 1])
    return textwrap.dedent(block[block.index("/--") + 3 : block.rindex("-/")]).strip() or None


def humanize(name: str) -> str:
    text = " ".join(re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", name.replace("_", " ")).split())
    return text[:1].upper() + text[1:]


def split_docstring(doc: str) -> tuple[str, list[str]]:
    """Separate the mathematical statement from its citations and Lean-side notes."""
    statement, citations = [], []
    for paragraph in re.split(r"\n\s*\n", doc):
        if re.match(r"(?i)proves `?wanted`? entr", paragraph.strip()):
            continue
        cite = re.search(r"(?m)^Sources?:\s*", paragraph)
        if cite:
            statement.append(paragraph[: cite.start()].strip())
            citations.append(" ".join(paragraph[cite.end() :].split()))
        else:
            statement.append(paragraph.strip())
    text = "\n\n".join(part for part in statement if part)
    return (text, citations) if text else (doc, [])


def first_words(text: str, limit: int = 60) -> str:
    sentence = re.split(r"(?<=[.!?])\s", " ".join(text.split()), maxsplit=1)[0].rstrip(".")
    return sentence if len(sentence) <= limit else sentence[:limit].rsplit(" ", 1)[0] + "..."


def load_library(library: str, index) -> tuple[list[Target], dict]:
    located = {
        (declaration.path, declaration.line): declaration
        for declaration in index.declarations.values()
        if declaration.path.parts[:1] == (library,)
    }
    targets: list[Target] = []
    summary = {"modules": 0, "public": 0, "documented": 0, "wanted": 0, "instances": 0, "subjects": set()}
    named_by_docstring: set[int] = set()
    for path in sorted((ROOT / library).rglob("*.lean")):
        relative = path.relative_to(ROOT)
        text = path.read_text()
        lines = text.splitlines()
        has_sorry = re.search(r"\bsorry\b", without_comments(text)) is not None
        module = relative.with_suffix("").parts
        summary["modules"] += 1
        for number, line in enumerate(lines):
            match = V2_DECLARATION.match(line)
            if not match or "private" in match.group("mods"):
                continue
            summary["public"] += 1
            if match.group("kw") == "instance":
                summary["instances"] += 1
                continue
            doc = docstring_before(lines, number)
            if doc is None:
                continue
            summary["documented"] += 1
            keyword, short = match.group("kw"), match.group("name").split(".")[-1]
            found = located.get((relative, number + 1))
            if found is None:
                summary["wanted"] += keyword in WANTED
                declaration, lean, statement, proof = WANTED.get(keyword, keyword), None, False, False
            elif found.keyword in WANTED:
                # Stated without a proof. A wanted definition stays unstated,
                # because Autoform counts a stated definition as defined.
                summary["wanted"] += 1
                declaration, lean = WANTED[found.keyword], found.name
                statement, proof = found.keyword == "theorem_wanted", False
            else:
                declaration, lean = found.keyword, found.name
                is_data = declaration in DEFINITION_DECLARATIONS
                statement = not (is_data and has_sorry)
                proof = not is_data and not has_sorry
            statement_text, citations = split_docstring(doc)
            bold = BOLD_TITLE.match(statement_text)
            if bold:
                named_by_docstring.add(len(targets))
            # A bold name can wrap; a title must stay on its heading line.
            title = " ".join(bold.group("title").split()).rstrip(".") if bold else humanize(short) or first_words(statement_text)
            subject = LIBRARIES[library][1].get(module[1], module[1])
            if subject not in SUBJECTS:
                raise SystemExit(f"{relative}: no subject for directory {module[1]}")
            summary["subjects"].add(subject)
            body = "\n".join(
                "\\" + row if row.lstrip().startswith("#") else row for row in statement_text.splitlines()
            )
            targets.append(
                Target(
                    book=library,
                    idx=len(targets),
                    title=title.replace("[", "(").replace("]", ")"),
                    slug=slugify(humanize(short) or title, 40),
                    location=subject,
                    description=safe_math_markdown(body),
                    declaration=declaration,
                    lean=lean,
                    statement=statement,
                    proof=proof,
                    names=[lean or short],
                    source=(f"{library}, {'.'.join(module)}", Path("sources") / "v2" / f"{library}.md"),
                    citations=citations,
                    module=module,
                )
            )
    # A module with one article is usually named after its result.
    per_module: dict[tuple[str, ...], list[Target]] = defaultdict(list)
    for target in targets:
        per_module[target.module].append(target)
    for module, items in per_module.items():
        if len(items) == 1 and items[0].idx not in named_by_docstring:
            items[0].title = humanize(module[-1])
    return targets, summary


def library_tree(library: str, targets: list[Target]) -> Container:
    """Directories and modules below the subject directory become containers."""
    root: dict = {"dirs": {}, "modules": defaultdict(list)}
    for target in targets:
        node = root
        parts = target.module[2:] or target.module[-1:]
        for part in parts[:-1]:
            node = node["dirs"].setdefault(part, {"dirs": {}, "modules": defaultdict(list)})
        node["modules"][parts[-1]].append(target)

    def build(title: str, slug: str, node: dict) -> Container:
        children: list = [
            build(humanize(name), slugify(humanize(name)), node["dirs"][name]) for name in sorted(node["dirs"])
        ]
        for name in sorted(node["modules"]):
            items = node["modules"][name]
            children.append(items[0] if len(items) == 1 else chunk(humanize(name), slugify(humanize(name)), items))
        return chunk(title, slug, children)

    tree = build(library, library, root)
    tree.prose = LIBRARIES[library][0]
    return tree


def link_v2(targets: list[Target], dependencies: dict) -> None:
    """Add Lean dependency edges between v2 articles from sources/v2/lean-dependencies.json."""
    by_name = {target.lean: target for target in targets if target.lean}
    # Wanted entries have no `lean:` link; match them by module and short name.
    by_short = {(".".join(target.module), target.names[0]): target for target in targets if not target.lean}

    def find(name: str) -> Target | None:
        module = dependencies.get(name, {}).get("module", "")
        return by_name.get(name) or by_short.get((module, name.split(".")[-1]))

    for name, entry in dependencies.items():
        target = find(name)
        if target is None:
            continue
        seen = {id(other) for other in target.depends + target.proof_depends}
        for kind, bucket in (("statement", target.depends), ("proof", target.proof_depends)):
            for dependency in entry[kind]:
                other = find(dependency)
                if other is not None and other is not target and id(other) not in seen:
                    bucket.append(other)
                    seen.add(id(other))


def drop_cycle_closing_edges(tree: Container) -> int:
    """Keep a deterministic maximal acyclic subset of one v1 source graph.

    Edges to earlier source statements are always acyclic together and form
    the starting graph. A later-statement dependency is then retained unless
    the edges already kept provide a path back to its target. This discards
    only a feedback edge, never every dependency merely because its source
    happens to appear later in the book or wiki.
    """

    targets = [node for node in walk(tree) if isinstance(node, Target)]
    position = {id(target): number for number, target in enumerate(targets)}
    original = {
        (id(target), kind): list(bucket)
        for target in targets
        for kind, bucket in (("statement", target.depends), ("proof", target.proof_depends))
    }
    adjacency: dict[int, set[int]] = {id(target): set() for target in targets}
    kept: set[tuple[int, str, int]] = set()
    candidates: list[tuple[Target, str, int, Target]] = []
    for target in targets:
        for kind, bucket in (("statement", target.depends), ("proof", target.proof_depends)):
            for index, dependency in enumerate(bucket):
                edge = (id(target), kind, index)
                if position[id(dependency)] < position[id(target)]:
                    adjacency[id(target)].add(id(dependency))
                    kept.add(edge)
                else:
                    candidates.append((target, kind, index, dependency))

    def reaches(start: int, goal: int) -> bool:
        pending = [start]
        seen: set[int] = set()
        while pending:
            node = pending.pop()
            if node == goal:
                return True
            if node in seen:
                continue
            seen.add(node)
            pending.extend(adjacency[node] - seen)
        return False

    dropped = 0
    for target, kind, index, dependency in candidates:
        if reaches(id(dependency), id(target)):
            dropped += 1
            continue
        adjacency[id(target)].add(id(dependency))
        kept.add((id(target), kind, index))

    for target in targets:
        for kind, bucket in (("statement", target.depends), ("proof", target.proof_depends)):
            bucket[:] = [
                dependency
                for index, dependency in enumerate(original[id(target), kind])
                if (id(target), kind, index) in kept
            ]
    return dropped


def render_library_source(library: str, summary: dict) -> str:
    lines = [
        "---",
        "kind: source",
        "status: adopted",
        "---",
        "",
        f"# {library}",
        "",
        f"{LIBRARIES[library][0]} Source: <{REPOSITORY_URL}/tree/main/{library}>.",
        "",
        f"{summary['modules']} modules declare {summary['public']} public declarations. Leaving",
        f"out {summary['instances']} instances, the {summary['documented']} with a docstring are",
        "roadmap articles whose statement is that docstring, with its citations moved",
        "to the article's sources. Theorems are proved and definitions defined unless",
        "their module contains `sorry`.",
    ]
    if summary["wanted"]:
        lines += [
            "",
            f"{summary['wanted']} articles are `theorem_wanted` or `def_wanted` entries: their Lean",
            "statements exist without proofs. A wanted theorem shows as stated and unproved;",
            "a wanted definition shows as not stated, because a stated definition counts",
            "as defined.",
        ]
    if summary.get("edges"):
        lines += [
            "",
            f"{summary['edges']} roadmap edges come from the compiled Lean: the articles each",
            "article's statement or proof reaches, through private helpers and undocumented",
            "declarations if need be ([`lean-dependencies.json`](lean-dependencies.json)).",
        ]
    if summary.get("dependency_missing"):
        lines += [
            "",
            f"{summary['dependency_missing']} roadmap articles have no row in the compiled",
            "dependency dump (for example a wanted placeholder or a module excluded by a",
            "compiled-name collision), so no dependency edges are asserted for them.",
        ]
    return "\n".join(lines) + "\n"


def book_tree(book: str, targets: list[Target]) -> Container:
    chapters = [chapter(title, items) for title, items in groups(targets, lambda target: chapter_of(target.location))]
    tree = chunk(BOOKS[book][1], book, chapters)
    tree.prose = (
        f"Statements selected from [{link_text(BOOKS[book][1])}](SOURCES/v1/{book}.md) by ATLAS v1, in source order."
    )
    return tree


def assign_paths(node: Container, directory: Path) -> None:
    node.path = directory / "README.md"
    taken: set[str] = set()
    for child in node.children:
        base, number = child.slug, 1
        while child.slug in taken:
            number += 1
            child.slug = f"{base}-{number}"
        taken.add(child.slug)
        if isinstance(child, Container):
            assign_paths(child, directory / child.slug)
        else:
            child.path = directory / f"{child.slug}.md"


def rel(source: Path, target: Path) -> str:
    """Relative link from one vault file to another."""
    common = 0
    for left, right in zip(source.parent.parts, target.parts):
        if left != right:
            break
        common += 1
    up = len(source.parent.parts) - common
    return "/".join([".."] * up + list(target.parts[common:]))


def frontmatter(fields: list[tuple[str, str]], previous: str | None) -> str:
    match = ARTICLE_ID.search(previous or "")
    lines = ([f"article_id: {match.group(1)}"] if match else []) + [f"{key}: {value}" for key, value in fields]
    return "---\n" + "\n".join(lines) + "\n---\n\n" if lines else ""


def render_container(node: Container, previous: str | None, extra: str = "") -> str:
    vault_path = node.path.relative_to(VAULT)
    lines = [f"# {node.title}", ""]
    if node.prose:
        lines += [node.prose.replace("SOURCES/", rel(vault_path, Path("sources")) + "/"), ""]
    if extra:
        lines += [extra, ""]
    for child in node.children:
        target = child.path.relative_to(VAULT)
        lines.append(f"- [{link_text(child.title)}]({rel(vault_path, target)})")
    return frontmatter([], previous) + "\n".join(lines) + "\n"


def render_target(target: Target, previous: str | None) -> str:
    vault_path = target.path.relative_to(VAULT)
    fields = [("declaration", target.declaration), ("origin", "cited")]
    if target.statement:
        fields.append(("statement", "formalized"))
    if target.proof:
        fields.append(("proof", "formalized"))
    if target.lean:
        fields.append(("lean", target.lean))
    lines = [f"# {target.title}", "", target.description, "", "## Depends on", ""]
    if target.depends:
        lines += [f"- [{link_text(o.title)}]({rel(vault_path, o.path.relative_to(VAULT))})" for o in target.depends]
    else:
        lines.append("This node has no prerequisites.")
    if target.proof_depends:
        lines += ["", "## Proof depends on", ""]
        lines += [
            f"- [{link_text(o.title)}]({rel(vault_path, o.path.relative_to(VAULT))})" for o in target.proof_depends
        ]
    label, page = target.source or (
        f"{BOOKS[target.book][1]}, {target.location}",
        Path("sources") / "v1" / f"{target.book}.md",
    )
    lines += ["", "## Sources", "", f"- [{link_text(label)}]({rel(vault_path, page)})"]
    lines += [f"- {citation}" for citation in target.citations]
    return frontmatter(fields, previous) + "\n".join(lines) + "\n"


def walk(node: Container):
    yield node
    for child in node.children:
        if isinstance(child, Container):
            yield from walk(child)
        else:
            yield child


def book_urls() -> dict[str, str]:
    text = (V1 / "README.md").read_text()
    return dict(re.findall(r"^\| \[(\w+)\]\((\S+)\) \|", text, re.M))


def render_source(book: str, url: str, summary: dict) -> str:
    blob = f"{REPOSITORY_URL}/blob/main/v1/Atlas/{book}"
    lines = [
        "---",
        "kind: source",
        "status: adopted",
        "---",
        "",
        f"# {BOOKS[book][1]}",
        "",
        f"Stable public record: <{url}>.",
        "",
        f"ATLAS v1 selected {summary['targets']} statements from this source in",
        f"[`targets.yaml`]({blob}/targets.yaml) and evaluated the Lean declaration",
        f"matched to each in [`report.json`]({blob}/report.json). Each roadmap article",
        "reproduces one target's statement and the source location it names.",
    ]
    if summary["book_edges"]:
        lines += [
            "",
            f"{summary['book_edges']} roadmap edges come from the source text rather than",
            f"the Lean code; each is recorded with its evidence in",
            f"[`book-dependencies/{book}.json`](book-dependencies/{book}.json).",
        ]
    if summary["cycle_edges"]:
        lines += [
            "",
            f"{summary['cycle_edges']} candidate dependencies are not drawn because adding",
            "them would create a cycle between source statements. Every other verified",
            "dependency is retained, including relations in both directions between chapters.",
        ]
    missing = summary["unmatched"] + summary["unresolved"]
    if missing:
        lines += [
            "",
            "## Targets without a linked Lean declaration",
            "",
            "These targets have no `lean:` link: v1 matched no declaration, the",
            "matched name is not found by Autoform's lexical scan, or another v1 book",
            "or a root library declares the same name.",
            "",
            "| Target | v1 match |",
            "| --- | --- |",
        ]
        for item in sorted(missing, key=lambda item: item["idx"]):
            match = item.get("lean_declaration") or item.get("match_confidence") or "none"
            lines.append(f"| {link_text(' '.join(item['name'].split()))} | `{match}` |")
    return "\n".join(lines) + "\n"


def render_coverage(rows: list[tuple[str, str, str]]) -> str:
    lines = [
        "---",
        "kind: coverage",
        "status: in-progress",
        "---",
        "",
        "# ATLAS coverage",
        "",
        "Every documented public declaration of the ATLAS v2 libraries and every",
        "ATLAS v1 textbook target has one roadmap article. The standalone `Atlas/`",
        "developments are not decomposed yet. Progress percentages and target counts",
        "cover only the decomposed rows below; they are not repository-wide coverage.",
        "",
        "| Area | Coverage | Evidence |",
        "| --- | --- | --- |",
    ]
    lines += [f"| {area} | {coverage} | {evidence} |" for area, coverage, evidence in rows]
    return "\n".join(lines) + "\n"


def render_roadmap_root(subjects: list[str], previous: str | None) -> str:
    lines = [
        "# ATLAS roadmap",
        "",
        "ATLAS v2 is the root Lake package: MathlibExt and CSLibExt hold reusable,",
        "fully proved results, and WantedExt states established results whose proofs",
        "are deferred. Each subject below leads with those libraries. The 26",
        "textbooks and lecture notes formalized by the archived ATLAS v1 release follow",
        "as source tracks whose articles reproduce the source statements in order.",
        "Standalone developments under `Atlas/` remain outside these roadmap and progress",
        "counts until their `MAPPED` coverage rows are decomposed.",
        "",
        "## Subjects",
        "",
    ]
    lines += [f"- [{SUBJECTS[subject][0]}]({subject}/README.md)" for subject in subjects]
    return frontmatter([], previous) + "\n".join(lines) + "\n"


def generate(selected: list[str]) -> dict[Path, str]:
    index = index_project(ROOT)
    lean_dependencies = json.loads((SOURCES / "v1" / "lean-dependencies.json").read_text())["books"]
    urls = book_urls()
    files: dict[Path, str] = {}
    previous = lambda path: path.read_text() if path.is_file() else None  # noqa: E731
    coverage = []
    by_subject: dict[str, list[Container]] = defaultdict(list)
    for book in selected:
        targets, summary = load_book(book, index, lean_dependencies.get(book, {}))
        subject = BOOKS[book][0]
        tree = book_tree(book, targets)
        assign_paths(tree, ROADMAP / subject / book)
        summary["cycle_edges"] = drop_cycle_closing_edges(tree)
        summary["book_edges"] = sum(
            (target.idx, other.idx) in summary["book_pairs"]
            for target in targets
            for other in target.depends + target.proof_depends
        )
        for node in walk(tree):
            if isinstance(node, Container):
                files[node.path] = render_container(node, previous(node.path))
            else:
                files[node.path] = render_target(node, previous(node.path))
        files[SOURCES / "v1" / f"{book}.md"] = render_source(book, urls[book], summary)
        by_subject[subject].append(tree)
        formalized = sum(target.statement for target in targets)
        coverage.append(
            (
                f"v1 / {book}",
                "DECOMPOSED",
                f"[{len(targets)} source statements](../roadmap/{subject}/{book}/README.md), "
                f"{formalized} with a formalized statement.",
            )
        )
    v2_coverage = []
    v2_by_subject: dict[str, list[Container]] = defaultdict(list)
    v2_loaded = {library: load_library(library, index) for library in LIBRARIES}
    for library, (targets, summary) in v2_loaded.items():
        for subject in sorted(summary["subjects"]):
            tree = library_tree(library, [target for target in targets if target.location == subject])
            assign_paths(tree, ROADMAP / subject / library)
            v2_by_subject[subject].append(tree)
    dependency_file = SOURCES / "v2" / "lean-dependencies.json"
    dependency_data = None
    if dependency_file.is_file():
        dependency_data = json.loads(dependency_file.read_text())
        link_v2(
            [target for targets, _ in v2_loaded.values() for target in targets],
            dependency_data["articles"],
        )
    every_v2 = Container("v2", "v2", [tree for subject in sorted(v2_by_subject) for tree in v2_by_subject[subject]])
    for node in walk(every_v2):
        if node is not every_v2:
            render = render_container if isinstance(node, Container) else render_target
            files[node.path] = render(node, previous(node.path))
    for library, (targets, summary) in v2_loaded.items():
        summary["edges"] = sum(len(target.depends) + len(target.proof_depends) for target in targets)
        summary["dependency_missing"] = len((dependency_data or {}).get("missing_articles", {}).get(library, ()))
        files[SOURCES / "v2" / f"{library}.md"] = render_library_source(library, summary)
        first = sorted(summary["subjects"])[0]
        v2_coverage.append(
            (
                f"v2 / {library}",
                "DECOMPOSED",
                f"[{summary['documented']} documented public declarations](../roadmap/{first}/{library}/README.md) "
                f"across {len(summary['subjects'])} subjects; {summary['instances']} instances and "
                f"{summary['public'] - summary['instances'] - summary['documented']} undocumented public "
                "declarations are not articles.",
            )
        )
    statistical_mechanics_files = sum(1 for _ in (ROOT / "Atlas" / "StatisticalMechanics").rglob("*.lean"))
    fc_files = sum(1 for _ in (ROOT / "Atlas" / "FC").rglob("*.lean"))
    coverage = v2_coverage + coverage + [
        ("v2 tests (MathlibExtTest, CSLibExtTest)", "OUT", "Tests and diagnostics rather than mathematical results."),
        (
            "Atlas/StatisticalMechanics",
            "MAPPED",
            f"{statistical_mechanics_files} standalone Lean files; no roadmap articles yet.",
        ),
        ("Atlas/FC", "MAPPED", f"{fc_files} standalone Lean files; no roadmap articles yet."),
        ("Atlas/CPythonListsort", "OUT", "Maintained as its own Autoform blueprint inside Atlas/CPythonListsort."),
    ]
    subjects = sorted(set(by_subject) | set(v2_by_subject))
    for subject in subjects:
        trees = v2_by_subject[subject] + by_subject[subject]
        node = Container(SUBJECTS[subject][0], subject, trees, prose=SUBJECTS[subject][1])
        node.path = ROADMAP / subject / "README.md"
        files[node.path] = render_container(node, previous(node.path))
    root = ROADMAP / "README.md"
    files[root] = render_roadmap_root(subjects, previous(root))
    files[VAULT / "coverage" / "README.md"] = render_coverage(coverage)
    sources = ["# ATLAS source catalog", "", "## ATLAS v2", ""]
    sources += [f"- [{library}](v2/{library}.md)" for library in LIBRARIES]
    sources += ["", "## ATLAS v1 textbooks", ""]
    sources += [f"- [{BOOKS[book][1]}](v1/{book}.md)" for book in selected]
    files[SOURCES / "README.md"] = "\n".join(sources) + "\n"
    return files


def owned(selected: list[str]) -> set[Path]:
    """Existing files the generator owns, so stale pages can be removed."""
    directories = [ROADMAP / BOOKS[book][0] / book for book in selected]
    directories += [directory for library in LIBRARIES for directory in ROADMAP.glob(f"*/{library}")]
    paths = set()
    for directory in directories:
        if directory.is_dir():
            paths.update(path for path in directory.rglob("*.md"))
    return paths


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--check", action="store_true", help="fail if any generated page is stale")
    parser.add_argument("--book", action="append", choices=sorted(BOOKS), help="limit to one v1 book (repeatable)")
    args = parser.parse_args()
    selected = args.book or sorted(BOOKS)
    files = generate(selected)
    stale = sorted(owned(selected) - set(files))
    changed = sorted(path for path, text in files.items() if not path.is_file() or path.read_text() != text)
    if args.check:
        for path in changed + stale:
            print(f"stale: {path.relative_to(ROOT)}", file=sys.stderr)
        return 1 if changed or stale else 0
    for path in stale:
        path.unlink()
    for path in changed:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(files[path])
    print(f"{len(files)} pages, {len(changed)} written, {len(stale)} removed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
