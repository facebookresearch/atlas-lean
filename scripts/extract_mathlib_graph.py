#!/usr/bin/env python3
"""The Mathlib layer of the dependency graph, computed from compiled Lean.

    scripts/extract_mathlib_graph.py dump [--modules LIST] [--keep ROOTS] [--shards N] [--jobs J] DUMP.jsonl.gz
    scripts/extract_mathlib_graph.py graph DUMP.jsonl.gz OUTDIR
    scripts/extract_mathlib_graph.py bridge V2_DUMP.jsonl.gz OUTDIR
    scripts/extract_mathlib_graph.py join [--taxonomy TAXONOMY.json] [--strict] OUTDIR [PLACEMENTS.json ...]
    scripts/extract_mathlib_graph.py stats OUTDIR

`dump` runs scripts/dump_mathlib_dependencies.lean over every Mathlib module (or the listed ones), in parallel
shards that each import all of them, and merges the rows by name. `graph` turns the rows into the graph: its
nodes are the Mathlib declarations a mathematician could cite (RULES says which constants are not, and
graph-meta.json counts what each rule removes), and its statement and proof edges collapse what a node uses onto
nodes exactly as scripts/extract_v2_lean_dependencies.py collapses ATLAS's own declarations onto articles: the
body of a definition, of an `abbrev` and of an instance of a class of data (all compiled as definitions), and an
inductive type's constructors, are part of what it states; a theorem's proof, a proposition-valued instance's
included (it compiles to a theorem), and an `opaque` body give proof edges only; uses reach through constants
that are not nodes (through what a hidden constant states, for statement edges); and statement edges inside a
mutual group are left out and the group is listed. `bridge` adds the edges from ATLAS's articles (the Lean names
that blueprint/links annotations link, as Autoform reads them) to the Mathlib nodes they use, from a dump of the
v2 modules that keeps Mathlib constants. `join` gives every node the topic of its module in the taxonomy's
`placements` (its own key, else its nearest placed directory), or the reason in `mathlib_exclusions`. `stats`
summarises the outputs in stats.json. docs/mathlib-layer.md describes the rules and the files; the build
produces them and they are never committed.
"""

from __future__ import annotations

import argparse
import collections
import concurrent.futures
import functools
import gzip
import io
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import extract_v2_lean_dependencies as v2  # noqa: E402  (the shared collapse semantics)

ROOT = Path(__file__).resolve().parent.parent
DUMP_SCRIPT = ROOT / "scripts" / "dump_mathlib_dependencies.lean"
MATHLIB_PACKAGE = Path(".lake") / "packages" / "mathlib"
V2_KEEP = "Mathlib,MathlibExt,CSLibExt,PhyslibExt,Domains,WantedExt"
TAXONOMY = ROOT / "scripts" / "taxonomy.json"

# Modules with no mathematics for the graph: tactics, metaprogramming, linters and test infrastructure, and
# the deprecated archive. Their constants stay in the dump, so edges still reach through them.
EXCLUDED_DIRECTORIES = ("Mathlib.Tactic", "Mathlib.Lean", "Mathlib.Util", "Mathlib.Testing", "Mathlib.Deprecated")
EXCLUDED_MODULES = ("Mathlib.Init", "Mathlib.Tactic")

# Why a Mathlib constant is not a node, in the order the rules apply: a constant is counted under the first
# rule it meets. `lean:*` are Lean's own predicates for generated machinery (the dump's `aux`).
RULES = (
    "excluded_module",  # declared in an excluded module (EXCLUDED_DIRECTORIES, EXCLUDED_MODULES)
    "private",  # private name, including a `module` file's non-public declarations
    "lean:internal",  # `_`-prefixed or numeric name part, `eq_1`, `match_1`, `proof_1`, ...: `Name.isInternalDetail`
    "lean:recursor",  # `T.rec`
    "lean:aux_recursor",  # `casesOn`, `recOn`, `brecOn`, `below`, ...: `isAuxRecursor`, sparse `casesOn`
    "lean:no_confusion",  # `noConfusion`, `noConfusionType`
    "lean:matcher",  # `match_1` matchers
    "lean:reserved",  # reserved names realised on demand: `eq_def`, `induct`, `fun_cases`, `congr_simp`, ...
    "constructor",  # constructors: their types are part of their inductive type's statement
    "generated",  # no declaration range: made by a command or attribute (`ctorIdx`, `mk.injEq`, `sizeOf_spec`)
    "deprecated",  # `@[deprecated]`
    "metaprogramming",  # `meta`/`unsafe` code, a type about Lean's metaprogramming, a tactic or display instance
    "data_field",  # the projection of a structure's own field that is not a proposition (data, not an axiom)
)
NODE = "node"
# Constant kinds whose value is part of what they state (`abbrev`, and `instance` of a class of data, compile to
# `def`; an `instance` of a proposition compiles to `theorem`, whose value is a proof).
STATEMENT_VALUE = v2.STATEMENT_VALUE


def module_key(module: str) -> str:
    """`Mathlib.Topology.Basic` -> `Mathlib/Topology/Basic`, the taxonomy's key for the module."""
    return module.replace(".", "/")


def write_jsonl_gz(path: Path, rows) -> int:
    """Write rows as gzipped JSON lines: the same rows give the same lines, and the same file with the same zlib."""
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with open(path, "wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0, compresslevel=6) as gz:
        with io.TextIOWrapper(gz, encoding="utf-8", newline="\n") as text:
            for row in rows:
                text.write(json.dumps(row, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n")
                count += 1
    return count


def read_jsonl(path: Path):
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                yield json.loads(line)


def write_json(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=1, sort_keys=True) + "\n", encoding="utf-8")


# --------------------------------------------------------------------------------------------------- dump


def mathlib_modules(lean_root: Path) -> list[str]:
    """Every module of the Mathlib package Lake checked out: `Mathlib` and each `Mathlib/**/*.lean`."""
    package = lean_root / MATHLIB_PACKAGE
    listed = subprocess.run(["git", "-C", str(package), "ls-files", "--", "Mathlib.lean", "Mathlib/*.lean"],
                            check=True, capture_output=True, text=True).stdout.split()
    modules = sorted(path[: -len(".lean")].replace("/", ".") for path in listed)
    olean_root = package / ".lake" / "build" / "lib" / "lean"
    missing = [m for m in modules if not (olean_root / (m.replace(".", "/") + ".olean")).is_file()]
    if missing:
        raise SystemExit(f"{len(missing)} Mathlib modules have no compiled .olean (first: {missing[:5]}); "
                         "run `lake exe cache get`")
    return modules


def toolchain_facts(lean_root: Path) -> dict:
    manifest = json.loads((lean_root / "lake-manifest.json").read_text(encoding="utf-8"))
    revs = {package["name"]: package["rev"] for package in manifest["packages"]}
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=lean_root, check=True,
                             capture_output=True, text=True).stdout.strip()
    head = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True)
    return {
        "lean_toolchain": (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_version": version,
        "mathlib_rev": revs.get("mathlib"),
        "package_revs": dict(sorted(revs.items())),
        "atlas_commit": head.stdout.strip() if head.returncode == 0 else None,
    }


def run_dump(modules: list[str], keep: str, shards: int, jobs: int, out: Path, lean_root: Path) -> dict:
    """Run the Lean dump in shards, merge the rows sorted by name, and return the run's facts."""
    started = time.time()
    with tempfile.TemporaryDirectory(prefix="mathlib-dump-") as directory:
        listing = Path(directory) / "modules.txt"
        listing.write_text("".join(f"{module}\n" for module in modules), encoding="utf-8")

        def shard(index: int) -> tuple[int, float, Path]:
            target = Path(directory) / f"shard-{index}.jsonl"
            began = time.time()
            with open(target, "wb") as stdout, open(Path(directory) / f"shard-{index}.err", "wb") as stderr:
                result = subprocess.run(["lake", "env", "lean", "--run", str(DUMP_SCRIPT), str(listing), keep,
                                         str(index), str(shards)], cwd=lean_root, stdout=stdout, stderr=stderr)
            if result.returncode != 0:
                tail = (Path(directory) / f"shard-{index}.err").read_text(errors="replace")[-2000:]
                raise RuntimeError(f"shard {index} failed with exit code {result.returncode}:\n{tail}")
            return index, time.time() - began, target

        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
            results = sorted(pool.map(shard, range(shards)))
        rows = []
        for _, _, target in results:
            rows.extend(read_jsonl(target))
    rows.sort(key=lambda row: row["name"])
    names = [row["name"] for row in rows]
    if len(set(names)) != len(names):
        raise SystemExit("the shards wrote a constant twice")
    write_jsonl_gz(out, rows)
    return {
        "modules": len(modules),
        "keep": keep.split(","),
        "shards": shards,
        "jobs": jobs,
        "rows": len(rows),
        "shard_seconds": [round(seconds, 1) for _, seconds, _ in results],
        "seconds": round(time.time() - started, 1),
    }


def command_dump(args: argparse.Namespace) -> int:
    lean_root = Path(args.lean_root).resolve()
    if args.modules:
        modules = [line.strip() for line in Path(args.modules).read_text(encoding="utf-8").splitlines() if line.strip()]
    else:
        modules = mathlib_modules(lean_root)
    jobs = args.jobs or max(1, min(16, os.cpu_count() or 1))
    shards = args.shards or 2 * jobs
    out = Path(args.output)
    facts = toolchain_facts(lean_root)
    facts["dump"] = run_dump(modules, args.keep, shards, jobs, out, lean_root)
    write_json(out.with_name(out.name.split(".")[0] + "-meta.json"), facts)
    print(f"{facts['dump']['rows']} constants from {len(modules)} modules in {facts['dump']['seconds']} s -> {out}")
    return 0


# --------------------------------------------------------------------------------------------------- graph

# Namespace roots that hold Mathlib's tactic and metaprogramming code (`Mathlib.Meta.NormNum`, `Mathlib.Tactic`,
# `Lean.Expr.ineq?`, ...). Mathlib states no mathematics in them.
META_NAMESPACES = frozenset({"Mathlib", "Lean", "Qq", "Aesop", "ProofWidgets", "Plausible"})
# A type that uses one of these constants (the dump's `type_meta`) is about Lean's syntax, expressions or
# elaboration. Lean's other namespaces (`Lean.Grind`, `Lean.Internal`) also occur in statements of mathematics.
META_TYPE_PREFIXES = (
    "Lean.Expr", "Lean.Syntax", "Lean.TSyntax", "Lean.Name", "Lean.Level", "Lean.Meta.", "Lean.Elab.",
    "Lean.Parser", "Lean.ParserDescr", "Lean.TrailingParserDescr", "Lean.PrettyPrinter.", "Lean.Macro",
    "Lean.MVarId", "Lean.FVarId", "Lean.Json", "Lean.ToExpr", "Lean.Widget.", "Lean.Server.", "Qq.",
    "ProofWidgets.",
)
# Classes whose instances only print or hash values.
DISPLAY_CLASSES = frozenset({"Repr", "ToString", "Std.ToFormat", "Hashable"})
DIRECT = "direct"


def excluded_module(module: str) -> bool:
    return module in EXCLUDED_MODULES or any(module == d or module.startswith(d + ".") for d in EXCLUDED_DIRECTORIES)


def metaprogramming(row: dict) -> bool:
    if row["meta"] or row["unsafe"]:
        return True
    if row["name"].split(".", 1)[0] in META_NAMESPACES:
        return True
    if any(use.startswith(META_TYPE_PREFIXES) for use in row["type_meta"]):
        return True
    head = row.get("head") or ""
    # Instances of Lean's tactic classes (`Lean.Grind.CommRing`, `Lean.ToExpr`) and of display classes.
    return bool(row["instance"]) and (head.startswith("Lean.") or head in DISPLAY_CLASSES)


def removal_rule(row: dict) -> str:
    """The first rule in RULES that keeps the constant out of the node set, or NODE."""
    if excluded_module(row["module"]):
        return "excluded_module"
    if row["private"]:
        return "private"
    if row["aux"]:
        return "lean:" + row["aux"]
    if row["kind"] == "constructor":
        return "constructor"
    if row["line"] is None:
        return "generated"
    if row["deprecated"] is not None:
        return "deprecated"
    if metaprogramming(row):
        return "metaprogramming"
    if row.get("projection") and not parent_projection(row) and row.get("prop") is not True:
        return "data_field"
    return NODE


def parent_projection(row: dict) -> bool:
    """`toB` of a structure or class extending `B`. A class's is an instance; a structure's (`RingHom.toMonoidHom`)
    is a definition in its own right. Both stay nodes: when `B` shares fields with another parent, `toB` is a
    definition that rebuilds `B` from the fields, axioms included, and reaching through it would make every
    statement that uses it depend on those axioms."""
    projection = row.get("projection")
    return bool(row.get("parent_projection") or (projection and projection["subobject"]))


def node_kind(row: dict) -> str:
    if row["instance"]:
        return "instance"
    if row.get("projection") and row.get("prop"):
        return "field"  # a field that states an axiom (a parent's, for a proposition-valued parent)
    if parent_projection(row):
        return "definition"
    if row["kind"] == "inductive":
        return "class" if row["class"] else "structure" if row["structure"] else "inductive"
    if row["kind"] == "def":
        return "abbreviation" if row["reducibility"] == "reducible" else "definition"
    return row["kind"]  # theorem, opaque, axiom


def gather(uses: list[str], through: dict[str, frozenset[str]], nodes, rule_of: dict[str, str],
           found: dict[str, set[str]], alias: dict[str, str | None] | None = None, name: str | None = None) -> None:
    """Add the nodes that *uses*, an expression of *name*, reach, each with how: directly, or through hidden constants
    of which rules. A use of a duplicate (*alias*, see extract_v2_lean_dependencies.frontiers) is a use of its
    article, and so counts as direct: the duplicate states the article's result; one whose article is gone reaches
    nothing. A duplicate of *name*'s own is part of it, as in the v2 extraction: *uses* come with those it names
    replaced by what they use (extract_v2_lean_dependencies.own_duplicates), a direct use of theirs being one of
    *name*'s. One reached otherwise, through hidden constants or through another of its duplicates, reaches what it
    reaches itself, as a hidden constant does."""
    alias = alias or {}
    for use in uses:
        if use in nodes:
            found.setdefault(use, set()).add(DIRECT)
        elif use in alias and alias[use] != name:
            if alias[use] is not None:
                found.setdefault(alias[use], set()).add(DIRECT)
        else:
            rule = rule_of.get(use, "outside")
            for target in v2.through_aliases(name, through.get(use, frozenset()), through, alias):
                found.setdefault(target, set()).add(rule)


def collapse(rows: dict[str, dict], nodes, sources, rule_of: dict[str, str],
             alias: dict[str, str | None] | None = None) -> tuple[list[dict], list[list[str]], dict]:
    """Statement and proof edges from each name in *sources* to *nodes*, with extract_v2_lean_dependencies.py's
    semantics, the mutual groups whose statement edges to each other are left out, and edge counts."""
    alias = alias or {}
    reach_statement = v2.frontiers(rows, nodes, statement=True, alias=alias)
    reach = v2.frontiers(rows, nodes, alias=alias)
    found_statement: dict[str, dict[str, tuple[str, set[str]]]] = {}
    found_proof: dict[str, dict[str, set[str]]] = {}
    for name in sources:
        row = rows[name]
        by_type: dict[str, set[str]] = {}
        by_value: dict[str, set[str]] = {}
        # The source's own duplicates are part of it: what they use, it uses.
        own_type = v2.own_duplicates(name, row["type"], rows, alias, True)[0]
        gather(own_type, reach_statement, nodes, rule_of, by_type, alias, name)
        statement: dict[str, tuple[str, set[str]]] = {}
        proof: dict[str, set[str]] = {}
        if row["kind"] in STATEMENT_VALUE:
            own_value = v2.own_duplicates(name, row["value"], rows, alias, True)[0]
            gather(own_value, reach_statement, nodes, rule_of, by_value, alias, name)
        else:
            own_value = v2.own_duplicates(name, row["value"], rows, alias, False)[0]
            gather(own_value, reach, nodes, rule_of, proof, alias, name)
        for target, how in by_value.items():
            statement[target] = ("value", how)
        for target, how in by_type.items():
            statement[target] = ("type", how | by_value.get(target, set()))
        statement.pop(name, None)
        proof = {target: how for target, how in proof.items() if target != name and target not in statement}
        found_statement[name], found_proof[name] = statement, proof
    groups = v2.mutual_groups({name: set(edges) for name, edges in found_statement.items()})
    for group in groups:
        members = set(group)
        for name in group:
            found_statement[name] = {t: e for t, e in found_statement[name].items() if t not in members}
    edges: list[dict] = []
    counts = {"statement": collections.Counter(), "proof": collections.Counter()}
    via = {"statement": collections.Counter(), "proof": collections.Counter()}
    only_via = {"statement": collections.Counter(), "proof": collections.Counter()}

    def edge(name: str, target: str, kind: str, part: str, how: set[str]) -> dict:
        direct = DIRECT in how
        through = [] if direct else sorted(how)
        counts[kind][part] += 1
        counts[kind]["direct" if direct else "collapsed"] += 1
        for rule in through:
            via[kind][rule] += 1
        if len(through) == 1:
            only_via[kind][through[0]] += 1
        return {"source": name, "target": target, "kind": kind, "part": part, "direct": direct, "through": through}

    for name in sources:
        for target in sorted(found_statement[name]):
            part, how = found_statement[name][target]
            edges.append(edge(name, target, "statement", part, how))
        for target in sorted(found_proof[name]):
            edges.append(edge(name, target, "proof", "value", found_proof[name][target]))
    report = {
        "edges": {kind: dict(sorted(counter.items())) for kind, counter in counts.items()},
        # Collapsed edges by the rule of the hidden constant they pass through first: `through` counts an edge
        # under every such rule, `only_through` only when that rule's constants are its sole way in.
        "through": {kind: dict(sorted(counter.items())) for kind, counter in via.items()},
        "only_through": {kind: dict(sorted(counter.items())) for kind, counter in only_via.items()},
    }
    return edges, groups, report


def node_row(row: dict, partners: dict[str, dict[str, str]]) -> dict:
    kind = node_kind(row)
    out = {
        "name": row["name"],
        "module": row["module"],
        "key": module_key(row["module"]),
        "kind": kind,
        "lean_kind": row["kind"],
        "line": row["line"],
        "name_line": row["name_line"],
        "doc": row["doc"],
        "has_doc": row["doc"] is not None,
        "signature": row["signature"],
        "proposition": row.get("prop"),
        "simp": row["simp"],
        "additive": partners["additive"].get(row["name"]),
        "multiplicative": partners["multiplicative"].get(row["name"]),
        "dual": partners["dual"].get(row["name"]),
    }
    if kind == "instance":
        out["instance_of"] = row.get("head")
    if row.get("projection"):
        out["projection_of"] = row["projection"]["structure"]
    elif row.get("parent_projection"):
        out["projection_of"] = row["parent_projection"]  # a parent's generated `toB`, not a projection function
    if parent_projection(row):
        out["parent_projection"] = True
    return out


def translation_partners(rows) -> dict[str, dict[str, str]]:
    """`to_additive` partners both ways, and `to_dual` partners made symmetric."""
    additive, multiplicative, dual = {}, {}, {}
    for row in rows:
        name = row["name"]
        target = row.get("to_additive")
        if target and target != name:
            additive[name] = target
            multiplicative.setdefault(target, name)
        target = row.get("to_dual")
        if target and target != name:
            dual[name] = target
            dual.setdefault(target, name)
    return {"additive": additive, "multiplicative": multiplicative, "dual": dual}


def slim(row: dict) -> dict:
    """What collapsing needs of a row."""
    return {"name": row["name"], "module": row["module"], "kind": row["kind"], "type": row["type"],
            "value": row["value"]}


def load_classified(path: Path) -> tuple[dict[str, dict], dict[str, str], dict[str, dict], list[dict]]:
    """The dump's rows (slimmed), each constant's rule, the full rows of the nodes, and translation rows."""
    rows, rule_of, full, translations = {}, {}, {}, []
    for row in read_jsonl(path):
        name = row["name"]
        rule_of[name] = removal_rule(row)
        if rule_of[name] == NODE:
            full[name] = row
        if row.get("to_additive") or row.get("to_dual"):
            translations.append({"name": name, "to_additive": row.get("to_additive"), "to_dual": row.get("to_dual")})
        rows[name] = slim(row)
    return rows, rule_of, full, translations


def command_graph(args: argparse.Namespace) -> int:
    started = time.time()
    out = Path(args.outdir)
    rows, rule_of, full, translations = load_classified(Path(args.dump))
    loaded = time.time()
    nodes = frozenset(full)
    removed = collections.Counter(rule_of.values())
    removed_by_kind: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    examples: dict[str, list[str]] = collections.defaultdict(list)
    for name in sorted(rows):
        rule = rule_of[name]
        removed_by_kind[rule][rows[name]["kind"]] += 1
        if len(examples[rule]) < 5:
            examples[rule].append(name)
    generated_suffixes = collections.Counter(name.rsplit(".", 1)[-1] for name, rule in rule_of.items()
                                             if rule == "generated")
    edges, groups, report = collapse(rows, nodes, sorted(nodes), rule_of)
    collapsed = time.time()
    partners = translation_partners(translations)
    write_jsonl_gz(out / "nodes.jsonl.gz", (node_row(full[name], partners) for name in sorted(nodes)))
    write_jsonl_gz(out / "edges.jsonl.gz", edges)
    statement_cycles = v2.mutual_groups(collections.defaultdict(set, _adjacency(edges, ("statement",))))
    all_cycles = v2.mutual_groups(collections.defaultdict(set, _adjacency(edges, ("statement", "proof"))))
    meta = {
        "constants": len(rows),
        "nodes": len(nodes),
        "rules": [{"rule": rule, "removed": removed.get(rule, 0),
                   "by_lean_kind": dict(sorted(removed_by_kind[rule].items())), "examples": examples[rule]}
                  for rule in RULES],
        "node_rule": {"kept": removed.get(NODE, 0), "by_lean_kind": dict(sorted(removed_by_kind[NODE].items()))},
        "generated_suffixes": dict(generated_suffixes.most_common(30)),
        "mutual_groups": groups,
        "statement_cycles_after_mutual": statement_cycles,
        "cycles_statement_and_proof": all_cycles,
        **report,
        "seconds": {"load": round(loaded - started, 1), "collapse": round(collapsed - loaded, 1),
                    "total": round(time.time() - started, 1)},
    }
    write_json(out / "graph-meta.json", meta)
    print(f"{len(rows)} constants, {len(nodes)} nodes, {len(edges)} edges, {len(groups)} mutual groups -> {out}")
    return 0


def _adjacency(edges: list[dict], kinds: tuple[str, ...]) -> dict[str, set[str]]:
    adjacency: dict[str, set[str]] = {}
    for edge in edges:
        if edge["kind"] in kinds:
            adjacency.setdefault(edge["source"], set()).add(edge["target"])
    return adjacency


# -------------------------------------------------------------------------------------------------- bridge


def read_aliases(path: str | None) -> dict[str, str]:
    """The duplicates and their articles a file gives, one `name<TAB>article` a line (see
    extract_v2_lean_dependencies.article_aliases); none without a file."""
    if path is None:
        return {}
    aliases: dict[str, str] = {}
    for number, line in enumerate(Path(path).read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) != 2 or not all(field.strip() == field and field for field in fields) or fields[0] in aliases:
            raise SystemExit(f"{path}, line {number}: not `name<TAB>article`, each name once")
        aliases[fields[0]] = fields[1]
    return aliases

ATLAS_HIDDEN = "atlas_non_article"  # how a bridge edge passes through an ATLAS constant that no article links


def compare_with_v2(edges: list[dict], articles: set[str], v2_output: Path) -> dict:
    """Check the ATLAS-to-ATLAS edges against extract_v2_lean_dependencies.py's output for the same build: the same
    articles, and for each the same statement and proof edges. An article that only one side has is a difference:
    otherwise a dump that left out a module would pass with the articles it still had."""
    expected = json.loads(v2_output.read_text(encoding="utf-8"))["articles"]
    missing = sorted(expected.keys() - articles)  # compiled articles of the v2 extraction that the dump lacks
    unexpected = sorted(articles - expected.keys())
    found: dict[str, dict[str, set[str]]] = {name: {"statement": set(), "proof": set()} for name in articles}
    for edge in edges:
        if edge["target"] in articles:
            found[edge["source"]][edge["kind"]].add(edge["target"])
    differing = sorted(name for name in articles & expected.keys()
                       if any(set(expected[name][kind]) != found[name][kind] for kind in ("statement", "proof")))
    return {"articles_compared": len(articles & expected.keys()), "articles_differing": len(differing),
            "examples": differing[:10], "missing_articles": len(missing), "missing_examples": missing[:10],
            "unexpected_articles": len(unexpected), "unexpected_examples": unexpected[:10]}


def command_bridge(args: argparse.Namespace) -> int:
    started = time.time()
    out = Path(args.outdir)
    rows, rule_of, full, _ = load_classified(Path(args.mathlib_dump))
    mathlib_nodes = frozenset(full)
    del full
    if args.aliases is not None and args.articles is None:
        raise SystemExit("--aliases goes with --articles: without them, both are read from blueprint/")
    # The annotations' problems stop the bridge before it writes, as they stop the v2 extraction.
    try:
        manifest = v2.article_manifest() if args.articles is None else set(
            line.strip() for line in Path(args.articles).read_text(encoding="utf-8").splitlines() if line.strip())
        # The duplicates the annotations list, or those --aliases gives beside --articles (none without it, so that
        # such a run needs no Autoform), collapsed onto their articles as the v2 extraction collapses them.
        listed = v2.article_aliases() if args.articles is None else read_aliases(args.aliases)
    except ValueError as error:
        raise SystemExit(str(error)) from None
    project_rows = v2.read_dump(Path(args.v2_dump))[0]
    collisions = v2.private_collisions(project_rows, listed.keys() | set(listed.values()))
    atlas_rows = v2.publish_private_targets(project_rows, manifest | listed.keys())
    # A reserved name that both a v2 module and a Mathlib module the v2 module does not import realise on
    # demand (`AddMonoidHom.mk.congr_simp`) is in both dumps: the two are the same generated lemma.
    realised_twice = sorted(atlas_rows.keys() & rows.keys())
    if manifest.intersection(realised_twice) or any(rule_of[name] == NODE for name in realised_twice):
        raise SystemExit(f"constants in both dumps include articles or Mathlib nodes: {realised_twice[:5]}")
    for name in realised_twice:
        del atlas_rows[name]
    articles = manifest & atlas_rows.keys()
    # The duplicates as the v2 extraction counts them: one this dump cannot count stops the bridge before it writes, and
    # one the Lean no longer declares is warned about. Only the checkout's Lean sources can tell a deleted declaration
    # from an incomplete dump: an explicit manifest has none.
    sources = functools.cache(v2.lean_index)
    alias, problems, warnings = v2.resolve_aliases(
        listed, manifest, atlas_rows,
        (lambda name: name in sources().declarations) if args.articles is None else (lambda name: None), collisions)
    for warning in warnings:
        print(f"warning: {warning}", file=sys.stderr)
    if problems:
        raise SystemExit(f"{len(problems)} declarations listed as duplicates whose uses could not count as uses of "
                         "their articles: " + "; ".join(problems[:5]))
    for name in atlas_rows:
        rule_of[name] = NODE if name in articles else ATLAS_HIDDEN
    rows.update(atlas_rows)
    edges, groups, report = collapse(rows, mathlib_nodes | articles, sorted(articles), rule_of, alias)
    bridge = []
    for edge in edges:
        if edge["target"] in mathlib_nodes:
            bridge.append({**edge, "library": atlas_rows[edge["source"]]["module"].split(".", 1)[0]})
    write_jsonl_gz(out / "bridge-edges.jsonl.gz", bridge)
    meta = {
        "articles": len(articles),
        "articles_by_library": dict(sorted(collections.Counter(
            atlas_rows[name]["module"].split(".", 1)[0] for name in articles).items())),
        "manifest_without_v2_row": len(manifest - atlas_rows.keys()),
        "manifest_naming_mathlib": sorted(manifest & rule_of.keys() - atlas_rows.keys())[:50],
        "v2_constants": len(atlas_rows),
        "realised_in_both_dumps": realised_twice,
        "bridge_edges": len(bridge),
        "atlas_edges": sum(1 for edge in edges if edge["target"] in articles),
        "mutual_groups": groups,
        "seconds": round(time.time() - started, 1),
    }
    bridge_counts = {"statement": collections.Counter(), "proof": collections.Counter()}
    for edge in bridge:
        bridge_counts[edge["kind"]][edge["part"]] += 1
        bridge_counts[edge["kind"]]["direct" if edge["direct"] else "collapsed"] += 1
    meta["bridge_edges_by_kind"] = {kind: dict(sorted(c.items())) for kind, c in bridge_counts.items()}
    if args.check_v2:
        meta["v2_agreement"] = compare_with_v2(edges, articles, Path(args.check_v2))
    write_json(out / "bridge-meta.json", meta)
    print(f"{len(articles)} ATLAS articles, {len(bridge)} bridge edges to {len(mathlib_nodes)} Mathlib nodes -> {out}")
    agreement = meta.get("v2_agreement")
    if agreement and (agreement["articles_differing"] or agreement["missing_articles"]
                      or agreement["unexpected_articles"]):
        print(f"error: the bridge disagrees with {args.check_v2}: {agreement['missing_articles']} of its articles "
              f"missing (e.g. {agreement['missing_examples'][:3]}), {agreement['unexpected_articles']} not in it "
              f"(e.g. {agreement['unexpected_examples'][:3]}), {agreement['articles_differing']} with other ATLAS "
              f"edges (e.g. {agreement['examples'][:3]})", file=sys.stderr)
        return 1
    return 0


# ---------------------------------------------------------------------------------------------------- join


def read_json_object(path: Path, what: str) -> dict:
    if not path.is_file():
        raise SystemExit(f"{path}: no such {what}")
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise SystemExit(f"{path}: not JSON: {error}") from None
    if not isinstance(data, dict):
        raise SystemExit(f"{path}: the {what} is not a JSON object")
    return data


def mathlib_key(key: str) -> bool:
    """`Mathlib` (the root file) or a module or directory key below it, such as `Mathlib/Topology/Basic`."""
    return key == "Mathlib" or (key.startswith("Mathlib/") and all(key.split("/")))


def placement_entry(key: str, value, where: str) -> dict:
    """A Mathlib key's value: exactly `{to, title}`, `to` naming `Subject/field[/subfield]`, or exactly `{exclude}`."""
    if isinstance(value, dict) and set(value) == {"to", "title"} and all(
            isinstance(value[field], str) and value[field].strip() for field in ("to", "title")):
        parts = value["to"].split("/")
        if len(parts) in (2, 3) and all(parts):
            return {"to": value["to"], "title": value["title"]}
    if isinstance(value, dict) and set(value) == {"exclude"} and isinstance(value["exclude"], str) \
            and value["exclude"].strip():
        return {"exclude": value["exclude"]}
    raise SystemExit(f'{where}: {key}: expected {{"to": "Subject/field[/subfield]", "title": "..."}} '
                     f'or {{"exclude": "reason"}}, not {json.dumps(value, ensure_ascii=False)[:200]}')


def load_placements(paths: list[Path]) -> dict[str, dict]:
    """Mathlib keys from taxonomy-shaped files: `placements` ({to, title}, or {exclude} as the classification
    proposals write it) and `mathlib_exclusions` ({key: reason}). Keys of other libraries are left out; a malformed
    value, or a key placed twice differently, is an error."""
    merged: dict[str, dict] = {}
    origin: dict[str, str] = {}

    def add(key: str, entry: dict, where: str) -> None:
        if key in merged and merged[key] != entry:
            twice = "placed twice" if ("exclude" in entry) == ("exclude" in merged[key]) else "placed and excluded"
            raise SystemExit(f"{key} is {twice}: in {origin[key]} and in {where}")
        merged[key], origin[key] = entry, where

    for path in paths:
        data = read_json_object(path, "placement file")
        placements, exclusions = data.get("placements", {}), data.get("mathlib_exclusions", {})
        if not isinstance(placements, dict) or not isinstance(exclusions, dict):
            raise SystemExit(f"{path}: `placements` and `mathlib_exclusions` must be JSON objects")
        for key, value in placements.items():
            if key.startswith("Mathlib/") and not mathlib_key(key):
                raise SystemExit(f"{path} (placements): {key} is not a module or directory key")
            if mathlib_key(key):  # other keys place the ATLAS libraries' own modules
                add(key, placement_entry(key, value, f"{path} (placements)"), f"{path} (placements)")
        for key, reason in exclusions.items():
            if not mathlib_key(key):
                raise SystemExit(f"{path} (mathlib_exclusions): {key} is not a Mathlib module or directory key")
            where = f"{path} (mathlib_exclusions)"
            add(key, placement_entry(key, {"exclude": reason}, where), where)
    return merged


def resolve(key: str, placements: dict[str, dict]) -> tuple[str, dict] | None:
    """A module's own key, else its nearest placed directory, as generate_wiki.placement resolves ATLAS modules.
    The bare `Mathlib` key belongs to the root module `Mathlib.lean` alone: it is never a fallback."""
    if key == "Mathlib":
        return (key, placements[key]) if key in placements else None
    parts = key.split("/")
    for end in range(len(parts), 1, -1):
        candidate = "/".join(parts[:end])
        if candidate in placements:
            return candidate, placements[candidate]
    return None


def defined_scopes(data: dict, where: str) -> set[str]:
    """The fields and subfields of a taxonomy's subjects, and those a classification proposal adds in
    `new_fields` and `new_subfields`."""
    scopes = set()
    try:
        for subject, entry in data.get("subjects", {}).items():
            for field in entry.get("fields", []):
                scopes.add(f"{subject}/{field['slug']}")
                scopes.update(f"{subject}/{field['slug']}/{sub['slug']}" for sub in field.get("subfields", []))
        for added in data.get("new_fields", []):
            field = added["field"]
            scopes.add(f"{added['subject']}/{field['slug']}")
            scopes.update(f"{added['subject']}/{field['slug']}/{sub['slug']}" for sub in field.get("subfields", []))
        for added in data.get("new_subfields", []):
            scopes.add(f"{added['subject']}/{added['field']}/{added['subfield']['slug']}")
    except (AttributeError, KeyError, TypeError) as error:
        raise SystemExit(f"{where}: malformed `subjects`, `new_fields` or `new_subfields` ({error!r})") from None
    return scopes


def shown(path: Path) -> str:
    """A path as reports give it: relative to this checkout when inside it, so reports do not depend on where the
    checkout is."""
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def command_join(args: argparse.Namespace) -> int:
    out = Path(args.outdir)
    taxonomy = Path(args.taxonomy)
    sources = [Path(p) for p in args.placements] or [taxonomy]
    placements = load_placements(sources)
    scopes = defined_scopes(read_json_object(taxonomy, "taxonomy"), str(taxonomy))
    if not scopes:
        raise SystemExit(f"{taxonomy}: defines no fields, so placement targets cannot be checked")
    for source in sources:
        scopes |= defined_scopes(read_json_object(source, "placement file"), str(source))
    unknown: dict[str, list[str]] = collections.defaultdict(list)
    for key, entry in sorted(placements.items()):
        if "to" in entry and entry["to"] not in scopes:
            unknown[entry["to"]].append(key)
    nodes = list(read_jsonl(out / "nodes.jsonl.gz"))
    rows, used = [], collections.Counter()
    status = collections.Counter()
    modules: dict[str, str] = {}
    topics: set[tuple[str, str]] = set()
    for node in nodes:
        found = resolve(node["key"], placements)
        row = {"name": node["name"], "key": node["key"], "placement": None}
        if found is None:
            state = "unplaced"
        else:
            row["placement"], entry = found
            used[found[0]] += 1
            if "exclude" in entry:
                state, row["exclude"] = "excluded", entry["exclude"]
            else:
                state = "placed"
                row["to"], row["title"] = entry["to"], entry["title"]
                topics.add((entry["to"], entry["title"]))
        status[state] += 1
        modules[node["key"]] = state
        rows.append(row)
    write_jsonl_gz(out / "topics.jsonl.gz", rows)
    module_status = collections.Counter(modules.values())
    report = {
        "sources": [shown(source) for source in sources],
        "taxonomy": shown(taxonomy),
        "strict": args.strict,
        "placement_keys": len(placements),
        "nodes": dict(sorted(status.items())),
        "modules_with_nodes": dict(sorted(module_status.items())),
        "topics": len(topics),
        "unplaced_modules": sorted(key for key, state in modules.items() if state == "unplaced"),
        "keys_matching_no_node": sorted(key for key in placements if key not in used),
        "targets_not_in_taxonomy": dict(sorted(unknown.items())),
    }
    write_json(out / "join-report.json", report)
    print(f"{status['placed']} nodes placed in {len(topics)} topics, {status['excluded']} excluded, "
          f"{status['unplaced']} unplaced ({module_status['unplaced']} modules) -> {out / 'topics.jsonl.gz'}")
    if unknown:
        print(f"{'error' if args.strict else 'warning'}: {len(unknown)} placement targets name no field or subfield "
              f"of {taxonomy} or of the given proposals, e.g. {sorted(unknown)[:3]}", file=sys.stderr)
        if args.strict:
            return 1
    return 0


# --------------------------------------------------------------------------------------------------- stats


def weak_components(names: list[str], edges) -> list[int]:
    """Sizes of the weakly connected components, largest first (union-find)."""
    index = {name: i for i, name in enumerate(names)}
    parent = list(range(len(names)))

    def find(i: int) -> int:
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for source, target in edges:
        a, b = find(index[source]), find(index[target])
        if a != b:
            parent[a] = b
    return sorted(collections.Counter(find(i) for i in range(len(names))).values(), reverse=True)


def command_stats(args: argparse.Namespace) -> int:
    out = Path(args.outdir)
    nodes = {node["name"]: node for node in read_jsonl(out / "nodes.jsonl.gz")}
    graph_meta = json.loads((out / "graph-meta.json").read_text(encoding="utf-8"))
    by_kind = collections.Counter(node["kind"] for node in nodes.values())
    by_directory = collections.Counter("/".join(node["key"].split("/")[:2]) for node in nodes.values())
    edge_counts = collections.Counter()
    indegree = {"statement": collections.Counter(), "proof": collections.Counter()}
    pairs = []
    for edge in read_jsonl(out / "edges.jsonl.gz"):
        edge_counts[(edge["kind"], edge["part"], edge["direct"])] += 1
        indegree[edge["kind"]][edge["target"]] += 1
        pairs.append((edge["source"], edge["target"]))
    sizes = weak_components(sorted(nodes), pairs)
    del pairs
    total_in = indegree["statement"] + indegree["proof"]

    def top(counter: collections.Counter, n: int = 30) -> list[dict]:
        return [{"name": name, "kind": nodes[name]["kind"], "module": nodes[name]["module"], "uses": count,
                 "statement_uses": indegree["statement"][name], "proof_uses": indegree["proof"][name]}
                for name, count in sorted(counter.items(), key=lambda item: (-item[1], item[0]))[:n]]

    stats = {
        "nodes": {"total": len(nodes), "by_kind": dict(sorted(by_kind.items())),
                  "by_directory": dict(sorted(by_directory.items())),
                  "with_docstring": sum(1 for node in nodes.values() if node["has_doc"]),
                  "simp": sum(1 for node in nodes.values() if node["simp"]),
                  "with_additive_partner": sum(1 for node in nodes.values() if node["additive"]),
                  "with_multiplicative_partner": sum(1 for node in nodes.values() if node["multiplicative"])},
        "edges": {
            "total": sum(edge_counts.values()),
            "by_kind": {kind: sum(c for (k, _, _), c in edge_counts.items() if k == kind)
                        for kind in ("statement", "proof")},
            "statement_from_type": sum(c for (k, p, _), c in edge_counts.items() if k == "statement" and p == "type"),
            "statement_from_value_only": sum(c for (k, p, _), c in edge_counts.items()
                                             if k == "statement" and p == "value"),
            "direct": sum(c for (_, _, d), c in edge_counts.items() if d),
            "collapsed": sum(c for (_, _, d), c in edge_counts.items() if not d),
            "collapsed_through_rule": graph_meta["through"],
            "collapsed_only_through_rule": graph_meta["only_through"],
        },
        "rules": {"constants": graph_meta["constants"],
                  "removed": {rule["rule"]: rule["removed"] for rule in graph_meta["rules"]},
                  "nodes": graph_meta["nodes"]},
        "mutual_groups": graph_meta["mutual_groups"],
        "statement_cycles_after_mutual": len(graph_meta["statement_cycles_after_mutual"]),
        "cycles_statement_and_proof": len(graph_meta["cycles_statement_and_proof"]),
        "weak_components": {"count": len(sizes), "largest": sizes[0] if sizes else 0,
                            "isolated_nodes": sum(1 for size in sizes if size == 1),
                            "largest_ten": sizes[:10]},
        "most_used": top(total_in),
        "most_used_in_statements": top(indegree["statement"]),
        "seconds": {"graph": graph_meta["seconds"]},
    }
    # The v2 dump's meta first: its ATLAS commit is the layer's. The Mathlib dump depends only on the pins, and the
    # workflow may restore it from a cache made at another commit.
    for meta_file in sorted(out.glob("*dump-meta.json"), reverse=True):
        meta = json.loads(meta_file.read_text(encoding="utf-8"))
        stats.setdefault("versions", {key: meta.get(key) for key in ("lean_version", "mathlib_rev", "atlas_commit")})
        stats["seconds"][meta_file.name.removesuffix("-meta.json")] = meta["dump"]["seconds"]
    bridge_path = out / "bridge-edges.jsonl.gz"
    if bridge_path.is_file():
        bridge_meta = json.loads((out / "bridge-meta.json").read_text(encoding="utf-8"))
        sources_by_library: dict[str, set[str]] = collections.defaultdict(set)
        bridge_in = collections.Counter()
        bridge_kinds = collections.Counter()
        for edge in read_jsonl(bridge_path):
            sources_by_library[edge["library"]].add(edge["source"])
            bridge_in[edge["target"]] += 1
            bridge_kinds[edge["kind"]] += 1
        stats["bridge"] = {
            "edges": sum(bridge_kinds.values()),
            "by_kind": dict(sorted(bridge_kinds.items())),
            "articles": bridge_meta["articles"],
            "articles_by_library": bridge_meta["articles_by_library"],
            "articles_with_bridge_edge": sum(len(s) for s in sources_by_library.values()),
            "articles_with_bridge_edge_by_library": {lib: len(s) for lib, s in sorted(sources_by_library.items())},
            "mathlib_nodes_used": len(bridge_in),
            "most_used_by_atlas": [{"name": name, "kind": nodes[name]["kind"], "uses": count}
                                   for name, count in sorted(bridge_in.items(), key=lambda i: (-i[1], i[0]))[:30]],
            "v2_agreement": bridge_meta.get("v2_agreement"),
        }
        stats["seconds"]["bridge"] = bridge_meta["seconds"]
    join_path = out / "join-report.json"
    if join_path.is_file():
        join = json.loads(join_path.read_text(encoding="utf-8"))
        stats["join"] = {key: join[key] for key in ("nodes", "modules_with_nodes", "topics", "placement_keys")}
    write_json(out / "stats.json", stats)
    print(f"stats -> {out / 'stats.json'}")
    return 0


# --------------------------------------------------------------------------------------------------- main


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)

    dump = commands.add_parser("dump", help="run the Lean dump in shards")
    dump.add_argument("output", help="merged rows, gzipped JSON lines")
    dump.add_argument("--modules", help="file naming the modules to dump (default: every Mathlib module)")
    dump.add_argument("--keep", default="Mathlib", help="module roots whose constants the uses keep")
    dump.add_argument("--shards", type=int, default=0,
                      help="processes, each importing every listed module (default: twice --jobs)")
    dump.add_argument("--jobs", type=int, default=0,
                      help="shards run at once, each needing about 9 GB, mostly shared .olean pages "
                           "(default: the CPUs, at most 16)")
    dump.add_argument("--lean-root", default=str(ROOT),
                      help="the built Lake project to run this checkout's dump script in (default: this checkout)")
    dump.set_defaults(run=command_dump)

    graph = commands.add_parser("graph", help="nodes and edges of the Mathlib layer")
    graph.add_argument("dump", help="the merged Mathlib dump")
    graph.add_argument("outdir")
    graph.set_defaults(run=command_graph)

    bridge = commands.add_parser("bridge", help="edges from ATLAS's articles to Mathlib nodes")
    bridge.add_argument("v2_dump", help="the dump of the v2 modules, with --keep " + V2_KEEP)
    bridge.add_argument("outdir")
    bridge.add_argument("--mathlib-dump", required=True, help="the merged Mathlib dump")
    bridge.add_argument("--articles", help="file of article Lean names (default: read by Autoform from blueprint/)")
    bridge.add_argument("--aliases", help="with --articles, file of duplicates and their articles, one "
                                          "`name<TAB>article` a line (default: none; without --articles, read by "
                                          "Autoform from blueprint/)")
    bridge.add_argument("--check-v2", help="extract_v2_lean_dependencies.py output to compare ATLAS edges with")
    bridge.set_defaults(run=command_bridge)

    join = commands.add_parser("join", help="give each node its module's topic")
    join.add_argument("outdir")
    join.add_argument("placements", nargs="*", help="taxonomy-shaped files (default: scripts/taxonomy.json)")
    join.add_argument("--taxonomy", default=str(TAXONOMY),
                      help="taxonomy whose fields and subfields the placement targets must name")
    join.add_argument("--strict", action="store_true",
                      help="fail when a placement target names no field or subfield (unplaced nodes are allowed)")
    join.set_defaults(run=command_join)

    stats = commands.add_parser("stats", help="summarise the outputs in stats.json")
    stats.add_argument("outdir", help="the graph's directory; its *dump-meta.json files give versions and run times")
    stats.set_defaults(run=command_stats)

    args = parser.parse_args(argv)
    return args.run(args)


if __name__ == "__main__":
    sys.exit(main())
