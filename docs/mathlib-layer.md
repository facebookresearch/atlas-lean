# The Mathlib layer of the dependency graph

The dependency explorer's graph also covers Mathlib at the pinned revision: one
node per Mathlib declaration a mathematician could cite, statement and proof
edges between them computed from compiled Lean, bridge edges from ATLAS's
articles to the Mathlib nodes they use, and each node's topic in
`scripts/taxonomy.json`. `scripts/dump_mathlib_dependencies.lean` reads the
compiled constants and `scripts/extract_mathlib_graph.py` builds the files
below. The workflow's `build the Mathlib layer` job uploads them as the
`mathlib-graph` artifact, with this page as `SCHEMA.md`, except the two dumps:
the v2 one is that job's `v2-mathlib-dump` artifact and the Mathlib one
depends only on the pinned Mathlib. Like the v2 dependency dump, they are build outputs and are
never committed. `docs/BLUEPRINT.md` gives the commands, and
`docs/mathlib-pages.md` describes the pages built from the layer.

## Nodes

Every constant declared in a Mathlib module gets a dump row. A constant is a
node unless the first of these rules that applies removes it; `graph-meta.json`
counts what each rule removes, with examples.

| Rule | Removes |
|---|---|
| `excluded_module` | constants of `Mathlib/Tactic`, `Mathlib/Lean`, `Mathlib/Util`, `Mathlib/Testing`, `Mathlib/Deprecated`, `Mathlib/Init.lean` and `Mathlib/Tactic.lean` |
| `private` | private names, including a `module` file's non-public declarations |
| `lean:internal` | names with a part that starts with `_` or is a number, and `eq_1`, `match_1`, `proof_1`, `omega_1` parts (`Name.isInternalDetail`) |
| `lean:recursor` | recursors (`T.rec`) |
| `lean:aux_recursor` | `casesOn`, `recOn`, `brecOn`, `below` and sparse `casesOn` |
| `lean:no_confusion` | `noConfusion` and `noConfusionType` |
| `lean:matcher` | matchers |
| `lean:reserved` | reserved names Lean realises on demand: `eq_def`, `induct`, `fun_cases`, `congr_simp`, ... |
| `constructor` | constructors: their types are part of their inductive type's statement |
| `generated` | constants with no declaration range, which commands and attributes generate (`ctorIdx`, `mk.injEq`, `mk.inj`, `sizeOf_spec`, `ctorElimType`) |
| `deprecated` | `@[deprecated]` declarations |
| `metaprogramming` | `meta` or `unsafe` constants (syntax, delaborators, tactic extensions); names under `Mathlib`, `Lean`, `Qq`, `Aesop`, `ProofWidgets` or `Plausible` (`Mathlib.Meta.NormNum.*`); types that use Lean's expressions, syntax, names, levels or elaboration monads, `Qq` or `ProofWidgets`; instances of a class under `Lean` (`Lean.Grind.CommRing`, `Lean.ToExpr`) or of `Repr`, `ToString`, `Std.ToFormat` or `Hashable` |
| `data_field` | the projection of a structure's own field that is not a proposition (`Norm.norm`, `Subgroup.carrier`): uses of it reach the structure through its type |

What remains are theorems, definitions, abbreviations (reducible definitions),
structures, classes, inductive types, instances, the fields of structures and
classes that state axioms (`Semigroup.mul_assoc`), and parent projections
(`Ring.toSemiring`, an instance, and `RingHom.toMonoidHom`, a definition).
Instances and parent projections are nodes so that edges stop at them: the
body of an instance of a class of data, or of a parent projection that rebuilds
its parent from fields, holds proofs of axioms, and reaching through it would
make every statement that uses it depend on those proofs.

## Edges

Edges follow `scripts/extract_v2_lean_dependencies.py`, which tells constants
apart by the kind Lean compiles them to. A node's statement edges come from its
type, and also from its value when that value is part of what it states: the
body of a definition, an abbreviation or an instance of a class of data (all
compiled as definitions), and an inductive type's constructors. Such nodes get
no proof edges. A theorem's proof, including that of an instance of a
proposition (`Fact (Nat.Prime 2)`, `IsScalarTower R S M`), which Lean compiles
as a theorem, and an `opaque` body give proof edges, minus the statement ones. A use that is not a node reaches the
nodes behind it: through what a hidden constant states (its type, and its body
if it is a definition) for statement edges, through everything it uses for
proof edges. Statement edges inside a group of nodes that reach each other
(mutual inductive types or definitions) are left out and the group is listed;
the statement graph is then acyclic, and `graph-meta.json` records the check.
Uses of constants outside Mathlib (Lean core, Batteries) are not recorded:
those libraries cannot reach Mathlib.

Bridge edges apply the same rules to ATLAS's articles (the Lean names that
`blueprint/links` annotations link, as Autoform reads them) over the v2 and
Mathlib constants together, and keep the edges whose target is a Mathlib node.
A declaration a row lists as a duplicate of its page's counts as that page's
article, as in the v2 extraction: another article's use of it is a direct use
of the article, and to the article itself it is part of the article, whose
edges reach what the duplicate uses: as directly as the duplicate does where
the article names it, and otherwise as through a hidden constant.
The bridge refuses a duplicate, or warns about one, as the extraction does;
with `--articles`, which comes with no Lean sources to tell a deleted
declaration from an incomplete dump, it refuses a duplicate its dump lacks.
Uses of CSLib, Physlib and other libraries are not followed. With `--check-v2`,
as the workflow runs it, the same computation must give exactly the articles
and ATLAS-to-ATLAS edges of `build/lean-dependencies.json`: an article only one
side has, or different edges, fails the run.

## Topics

`join` resolves each node's module key (`Mathlib/Topology/Basic`) in the
`placements` of `scripts/taxonomy.json` (or of the files it is given): the
module's own key, else its nearest placed directory, as `generate_wiki.py`
places ATLAS's modules. A key's value is exactly `{"to":
"Subject/field[/subfield]", "title": "..."}`, or `{"exclude": "reason"}` as the
classification proposals write it; a top-level `mathlib_exclusions` map (`{key:
reason}`) excludes too, and its keys must be Mathlib keys. Keys of the ATLAS
libraries are left alone. The bare key `Mathlib` belongs to the root file
`Mathlib.lean` only and is never a fallback. A malformed value, or a key placed
twice differently or both placed and excluded, is an error. A node without a
placement is unplaced, never excluded; exclusions annotate nodes and remove
neither nodes nor edges.

Placement targets are checked against the fields and subfields of `--taxonomy`
(default `scripts/taxonomy.json`, which must exist and define fields) and those
that the given classification proposals add in `new_fields` and
`new_subfields`. `join-report.json` lists every target that matches neither,
with the keys that use it; with `--strict`, as the workflow runs it, such a
target fails the run. Unplaced nodes are reported and never fail it, so the
layer builds before Mathlib's placements exist.

## Files

All JSON lines files are gzipped and sorted. Their uncompressed content is
deterministic: identical inputs give identical JSON lines. The gzip bytes are
identical too when the same zlib version compresses them (the gzip header
holds no time stamp); another zlib can compress the same content differently.

`mathlib-dump.jsonl.gz`: one row per constant declared in a Mathlib module.

| Field | Meaning |
|---|---|
| `name`, `module` | the constant and its module (`Mathlib.Topology.Basic`) |
| `kind` | `theorem`, `def`, `axiom`, `opaque`, `inductive`, `constructor`, `recursor` or `quot` |
| `private`, `unsafe`, `meta` | the name is private; the constant is unsafe; it was declared `meta` |
| `aux` | Lean's reason to treat it as generated (`internal`, `recursor`, `aux_recursor`, `no_confusion`, `matcher`, `reserved`), or null |
| `instance`, `class`, `structure` | instance attribute; class; structure |
| `projection` | for a structure projection: `structure`, `field`, `subobject` (a parent's field) and `from_class` |
| `parent_projection` | for the projection to a parent named in the structure's `extends` (a subobject field, or the generated `toB` of a parent that shares fields with another), the structure; else null |
| `deprecated` | `{new, since}` for a deprecated constant, else null |
| `reducibility` | `reducible`, `semireducible`, `irreducible`, `instance_reducible` or `implicit_reducible` |
| `prop` | whether its type is a proposition (computed for possible nodes and projections; null otherwise or on failure) |
| `head` | the constant at the head of its type's conclusion (an instance's class) |
| `ctors`, `mutual` | an inductive type's constructors; the other constants of its mutual block |
| `doc`, `line`, `name_line` | docstring; first line of the declaration (its docstring included) and of its name, from the declaration range |
| `to_additive`, `to_dual` | the `to_additive` and `to_dual` translations of the name |
| `simp` | whether it is a `simp` lemma |
| `type_meta` | constants of Lean's metaprogramming namespaces that its type uses |
| `signature` | the pretty-printed signature, for possible nodes (not private, generated, deprecated, a constructor or a recursor) |
| `type`, `value` | the Mathlib constants its type and its value use (an inductive type's value: its constructors' types) |

`v2-mathlib-dump.jsonl.gz` has the same rows for the constants of the v2
modules, keeping uses of v2 and Mathlib constants. Each dump has a
`*-meta.json` with the Lean version, the package revisions, the ATLAS commit,
the module and row counts, and the run times.

`nodes.jsonl.gz`: one row per node.

| Field | Meaning |
|---|---|
| `name`, `module`, `key` | the declaration, its module, and the module's taxonomy key |
| `kind` | `theorem`, `definition`, `abbreviation`, `structure`, `class`, `inductive`, `instance`, `field`, `opaque` or `axiom` |
| `lean_kind` | the dump's `kind` |
| `line`, `name_line` | as in the dump |
| `doc`, `has_doc` | the docstring, and whether there is one |
| `signature` | the pretty-printed signature |
| `proposition` | whether it states a proposition |
| `simp` | whether it is a `simp` lemma |
| `additive`, `multiplicative`, `dual` | `to_additive` partners in each direction, and the `to_dual` partner |
| `instance_of` | an instance's class |
| `projection_of`, `parent_projection` | for a field or a parent projection, the structure it belongs to; `true` for a parent projection: the dump's `parent_projection`, or any subobject field (an embedded parent, an indirect parent's included) |

`edges.jsonl.gz`: one row per edge, `{source, target, kind, part, direct,
through}`. `kind` is `statement` or `proof`; `part` is `type` for a statement
edge its type gives, `value` for one only its value gives and for every proof
edge; `direct` says whether the source uses the target itself; for an edge that
only passes through hidden constants, `through` lists the rules of the first
hidden constants on its way (`private`, `lean:internal`, `excluded_module`,
`data_field`, ...).

`bridge-edges.jsonl.gz`: the same fields for edges from ATLAS articles to
Mathlib nodes, with `library` (`MathlibExt`, `CSLibExt`, `PhyslibExt`, `Domains` or
`WantedExt`); `through` may name `atlas_non_article`, an ATLAS constant no article
links.

`topics.jsonl.gz`: one row per node, `{name, key, placement}` with `to` and
`title` when placed or `exclude` when excluded; `placement` is the matching key,
null when unplaced.

`graph-meta.json`, `bridge-meta.json`, `join-report.json`: rule counts and
examples, mutual groups and cycle checks, edge counts by how they are produced,
the bridge's agreement with the v2 extraction; the join's inputs, its node and
module counts by placed, excluded and unplaced, the unplaced modules, the
placement keys that match no node, and the targets that name no field
(`targets_not_in_taxonomy`). `stats.json` summarises them: nodes by kind and Mathlib
directory, edges by kind, weak components, the most used nodes, ATLAS articles
with a bridge edge, topics, versions and run times.
