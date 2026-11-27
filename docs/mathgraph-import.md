# Importing mathgraph

`scripts/import_mathgraph.py` adds pages and their annotations to the wiki from
Jack McCarthy's mathgraph, a graph of textbook results with statements, proof
sketches, sources and prerequisites. This release imports two kinds of page:
planned pages, which state a result and record their own prerequisites
([Writing pages](BLUEPRINT.md#writing-pages)), and pages credited to one Mathlib
declaration, in the format of
[Mathlib-credited pages](BLUEPRINT.md#mathlib-credited-pages). Records that a
result is already an existing page are left to a later release.

Besides the repository, the importer reads one file, a reviewed manifest, in
which each row authorises one page. It never reads mathgraph itself, matcher
outputs, review candidates or any other private record: the manifest is built
from them elsewhere, and reviewed, before it is applied. A PR made with the
importer is a graph PR ([CONTRIBUTING.md](../CONTRIBUTING.md#graph-prs)),
reviewed against the [graph rules](BLUEPRINT.md#graph-rules).

## Running it

Use the Python environment of
[BLUEPRINT.md](BLUEPRINT.md#local-environment-and-tests), on a clean worktree of
the PR's base. Run it on a case-sensitive filesystem, as on Linux: elsewhere a
`page_dir` that differs from an existing folder only in case would name that
folder, which the importer checks for the subject folder alone. The importer
imports `jsonschema`, which Autoform's dependencies install and the workflow
pins.

```sh
python scripts/import_mathgraph.py --check --manifest manifest.jsonl \
  --manifest-sha256 <SHA-256 the review approved>
python scripts/import_mathgraph.py --apply --manifest manifest.jsonl \
  --manifest-sha256 <SHA-256 the review approved>
python scripts/import_mathgraph.py --identity blueprint/roadmap/<page>.md
python scripts/import_mathgraph.py --check-map [--base <commit>]
python -m unittest scripts.test_import_mathgraph
```

`--check` runs the checks and, when they all pass, prints the change: each
folder and file to create and each line to add, with the rule that puts it
there. It writes nothing. `--apply` runs the same checks and writes the same
change. Applying a manifest twice is refused, as its ids and map rows exist
after the first time. `--identity` prints, as JSON, what a dependency on an
existing page is bound to (`path`, `statement_sha256`, `annotation_sha256`; see
below), with the importer's own definitions, so that a manifest is built with
them; it refuses a page that can be no dependency, or that no manifest can name,
as it does not match the schema's `page` pattern, and writes nothing.
`--check-map` checks the map and, with `--base`, that it only grows and that
each new line records a page the change adds ([The map](#the-map)); it writes
nothing. Here and below, "writes nothing" means nothing in the worktree: the
checks try their edits of folder pages on copies in a temporary folder.

What a run guarantees:

- **A failed check writes nothing.** The checks run in stages, and the whole
  change is staged in memory, before anything is written. A stage that finds a
  problem stops the run, which names every problem found so far and exits 1, so
  a later stage's problems show once those are fixed.
- **An exception while writing is rolled back.** `--apply` writes nothing unless
  nothing is at any path it creates and every file it edits still holds the
  bytes the checks read. It writes each file in its folder, opened one component
  at a time from the repository root without following a link, and checks the
  path again there just before writing it. Each file's staged bytes go to a
  temporary file beside it: an edited file's moves into place with `os.replace`,
  so the file holds its old bytes or its new ones, never part of them, and keeps
  its mode; a new file's is linked into place with `os.link`, and a new folder
  is made with `mkdir`, both of which fail if anything is at the path, so a new
  file or folder never replaces an entry. If an exception or an interruption it
  can catch stops the writing, it undoes the steps it took, last first: it gives
  each file it edited its old bytes back and removes each file and folder it
  created, the temporary files beside them included. It undoes a step only in
  the folder the step was taken in, reached the same way, and only on the file
  or folder the run made, as their device and inode show; a path where it finds
  anything else is left as it is. A folder that appears in the instant between
  the importer's `mkdir` and its record is treated as the importer's, under the
  exclusive-worktree assumption below, and removed only if it is empty and its
  parent is the verified one, which the importer then names; otherwise it is
  reported. It exits 1, saying either that every change was undone, the tree
  being as it was before the run, or which files and folders it could not
  restore.
- **Where symbolic links are refused.** Symbolic links are refused on every
  repository path the importer writes or removes, and on the files whose content
  it reads, each checked on the path it is then opened by: the manifest when it
  lies in the repository, the links files, `scripts/taxonomy.json`, the card
  move ledger, the map, the folder pages it edits or whose part copies it
  refreshes, the pages a dependency names and the pages the cycle check reads.
  Such a path is refused when it, or a folder between it and the repository
  root, is a link, a dangling link counting as there. A manifest that is itself
  a symbolic link is refused: the manifest is named by one path, the one given
  made absolute without resolving links, which is checked and then opened
  without following a link. The folders above a manifest outside the repository
  are not checked, as its SHA-256 must equal the reviewed digest, which is what
  binds its content. Folder listings, used to place pages and check names, and
  any other file that `sync_wiki.py`, `generate_wiki.py` and Autoform read, such
  as `mkdocs.yml` and `lake-manifest.json`, are read as those tools read them.
- **The worktree is the importer's alone.** The importer assumes an exclusive
  worktree that nothing else changes while it runs. It detects some concurrent
  changes and then refuses or reports an incomplete rollback, but it does not
  promise immunity to concurrent mutation.
- **A crash or a power loss is not covered.** If the process is killed, the
  machine stops or a second interruption stops the rollback, the tree may hold
  part of the change: new files and folders, temporary files, edited files with
  their new bytes. Run on a clean worktree, so that
  `git checkout -- . && git clean -fd` restores it.

## The manifest

The manifest is a JSON Lines file: one object per line, no blank line. Each row
is a page, of `kind` `planned` or `mathlib`: `key` is the mathgraph key of its
result, `seed` names that result (its mathgraph id and the revision the manifest
was built at), `statement`, `sketch` and `sources` are what the page says, and
`page_dir` and `stem` are where it goes. Paths are relative to the repository
and lie under `blueprint/roadmap/`. A page's text may be adapted from
mathgraph's, with the small edits a review asks for.

- `depends` lists the page's own prerequisites, each with its kind, `statement`
  or `proof`. A target is either the key of another row of the manifest, or an
  existing page bound to the identity it was reviewed against, which
  `--identity` prints:
  - `target_statement_sha256`, the SHA-256 of its statement as Autoform reads
    it: its body before the first `##` section, without its title
    (`autoform_cli.markdown.article_parts`);
  - `target_annotation_sha256`, the SHA-256 of its annotation row, parsed from
    its links file as the sync reads the rows, the links folder's defaults not
    merged in, and serialised as canonical JSON:
    `json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False)`,
    in UTF-8. The row as a whole is bound, not only its `id`, so that a change
    to any of its facts is caught.
- `pending` lists the prerequisites not yet linked by the import, each with its
  key, kind and public reason: `not-imported`, `under-review`,
  `source-unverified` or `covered-by-generalization`. A pending entry does not
  imply that no page states the prerequisite, only that this import does not
  link one. A row may not list as pending its own key, a key twice, the key of
  another row of the manifest, or a key the map holds. A result the map holds
  was imported already: a row that needs it names its page under `depends`, at
  its current path, by the identity its review confirmed (`--identity`); the
  map's `page` is where the result was imported, which the page may have left
  since. The importer never makes that link on its own; the manifest's builder
  leaves out (holds) a row whose endpoint's identity or statement cannot be
  confirmed. `not_ready` is true exactly when `pending` is not empty, and
  `prose_missing` is given exactly then: the text of the page's `## Expansion`.
- `mathlib`, on a `mathlib` row only, is `{declaration, module}`: the one
  Mathlib declaration the page states, and its module. The declaration is a name
  with no whitespace, and the module lies under `Mathlib.`: narrower than the
  format, on purpose, so that a Lean name quoted with «» that holds a space, a
  row with no module and a module outside Mathlib are refused. Such a row has no
  sketch, no `depends`, no `pending` and no `prose_missing`, and `not_ready` is
  false: its page states what the declaration states and has no dependency
  section, as the build derives its edges
  ([Mathlib-credited pages](BLUEPRINT.md#mathlib-credited-pages)). A planned row
  may depend on a `mathlib` row's page, as on any other row's.
- `statement_sha256` and `sketch_sha256` are the SHA-256s of the page's own
  `statement` and `sketch` (of the empty string when `sketch` is null), which
  the importer checks against the text.
- `mg_statement_sha256`, `mg_sketch_sha256`, `reference_sha256` and
  `edges_sha256` record the result as mathgraph has it at `seed.revision`, for
  the map: the SHA-256s of its original statement and sketch (of the empty
  string when it has no sketch), of its `reference` string as written (of the
  empty string when it has none), and of its outgoing edges as the compact
  JSON array of `[kind, target key]` pairs, sorted, with `,` and `:` as
  separators and no space (`[]` when it has none). The importer copies them to
  the map, checking only that each is 64 hexadecimal digits: it has no access
  to mathgraph.

Every row must match this JSON Schema, `MANIFEST_SCHEMA` in the importer; a test
keeps the two equal. Each `pattern` is a full-string match, which the importer
enforces: a JSON Schema validator searches for a pattern, and `$` also matches
before a final line break, so the importer matches every pattern of the schema
against the whole string (`re.fullmatch`), and refuses a key, an id, a revision,
a digest, a path or a line that ends in a line break:

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "A row of a mathgraph import manifest",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "key", "kind", "mg_kind", "title", "statement", "sketch", "sources", "page_dir", "stem", "seed",
    "depends", "pending", "not_ready", "prose_missing", "statement_sha256", "sketch_sha256",
    "mg_statement_sha256", "mg_sketch_sha256", "reference_sha256", "edges_sha256"
  ],
  "properties": {
    "key": {"$ref": "#/$defs/key"},
    "kind": {"enum": ["planned", "mathlib"]},
    "mg_kind": {"enum": ["theorem", "definition"]},
    "title": {"$ref": "#/$defs/line"},
    "statement": {"$ref": "#/$defs/text"},
    "sketch": {"anyOf": [{"$ref": "#/$defs/text"}, {"type": "null"}]},
    "sources": {
      "type": "array",
      "minItems": 1,
      "uniqueItems": true,
      "items": {"$ref": "#/$defs/line"}
    },
    "page_dir": {
      "type": "string",
      "pattern": "^blueprint/roadmap/[A-Z][A-Za-z]*(?:/[a-z0-9]+(?:-[a-z0-9]+)*)+$"
    },
    "stem": {"$ref": "#/$defs/key"},
    "seed": {
      "type": "object",
      "additionalProperties": false,
      "required": ["source", "node", "revision"],
      "properties": {
        "source": {"const": "mathgraph"},
        "node": {"type": "string", "pattern": "^mg_[0-9a-f]{24}$"},
        "revision": {"type": "string", "pattern": "^[0-9a-f]{40}$"}
      }
    },
    "depends": {"type": "array", "items": {"$ref": "#/$defs/dependency"}},
    "pending": {
      "type": "array",
      "items": {
        "type": "object",
        "additionalProperties": false,
        "required": ["key", "kind", "reason"],
        "properties": {
          "key": {"$ref": "#/$defs/key"},
          "kind": {"enum": ["statement", "proof"]},
          "reason": {
            "enum": [
              "not-imported", "under-review", "source-unverified", "covered-by-generalization"
            ]
          }
        }
      }
    },
    "not_ready": {"type": "boolean"},
    "prose_missing": {"anyOf": [{"$ref": "#/$defs/text"}, {"type": "null"}]},
    "statement_sha256": {"$ref": "#/$defs/sha256"},
    "sketch_sha256": {"$ref": "#/$defs/sha256"},
    "mg_statement_sha256": {"$ref": "#/$defs/sha256"},
    "mg_sketch_sha256": {"$ref": "#/$defs/sha256"},
    "reference_sha256": {"$ref": "#/$defs/sha256"},
    "edges_sha256": {"$ref": "#/$defs/sha256"},
    "mathlib": {
      "type": "object",
      "additionalProperties": false,
      "required": ["declaration", "module"],
      "properties": {
        "declaration": {"$ref": "#/$defs/declaration"},
        "module": {"$ref": "#/$defs/module"}
      }
    }
  },
  "if": {"required": ["kind"], "properties": {"kind": {"const": "mathlib"}}},
  "then": {
    "required": ["mathlib"],
    "properties": {
      "sketch": {"type": "null"},
      "depends": {"maxItems": 0},
      "pending": {"maxItems": 0},
      "not_ready": {"const": false},
      "prose_missing": {"type": "null"}
    }
  },
  "else": {"properties": {"mathlib": {"not": {}}}},
  "$defs": {
    "key": {"type": "string", "pattern": "^[a-z0-9]+(?:-[a-z0-9]+)*$", "maxLength": 96},
    "declaration": {"type": "string", "pattern": "^\\S+$"},
    "module": {"type": "string", "pattern": "^Mathlib(?:\\.[A-Za-z0-9_']+)+$"},
    "line": {"type": "string", "pattern": "^\\S(?:[^\\n\\r]*\\S)?$"},
    "text": {"type": "string", "pattern": "^\\S(?:[^\\r]*\\S)?$"},
    "sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
    "page": {
      "type": "string",
      "pattern": "^blueprint/roadmap/[A-Z][A-Za-z]*(?:/[a-z0-9]+(?:-[a-z0-9]+)*)*/(?:[a-z0-9]+(?:-[a-z0-9]+)*|README)\\.md$"
    },
    "dependency": {
      "type": "object",
      "additionalProperties": false,
      "required": ["target", "kind"],
      "properties": {
        "target": {"anyOf": [{"$ref": "#/$defs/key"}, {"$ref": "#/$defs/page"}]},
        "kind": {"enum": ["statement", "proof"]},
        "target_statement_sha256": {"$ref": "#/$defs/sha256"},
        "target_annotation_sha256": {"$ref": "#/$defs/sha256"}
      },
      "if": {"required": ["target"], "properties": {"target": {"$ref": "#/$defs/page"}}},
      "then": {"required": ["target_statement_sha256", "target_annotation_sha256"]},
      "else": {
        "properties": {
          "target_statement_sha256": {"not": {}},
          "target_annotation_sha256": {"not": {}}
        }
      }
    }
  }
}
```

Beyond the schema, the importer checks that:

- the file is there, is not empty and has the SHA-256 given; no key appears
  twice, and no two rows have one seed;
- `seed.node` is mathgraph's id of the result `key`: `mg_` and the first 24 hex
  digits of the SHA-256 of `result:<key>`;
- `statement_sha256` and `sketch_sha256` are those of the texts; `not_ready`
  and `prose_missing` match `pending`; a definition (`mg_kind` `definition`) has
  no sketch and no proof prerequisite;
- each `depends` target is a row of the manifest that passes its own checks,
  or an existing statement page whose statement and annotation row have the
  digests `target_statement_sha256` and `target_annotation_sha256`, which has
  one annotation row, and which is not held back, and so unlinked
  ([Maintaining articles](BLUEPRINT.md#maintaining-articles)); a folder page,
  a page with no annotation or more than one, a target named twice and the row
  itself are refused;
- a `pending` key is not the row's own and is listed once, which the map checks
  of its lines too ([The map](#the-map)); it is no row of the manifest, in
  either order, which would be an active endpoint and so belongs in `depends`;
  and it is no key the map holds, which was imported already and so belongs in
  `depends` too, on its page, by its reviewed identity. The map holds a line to
  this last rule against earlier lines only: a line keeps the `pending` list its
  row had when one of those prerequisites is imported later;
- the map holds no row's key;
- for `mathlib` rows, as `sync_wiki.py` reads credit: no two name one
  declaration, and no page credits it already, to Mathlib or as a declaration of
  this project (`page_owner`), a row an earlier sync wrote with a module and a
  name only being resolved by the build, which has the Lean index, not here, and
  a Mathlib link on a row without the `mathlib` flag being a reference, which
  credits nothing; the links folder's credits are not ambiguous, which
  `sync_wiki.py mathlib-names` refuses too; `lake-manifest.json` pins a Mathlib
  commit; and the links folder as the change would leave it passes
  `sync_wiki.py`'s credit check (`credit_problems`), each new page's row
  crediting what its manifest row says. The importer does not check that the
  declaration is Mathlib's at that revision, that the module is its, or that it
  is no declaration of this project that has no page: the manifest's review
  checks these against the pinned source. After the import, the wiki job's
  registry steps (`sync_wiki.py mathlib-names`, then `lean-facts --registry` on
  a clean checkout) check them as they check every credited row: a module that
  is not the declaration's, for a declaration the build finds, stops
  `lean-facts` and fails the job, until the row names the right one; a
  declaration the build does not find, or finds to be this project's, only
  unlinks the page, with a warning
  ([Mathlib-credited pages](BLUEPRINT.md#mathlib-credited-pages));
- no string holds a reference the Public references check reports
  ([CONTRIBUTING.md](../CONTRIBUTING.md#public-references)), read as file
  contents and, for keys, stems, folders and targets, also as file names; no
  line of text is a Markdown heading, and no line of a statement, sketch or
  `prose_missing` makes a setext heading or a thematic break, any of which would
  end its section, and no source makes a thematic break in the page's list of
  sources; a title does not end in a backslash, which would escape the bracket
  that closes every link to its page; Autoform reads each planned page's
  statement and sections as the importer writes them; and text links, shows and
  defines only `https://` addresses: every link and image of a text field as the
  site renders it alone (`autoform_cli.markdown.render_html`), and every
  reference definition (`autoform_cli.markdown.link_definitions`), which on the
  page would serve its other sections too, as the importer writes every link to
  a page itself;
- every link the importer writes, on a folder page or under `## Depends on` and
  `## Proof depends on`, is one link to its target as Autoform reads it
  (`autoform_cli.markdown.link_targets`); otherwise the run is refused, naming
  the row or folder it links, or the row whose page holds it;
- every page and folder page written passes Autoform's check of what the site
  may publish, which would otherwise show it as typed text.

## Pages

A planned page:

```markdown
# <title>

<statement>

## Proof sketch

<sketch>

## Expansion

<prose_missing>

## Depends on

- [<title of a statement prerequisite>](<relative path>)

## Proof depends on

- [<title of a proof prerequisite>](<relative path>)

## Sources

- <source>
```

Each section is written only with something to hold: `## Proof sketch` only
with a sketch, `## Expansion` only when a prerequisite is pending, and
`## Depends on` and `## Proof depends on` only with a link to list, so that no
section claims a page has no prerequisite. A definition has no proof sections.
`## Expansion` holds `prose_missing`, written to say what a good expansion of
the node contains, as a page still to expand does ([Nodes still to
expand](BLUEPRINT.md#nodes-still-to-expand)); being a section of its own, it
stays out of the statement, and so out of the theorem box. A link is titled as
its target: its row's title, or the heading of its page, else its file name. No
page gets `## Informally uses`.

## Placing pages

A page goes in a folder by these rules, in order, applied to its `page_dir`
against `scripts/taxonomy.json` as the worktree has it:

1. An existing folder: the page goes there.
2. A field or subfield of the taxonomy: the page goes in its folder, made if
   the wiki lacks it.
3. The folder of a topic that a placement defines, `<to>/<slugify(title)>` with
   `generate_wiki.slugify`: if a part of the `<to>` folder holds that folder,
   the page goes there; if the `<to>` folder, or one of its parts, holds a page
   at that path (a topic written as one page), the page goes beside it.
   Otherwise `<to>` must be a field or subfield of the taxonomy, or the row is
   refused; then, if the manifest puts no other page in the topic, the page goes
   in the `<to>` folder, as `generate_wiki` writes a topic of one page, and
   otherwise the topic folder is made.
4. Anything else is refused: no topic folder is made that no placement
   defines.

A page is never placed in a card or in a folder below one
([Cards](BLUEPRINT.md#cards)): the importer refuses such a row, where the sync
would put the page beside the card for an editor to place.

A folder the importer makes gets a folder page as `generate_wiki` writes one:
its title, the description of a field or subfield, and the list of its pages and
folders, in `generate_wiki.subject_tree`'s order whatever the manifest's: a
field's subfields first, in the taxonomy's order, then its other children, each
after the siblings whose pages its pages use (`generate_wiki.dependency_order`),
the rest by title, titles equal up to case by file name. Like `subject_tree`,
the importer builds the new folders from their children up, so that this order
sees the pages inside each new subfolder. A new topic titled like its new field
or subfield (the same title, up to case and en dashes) is that folder's own
material, as `generate_wiki.namesake_first` reads it: when the folder's list,
with the topic's entries in the topic's place, holds at most 20 entries
(`generate_wiki.MAX_CHILDREN`), the topic has no folder of its own and its
entries lead that list where `generate_wiki.dependency_order` allows; otherwise
it keeps its folder. A new folder is listed on its parent's folder page, and one
with more than 20 entries is split into transparent `part-NN` folders, named by
number, as `generate_wiki.chunk` splits a list in that order. Every page of the
manifest must end up in the layout once, with a path of its own; a page that
does not is refused by name. An existing folder keeps its children where they
are: when its new children would take it above the limit Autoform's audit sets
(24 direct children, 120 for a `navigation: module` page), they are grouped, in
manifest order, into new transparent parts of up to 20 entries, numbered after
its own and titled `Part N` by their number, and a folder that would still be
above the limit is refused. A subject folder holds its fields only and is never
split.

A folder and its transparent parts have one list, and so one set of names: those
of the pages and subfolders of the folder and of every one of its parts,
existing or new. A page's file name is its `stem`. New folders take their names
first; pages then take theirs in manifest order. A stem that its folder's list
already has, from an existing page or folder, a new folder or an earlier row
placed anywhere in that list, that is reserved (`readme`, `index`, `part-NN`) or
whose address `scripts/card-moves.jsonl` records is refused, with the collision
named: it is never numbered, as a numbered name could hide a duplicate. A new
field, subfield or topic folder takes its name from the taxonomy, which may not
have a part's form, and is refused if its folder's list has that name or the
move ledger records its address. A new part is numbered after the parts its
folder already has (`generate_wiki.chunk` numbers those of a new folder), so
that no two parts of a folder share a name, and it is refused if its path is
taken.

`sync_wiki.add_to_listing` lists each new page and folder on the page of the
existing folder it goes in: a folder after the folders the page lists, a page at
the end of the page's own list. On a folder page that the sync only appends to,
one that is not simple ([Maintaining
articles](BLUEPRINT.md#maintaining-articles)), the item goes right after the
page's own list, when the page renders as meant there by the check the sync
applies to its own edits, and the plan lists it as a "fallback insertion on a
non-simple folder page". A folder page split into parts copies each part's list
under the heading that links the part; when a page joins an existing part, that
copy gains its item too, as `sync_wiki.with_part_lists` keeps it. An item that
cannot be placed so, a copy that is not its part's list as it stands or would
not show as meant, and an edit that would change any line of a page, are
refused.

## Annotations

Each new page and folder page gets one annotation row, appended to its
subject's links file. A page's row has:

- `id`: `af_` and the first 24 hex digits of the SHA-256 of the compact JSON
  array `["<seed.source>","<seed.node>","<seed.revision>"]`; an id that an
  annotation already has is refused;
- `extensions.org.atlas-wiki.seed`: the row's seed, `{source, node, revision}`;
- for a page with a pending prerequisite, `extensions.org.atlas-wiki.pending`,
  the row's `pending` list, and `extensions.org.autoform.not_ready: true`
  ([Nodes still to expand](BLUEPRINT.md#nodes-still-to-expand)).
- for a `mathlib` row, `object`: one Lean link to Mathlib's repository,
  `https://github.com/leanprover-community/mathlib4`, whose `location` is the
  row's `declaration` and `module`; and `extensions.org.autoform.mathlib: true`,
  as [Mathlib-credited pages](BLUEPRINT.md#mathlib-credited-pages) specifies.

No row gets a `kind` or a `status`, which the tools own, and only a `mathlib`
row's page gets an `object`. A folder page's row has its `id`, the same digest
of `["folder","<folder path>","<manifest SHA-256>"]`, and a part's has
`navigation: transparent`.

## The map

`scripts/mathgraph-map.jsonl` is a one-way record of the rows applied: each
applied row adds one line, in manifest order, and the first import creates the
file. It keeps each line's `mg_statement_sha256`, `mg_sketch_sha256`,
`reference_sha256` and `edges_sha256` so that a later release can tell which
results changed upstream since they were applied, which a page whose text was
adapted does not hide. This release compares nothing and has no update path, and
it refuses to import a key the map holds.
A line has:

| Field | Value |
| --- | --- |
| `key` | the mathgraph key |
| `node`, `revision` | the seed's mathgraph id and revision |
| `page` | the page written |
| `statement_sha256`, `sketch_sha256` | the digests of the page's statement and sketch |
| `mg_statement_sha256`, `mg_sketch_sha256` | the digests of mathgraph's statement and sketch |
| `reference_sha256`, `edges_sha256` | the digests of mathgraph's reference and outgoing edges |
| `pending` | the row's `pending` list |
| `mathlib` | for a `mathlib` row only: its `declaration` and `module`, and `rev`, the Mathlib revision lake-manifest.json pins when it is imported |

Every line must match this JSON Schema, `MAP_SCHEMA` in the importer, each
`pattern` a full-string match as in the manifest's; a test keeps the two equal:

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "A line of the mathgraph import map",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "key", "node", "revision", "page", "statement_sha256", "sketch_sha256", "mg_statement_sha256",
    "mg_sketch_sha256", "reference_sha256", "edges_sha256", "pending"
  ],
  "properties": {
    "key": {"$ref": "#/$defs/key"},
    "node": {"type": "string", "pattern": "^mg_[0-9a-f]{24}$"},
    "revision": {"type": "string", "pattern": "^[0-9a-f]{40}$"},
    "page": {
      "type": "string",
      "pattern": "^blueprint/roadmap/[A-Z][A-Za-z]*(?:/[a-z0-9]+(?:-[a-z0-9]+)*)*/[a-z0-9]+(?:-[a-z0-9]+)*\\.md$"
    },
    "statement_sha256": {"$ref": "#/$defs/sha256"},
    "sketch_sha256": {"$ref": "#/$defs/sha256"},
    "mg_statement_sha256": {"$ref": "#/$defs/sha256"},
    "mg_sketch_sha256": {"$ref": "#/$defs/sha256"},
    "reference_sha256": {"$ref": "#/$defs/sha256"},
    "edges_sha256": {"$ref": "#/$defs/sha256"},
    "pending": {
      "type": "array",
      "items": {
        "type": "object",
        "additionalProperties": false,
        "required": ["key", "kind", "reason"],
        "properties": {
          "key": {"$ref": "#/$defs/key"},
          "kind": {"enum": ["statement", "proof"]},
          "reason": {
            "enum": [
              "not-imported", "under-review", "source-unverified", "covered-by-generalization"
            ]
          }
        }
      }
    },
    "mathlib": {
      "type": "object",
      "additionalProperties": false,
      "required": ["declaration", "module", "rev"],
      "properties": {
        "declaration": {"$ref": "#/$defs/declaration"},
        "module": {"$ref": "#/$defs/module"},
        "rev": {"type": "string", "pattern": "^[0-9a-f]{40}$"}
      }
    }
  },
  "if": {"required": ["mathlib"]},
  "then": {
    "properties": {
      "pending": {"maxItems": 0},
      "sketch_sha256": {"const": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}
    }
  },
  "$defs": {
    "key": {"type": "string", "pattern": "^[a-z0-9]+(?:-[a-z0-9]+)*$", "maxLength": 96},
    "sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
    "declaration": {"type": "string", "pattern": "^\\S+$"},
    "module": {"type": "string", "pattern": "^Mathlib(?:\\.[A-Za-z0-9_']+)+$"}
  }
}
```

A line must also be in the form the importer writes: the fields in the order
above, a `pending` entry's as `key`, `kind`, `reason`, and `mathlib`, when the
line has it, last, as `declaration`, `module`, `rev`, serialised by `json.dumps`
with its default separators (`, ` and `: `) and non-ASCII characters as they are
(`ensure_ascii=False`), then a line break. It is also held to those rules of a
manifest row that need nothing but the line itself: its `node` is mathgraph's id
of its `key`, its `page` lies in a folder a manifest's `page_dir` can name, at
least one folder below its subject, under a file name a new page may take (not
`readme`, `index` or `part-NN`, and at most 96 characters), its `pending` list
names neither its own `key` nor a key twice, and a line with `mathlib` has no
`pending` entry and the `sketch_sha256` of the empty string, as its row has
neither. Across lines, no two have the same `key` or the same `page`, and the
check looks strictly backwards: no `pending` key of a line is the key of an
earlier line, as the importer refuses a pending key the map holds. A line is
never judged by a later one, nor against the pages. A later change that tightens
these rules must accept every line already on `main`, as lines are never edited.
`--check` and `--apply` refuse a map with any other line, naming it, and write
nothing; so does `--check-map`.

The importer only appends to the map: it never edits, removes or moves a line,
and never edits a planned page an earlier import wrote or that page's
annotation. A line's `pending` is a snapshot of its row's list as it was
imported: when one of those prerequisites is imported later, its own line is
appended, and the older line and planned page stay as written
([Policy](#policy), "`pending` and `not_ready`"). With `--base <commit>`,
`--check-map` also reads the map at that commit with `git` (a map absent there
is empty), checks its lines the same way, and refuses the map unless that one is
its start, ending at a line break, naming the first line that differs.

It then checks each line appended since that commit against the page it records,
which the same change must add: the page is not in the commit's tree and is a
file in the worktree, with no symbolic link on its path, and it has exactly one
annotation row, whose seed is the line's (`source` `mathgraph`, the line's
`node` and `revision`), whose `id` is the one that seed gives, whose `pending`
list, none when it records none, is the line's, and which credits, as
`sync_wiki.py` reads it (`page_owner`), the declaration and module of the line's
`mathlib`, which no other page may credit, to Mathlib or as this project's, and
whose `rev` must be the Mathlib revision lake-manifest.json pins, or no
declaration when the line has none. The line's `statement_sha256` and
`sketch_sha256` must be those of the page's statement and `## Proof sketch` (the
empty string when it has none) as Autoform reads them, computed again with the
importer's own functions. The line's `mg_statement_sha256`, `mg_sketch_sha256`,
`reference_sha256` and `edges_sha256` come from mathgraph, which the importer
does not read, and are not recomputed. The check binds a line to its page and
annotation; it cannot tell whether the importer wrote them, nor whether a
declaration is Mathlib's. The lines of the map at that commit are never checked
against the pages, which may have moved since; without `--base`, the lines are
checked alone.

Blueprint Pages runs `--check-map` right after the wiki tests: on a pull request
that changes one of the paths that let its build run, the map among them, with
the base commit as `--base`, and on its runs of `main` without. Blueprint Pages
is not a required check
([GitHub Actions and publication](BLUEPRINT.md#github-actions-and-publication)):
it reports a map that fails these checks, but does not by itself stop a merge.

Content PRs add lines to it, so it is a graph file: the
[graph rules](BLUEPRINT.md#graph-rules) and `REVIEWING.md` list it with the
graph paths, a pull request that changes it runs Blueprint Pages, and
`.github/CODEOWNERS` gives it the owners of the wiki tooling.

## Policy

These are the port's rules for the people who build, review and apply manifests
and edit the pages; the importer checks only what the sections above say it
checks.

- **Only a reviewed manifest publishes.** What the importer writes comes only
  from the rows of a manifest the review approved, applied at the SHA-256 it
  approved. Everything else, mathgraph's other results and the records the
  manifest is built from, stays private.
- **Each manifest is reviewed in full** (every row, no sampling) before it is
  applied; the PR body names the manifest's SHA-256 and the review.
- **Planned and Mathlib-credited pages only.** This release writes planned pages
  and pages credited to one Mathlib declaration, and records no existing page as
  standing for a result. A `mathlib` row's page states what its declaration
  states. For each `mathlib` row, the manifest's review checks the declaration
  against the pinned source and records that no ATLAS declaration, paged or
  unpaged, states the result, so that only Mathlib proves it, and that the
  Mathlib declaration has one page. The manifest PR's Blueprint Pages job must
  pass, its `lean-facts` step reporting none of the manifest's pages as
  unlinked.
- **Inputs fail closed.** A failed check writes nothing, and an exception
  while writing is rolled back, within the limits [Running it](#running-it)
  states.
- **Statuses are not exported.** mathgraph's kinds, tiers and verdicts never
  become annotation facts: a page the importer writes has no kind or status
  ([What the tools own](BLUEPRINT.md#what-the-tools-own)).
- **Dependencies on exact identities only.** A planned page is imported with
  dependencies on another row's page, or on an existing page whose statement and
  annotation are the ones reviewed. A result an existing page covers only by
  generalization is no dependency: it stays under `pending`, with reason
  `covered-by-generalization`. The manifest's builder leaves out (holds) a row
  whose live endpoint's identity or statement cannot be confirmed: it is not
  linked.
- **`pending` and `not_ready`.** A planned page with a prerequisite not yet
  linked by the import lists it under `pending`, says under `## Expansion` what
  a good expansion contains, and is marked `not_ready`, so that it never looks
  complete. A pending entry does not imply that no page states the prerequisite.
  The importer never edits a planned page an earlier import wrote, that page's
  annotation or its line of the map, which keeps its snapshot: an older page
  keeps its pending entries, its `## Expansion` and its `not_ready` when a
  prerequisite is imported later. They stay until an editor changes the page. An
  editor who links a prerequisite under `## Depends on` or `## Proof depends on`
  removes its entry in the same change, and `## Expansion` and `not_ready` with
  the last entry; an expansion that replaces the page follows
  [Nodes still to expand](BLUEPRINT.md#nodes-still-to-expand). No tool makes or
  checks either edit; each is reviewed like any page edit.
- **Sources at book level unless verified.** A source names a work at book
  level: authors, title, edition, publisher and year. A chapter, section,
  theorem or page number appears only once it has been checked against that
  edition, as for any planned page
  ([Writing pages](BLUEPRINT.md#writing-pages), "Be unambiguous").
- **No `## Informally uses`.** mathgraph's proof routes are sketches, not the
  cited source's proof: they become `## Proof sketch` prose and the planned
  page's own dependency sections.
- **Credit.** Every commit that adds mathgraph's text carries the trailer
  `Co-authored-by: Jack McCarthy <Deicyde@users.noreply.github.com>`, and the
  PR body says that the pages are adapted from Jack McCarthy's mathgraph at the
  revision the seeds name. A page records where it comes from in its `seed`,
  not in its prose.
