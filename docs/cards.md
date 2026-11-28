# Cards: the wiki's reading level

A statement page states one precise result, usually one Lean declaration. Readers navigate by larger
units: the concepts a textbook gives a paragraph to and the theorems worth naming. A **card** is that
unit: a **concept card** (a definition with its basic facts) or a **result card** (a theorem with the
lemmas that serve it). Cards group statement pages; they never replace them. The statement pages stay
the formal layer: their annotations, the sync, readiness, work dispatch and status are unchanged, and
every edge between cards is derived from the edges between their statements.

`scripts/cards.py` checks the cards and derives their data. This page gives the format, the identity
rules, the derived data and the commands. The graph rules' [Cards](BLUEPRINT.md#cards) section points
here.

Below, a *statement page* (or *leaf*) is any page of `blueprint/roadmap/` that is not a folder page.
It is *credited* when its annotation names a declaration, of ATLAS or, through Autoform's Mathlib end,
of Mathlib, and *page-only* (planned) otherwise.

## A card is a folder

A card is a folder whose folder page's annotation carries a card record under
`extensions["org.atlas-wiki"]["card"]`. Either an existing topic or module folder whose whole content
is one idea becomes a card, and nothing moves; or a new subfolder of a topic or module folder gathers
the pages of one of its ideas, which move in with `autoform move` (article ids kept, links rewritten)
and are recorded in the move ledger below. A page without an `id` gets one before it moves.

```json
{"subject": [{"type": "generic", "uri": "../roadmap/MeasureTheory/<field>/<topic>/<card>/README.md"}],
 "id": "af_0123456789abcdef01234567",
 "extensions": {"org.atlas-wiki": {"card": {
   "kind": "result",
   "main_article_id": "af_89abcdef0123456789abcdef",
   "importance": "landmark",
   "level": "graduate",
   "supports": ["af_..."],
   "seeds": [{"source": "<collection>", "node": "<its id>", "revision": "<40-hex commit>"}]}}}}
```

| Field | Required | Meaning |
|---|---|---|
| row `id` | yes | The card's identity ([What the tools own](BLUEPRINT.md#what-the-tools-own)). A folder that becomes a card keeps its id; a missing one is minted fresh. |
| `kind` | yes | `concept` or `result`. |
| `main_article_id` | yes | The `id` of the card's main statement. |
| `importance` | yes | `landmark`, `key` or `supporting`, as reviewed. |
| `level` | yes | `undergraduate`, `graduate` or `research`; for filtering only. |
| `supports` | no | Ids of statement pages outside the folder that the card presents, such as shared lemmas. Shown, never counted. |
| `seeds` | no | Provenance of an imported outline record: exactly `source`, `node` and `revision`, a full commit. |

A card credits no declaration: its annotation has no `object`, `kind`, `status` or held marker, and no
`org.autoform` key but `navigation` and `area`; its folder page has no frontmatter. So Autoform counts,
schedules and rates its statement pages exactly as before. A card record belongs on a folder page's row
only; on a statement page's row it is an error.

The folder page, read as Autoform reads it (code fences, indented code and HTML comments are blanked
first, so a heading, a link or a list item inside one does not count, and a heading reads without its
comments):

- `# Title`: the concept's or the result's name.
- The opening, before the first `##`: the main statement in words, with every hypothesis that changes
  its meaning ([Writing pages](BLUEPRINT.md#writing-pages), against the main statement), or the
  definition in words.
- `## Idea`: a short explanation for a learner: why it matters, the intuition, a proof idea or an example.
- `## Statements`: each page of the folder exactly once, main statement first, one top-level list item
  each that opens with its link, `- [title](page.md)`, with a title a reader can see; text after the link
  may say why the page is there ("a stronger form", "used in the proof"). The list is read as the site
  renders it: a link outside such an item, or lines run into the paragraph before them, list nothing.
- The page is plain Markdown that Autoform publishes as such: raw HTML, which makes Autoform publish the
  page as typed text with no live link, is an error.
- `## Background` (optional): links to other cards a reader should know first. They are teaching links:
  they never count for readiness, status or the derived edges.
- `## In Mathlib` (optional): Mathlib facts with no page of their own, each linked to its source line at
  the pinned Mathlib with the declaration's name as the link's title,
  `[text](https://github.com/leanprover-community/mathlib4/blob/<pin>/<Module/Path>.lean#L<line> "<name>")`.
  The check verifies the link's form (a plain module path with no dot segment or escape, no query, a
  fragment `L<line>`), the pin, and that the title has the
  form of a Lean name (primes and all); that it is
  the declaration on that line is for review, since the build has no index of Mathlib's sources.
- `## Sources` (optional): literature, at the precision that has been checked.
- Never `## Depends on`, `## Proof depends on` or `## Informally uses`: a card's edges come from its
  statements, and what a proof cites belongs to the statement it proves ([Writing pages](BLUEPRINT.md#writing-pages)
  and [What the tools own](BLUEPRINT.md#what-the-tools-own)).

## Identity and membership

- The card is its row `id`, whatever its path; an id is never reused.
- The main statement is a page of the folder with an `id`, and heads no other card. Moving the card to
  an equivalent main statement keeps its id; a main statement with different mathematics makes a new
  card, and the old one is retired.
- A split keeps the id on the part that keeps the main statement; a merge keeps the id of the card whose
  main statement survives. A retired id is recorded in the move ledger with what replaces it.
- A card holds only statement pages, 1 to 24 of them (Autoform's `overfull-container` limit), and is a
  topic folder or a folder inside one, never a subject, a field, a subfield (`scripts/taxonomy.json`) or a
  `part-NN` folder the generator adds to split a long list.
- A statement page's home is its folder when that folder is a card; otherwise it is *unassigned*.
  `supports` is a separate, many-to-many relation; a page never supports its own card.
- `sync_wiki.py declarations` never places a new page inside a card or below one: such a page goes to the
  card's parent folder, and the run lists it as unassigned for an editor. No new page takes the name of
  a folder (a folder page has its folder's node id) or an address the move ledger records.

## Status

A card's **headline** is the first that applies to its main statement: `stale` (the committed row names
a declaration that `lean-facts` dropped because the Lean no longer has it), `held`, `not ready`,
`page only` (a planned page with no declaration kind: it is no task, as the graph rules' planned pages
and tasks say, so it is never shown as ready), then Autoform's state of the page, credited or with the kind
`lean-facts` gives a planned page that counts as a statement not yet in Lean: in Mathlib, fully proved, proved
(not fully), defined, conditionally proved, ready to prove, stated with its proof blocked, ready to
state, blocked. Its **supporting progress** counts its other statements, each once, by the same
precedence; the main statement is never among them. Readiness and tasks stay Autoform's.

## Counterparts

A planned statement page, a live page Autoform reads whose annotation links no Lean declaration (no Lean
link naming one, of any repository, and no module and name an earlier sync wrote), may record its
counterparts: the Mathlib or ATLAS declarations that state its result or a form close to it, as when a
card's planned main states an imported result that no declaration states exactly. They go under
`extensions["org.atlas-wiki"]["counterpart"]` of the page's own row, never anywhere in the links folder's
defaults (`_defaults.json`, a card record there included), which would give them to every row; they are a
list of one or more records:

```json
"counterpart": [{"mathlib": "<Mathlib name>", "relation": "weaker",
                 "needs": [{"mathlib": "<Mathlib name>"}, {"atlas": "<ATLAS name>"}]}]
```

- exactly one of `mathlib` and `atlas`: the declaration's full Lean name, as Lean stores it, without the
  `_root_.` prefix that only Lean source writes;
- `relation`: how the declaration compares with the page's statement: `same` (it states it), `stronger`
  (it implies it), `weaker` (the statement implies it) or `variant` (a related form, neither);
- `needs` (optional): the other declarations that, with it, give the page's statement, as when the
  statement combines several results; each is `{"mathlib": name}` or `{"atlas": name}`, since a
  combination may take declarations of both.

A record has no other key, a list names no declaration twice, and a record's own declaration is not among
its needs; names are compared as Lean reads them, so `Matrix.«det»` is `Matrix.det`, while `«a.b».c` is
not `a.b.c`. Each record is verified clause by clause against its declaration, at the pinned Mathlib or in
the project's Lean, before it is written. A counterpart is data only: it gives the page no credit, makes
no edge, and never changes readiness, status or the derived data. `needs` lists no prerequisites: the
page's own `## Depends on` and `## Proof depends on` follow the proof it states, as for any planned page.
`scripts/cards.py check` verifies the form (the keys, the relation, and that each name has the form of a
Lean name, not that the declaration exists or says what the record claims, which is for review) and the
place: a counterpart on a row whose page is missing or that Autoform does not read, on a page whose
annotation links a Lean declaration, as checked out or as committed, on a folder page, in a card record or
in the links folder's defaults is an error.

## Derived data

`scripts/cards.py rollup` writes `build/cards.json` (schema `atlas-cards/v1`), a build output that is
never committed ([What the tools own](BLUEPRINT.md#what-the-tools-own)). It reads the build's checkout after `sync_wiki.py lean-facts`, the
annotations as committed, and the extraction lean-facts used, which it requires: it runs only after the
strict check below passed. Identical inputs give identical bytes.

- `commit` and `pages`: the source commit, and each statement page the file mentions (in a card, a
  witness, a walk, `supports` or `unassigned`), by path, with its `article_id` (or null), credit,
  markers, Autoform state, declaration kind and card. A row an earlier sync wrote with a module and a
  name counts as ATLAS credit only once lean-facts gave the build's row the Lean link of the one declaration
  the Lean index finds for it; otherwise its page is stale.
- Each dependency has an **origin**: `compiled` between two ATLAS-credited pages, an edge the strict check
  matched against the extraction, or `planned` from a page-only page (written by hand, as
  [Writing pages](BLUEPRINT.md#writing-pages) says),
  whatever its target, a Mathlib-credited page included; `bridge` from an ATLAS-credited page to a
  Mathlib-credited one, and `mathlib` between two Mathlib-credited pages, which the strict check matched
  against the build's Mathlib registry ([Mathlib-credited pages](BLUEPRINT.md#mathlib-credited-pages)). The registry
  follows uses through declarations of the project and of Mathlib that no page credits, by the rule the
  extraction applies to the project's own constants, but a bridge comes only from what a statement or a
  proof names itself: one that reaches a Mathlib-credited page only through other declarations gives no
  bridge. The check also requires that the registry was made from the committed rows' credited names and
  `duplicates` lists, that
  its edges join declarations pages credit to ones it found, none both kept and left out, and that it finds
  exactly the declarations the build's pages credit to Mathlib,
  one page each, each page keeping the declaration its committed row credits; a Mathlib main heads a result
  card exactly when the registry finds that its type is a proposition, and a concept card otherwise.
  Without the registry, such edges and any edge a Mathlib-credited page lists are errors. Only statement
  pages Autoform loaded count, each by its own file: a row whose page is gone credits nothing, even where
  a folder page now has its node id.
- `uses`: card X uses card Y when a statement of X depends on a statement of Y. Each edge keeps every
  such dependency as a witness (`source`, `target`, `kind`, `origin`) with counts. A compiled dependency
  that is both a statement and a proof dependency is a statement one, as the extraction writes it; a
  page-only page that names a prerequisite under both kinds keeps both witnesses. The map may contain
  cycles: it reads "some statement of X uses some statement of Y", not "X comes first".
- `needs`: X needs Y (X ≠ Y) when X's main statement reaches Y's main statement through statements that
  are no card's main statement, wherever they live; a walk never passes through a folder page. Each edge carries a typed walk: `statement_walk`,
  using statement dependencies only, when one exists (phase `statement`); otherwise `walk` (phase
  `proof`). Ties go to the smallest sequence of paths. `needs` is acyclic because Autoform's graph is,
  and walks through it join into real statement-level walks, not necessarily shortest ones.
- `clusters`: each mutually reachable group of two or more cards (a strongly connected part of `uses`:
  each card of the group uses every other one, directly or through cards of the group), with its `uses` edges and
  one closed walk, `example_cycle`. No edge is dropped to make the map acyclic.
- `edges`: every dependency out of a card's statement, counted once: inside the card, to another card,
  to an unassigned page of a subject with cards, to a subject without cards, or to a folder page.
- `unassigned`: the statement pages of subjects with cards that no card holds.

## Checks and CI

`python scripts/cards.py check` fails on any malformed card record or id, a credited card, a nested card
or one that is a subject or field, a card with no page or more than 24, a main statement that is not a
page of the folder, has no id or heads another card, a main statement whose declaration kind does not
fit the card (a definition for a concept card, a theorem for a result card), whether it is credited or
has the kind `lean-facts` gives a planned page that counts as a statement not yet in Lean (a page-only
main statement with no kind is classified by its editors), a bad `supports` entry (one that names no statement page Autoform reads)
or seed entry, an earlier sync's declaration credit (`module`, `name`) on a card's annotation, a link to
another card's page outside `## Background` (or to a statement of another card other than its main
statement), an empty opening or `## Idea`,
a `## Statements` list that misses a page, repeats one or lists another, or does not start with the
main statement (every link of that section to a statement page counts, nested or in prose, and a
statement's box on a folder page, `#leaf` or `../other/README.md#leaf` (Autoform boxes a leaf that
declares something), is no way to link it there; other heading anchors are left alone), a forbidden section, an `## In Mathlib` link that is not a source line at the pinned
Mathlib titled with something of the form of a Lean name, a dependency on a card's folder page or one Autoform reads on it, a card record on a
statement page, a held marker that credit would override (a held row that credits a declaration, or a held
declaration another row credits), a malformed or misplaced counterpart ([Counterparts](#counterparts)), and
a bad move ledger. With `--dependencies build/lean-dependencies.json` (the strict check), the dependencies
of the checkout must equal the extraction's as sets of typed, oriented edges,
both ways: a dependency only one side has, a flipped kind, a target listed under both kinds, an
extracted declaration that credits no statement page, or a page whose declaration lean-facts found but the
extraction has no row for is an error, and the move ledger must exist. With
`--registry build/mathlib-registry.json`, the edges that reach Mathlib-credited pages must likewise equal
the registry's bridges and Mathlib edges; without it, they are errors, and so is any edge from a
Mathlib-credited page to a page that is not one, always. A `--registry` file that holds no JSON object is
an error, never a run without one, and so is a registry not of the extractor's form (a table of another
type, say), reported before any of its tables is read, or one made with another extraction than the one
given (the two are valid only as the pair one extractor run wrote). With `--base-ledger`, `--base-links` and
`--renames` (given together, or not at all), the ledger and the moves since the base commit are checked as
the move ledger section says. It warns about a `## Background` link that is not a card's page, a circle of
`## Background` links (a card linking itself there included), an `## Informally uses` link to a card, and a
module-and-name row lean-facts gave no Lean link (the Lean index resolves it to no one declaration).

The workflow tests the card scripts and runs `rollup`, which checks first, in their own read-only job,
`check the cards`, after `build the wiki` and from its `blueprint-dependencies` artifact; on a pull
request it passes the base commit's ledger (its frozen file and fragments) and annotations and Git's renames since
that commit. A pull request runs it only when the site's build runs, as when the PR changes the wiki, either ledger
or what builds and checks the site, and a merge group never does
([GitHub Actions and publication](BLUEPRINT.md#github-actions-and-publication)). It keeps
`build/cards.json` as the `cards` artifact. CI's required `check the graph` job checks the move ledger's integrity on
every pull request and merge group, with `scripts/card_moves.py check`, and only `check the cards` reconciles the
moves since the base with it ([Move ledger](#move-ledger)). The wiki job
runs the site hook's tests (`scripts/test_card_pages.py`) with its other tests and leaves
`scripts/test_cards.py` and the strict check of the content and its history to the card job; it runs
`moves` once, for the moved addresses its site keeps, and `rollup` once, for the card data its site shows, each in
a step of its own that fails closed and cannot fail the job ([Reading](#reading)). The site's deployment needs
only the wiki job.

```sh
python scripts/sync_wiki.py lean-facts build/lean-dependencies.json --registry build/mathlib-registry.json
python scripts/cards.py moves build/card-moves.json
python scripts/cards.py rollup build/cards.json --dependencies build/lean-dependencies.json \
  --registry build/mathlib-registry.json \
  [--base-ledger <a folder with the base commit's card-moves.jsonl and card-moves.d/> \
   --base-links <its blueprint/links/> --renames <git diff --name-status -M BASE HEAD -- blueprint/roadmap>]
```

## Move ledger

The move ledger records, one JSON object per line, never rewritten, every change that retires an address
(paths are Autoform ids: below `roadmap/`, without `.md`):

- a moved statement page: `{"page": "<old path>", "to": "<new path>", "article_id": "af_..."}`;
- a moved or renamed folder that keeps its id: `{"folder": "<old path>", "to": "<new path>", "article_id": "af_..."}`;
- a retired card: `{"card": "af_...", "folder": "<its last path>", "replaced_by": "af_..."}`;
- a retired statement page, such as a node an expansion replaces and deletes:
  `{"statement": "af_...", "page": "<its last path>", "replaced_by": "af_..."}`, where `replaced_by` is the id of
  the live statement page or folder page a reader of the old page should go to, named by id so that its later
  moves are followed.

A folder row moves the folder alone, its folder page and its address: each page and folder inside it that
moves has its own row, so the history never depends on what the folder holds later. Renaming a folder `a` to
`b` with its page `a/x` takes two rows, `a` to `b` and `a/x` to `b/x`; a page later added to `b` needs none.
An ordinary page or annotation change needs no row.

The ledger has two parts, so that two changes that add rows write distinct files, which avoids the conflict Git finds
when both append to the end of one file:

- `scripts/card-moves.jsonl`, frozen: the rows written before the ledger was split, which no change edits;
- `scripts/card-moves.d/`, one fragment per change: a file named `<YYYYMMDDTHHMMSSZ>-<slug>.jsonl` with the UTC time
  it was made, or one second after the latest fragment the checkout and base hold, if that is later, in ASCII
  digits, and a slug of lowercase letters, digits and hyphens, holding at least one row. Every entry of the folder
  is such a regular file, its stamp a real time; anything else is an error. A missing or empty folder holds no
  fragment. The folder and the fragments, like the frozen file, are a real directory and regular files, never
  symbolic links: every reader refuses a link, in the checkout or committed.

The logical ledger is the frozen file's rows, then each fragment's, in byte order of their names, each file's rows
in their order; each file is read on its own, line by line, so one with no final newline joins no rows. Every reader
reads it so: `scripts/card_moves.py` for the scripts, which prints a revision's logical ledger one row a line
(`python scripts/card_moves.py <revision>`), and a copy in the site hook. `python scripts/card_moves.py new-moves
<slug>` writes an empty fragment named with the UTC time it was made, or one second after the latest fragment the
checkout and base (`--base`, `origin/main` by default) hold, if that is later, so that it never starts out sorting
before a fragment it knows: a change's rows go in it in the order they happened. Each helper refuses a base it
cannot read in full, writing nothing: one whose folder of fragments holds a malformed entry, or that has no frozen
file. Rows a branch appended to the frozen file before the split move into a new fragment with `new-moves <slug>
--take-appended`, which restores the frozen file; it refuses unless the base's frozen file (`--base`, `origin/main`
by default) starts the branch's, byte for byte. Neither writes over a file, nor through a link: each writes in the
checkout it is run from, the Git top level of the current folder, and refuses before it writes unless the script run
is that checkout's own `scripts/card_moves.py`, or when `scripts/` or `scripts/card-moves.d` is a link or no folder,
or the fragment's name, or the frozen file it restores, is a link.

A fragment may sort anywhere: its stamp orders it, and nothing forces it after the fragments of its base. A row
comes after the rows it builds on: a move or retirement of an article builds on the move that put it at that
address; a retirement in place builds on the retirement there that named it as the replacement; and a move into an
address builds on the retirement there of an earlier occupant whose replacements lead to the article moving in,
which freed the address for it, page or folder alike, since a page and a folder of one name share an address
(retirements there of later occupants, which it handed the address to, are none of its prerequisites). A row before
one it builds on is an error that names the fragment sorting after its own and how to order the two. Where nothing
vouches for their order, two fragments must be independent: each new fragment (one the base commit lacks) and each
fragment of the base that sorts after it, and each two new fragments. Neither may write what the other writes or
reads. A fragment writes every address whose resolution its rows set (a move's old and new address, a retirement's
last one), every id they move or retire, and every folder above an address they leave that the site's replay could
find gone at that point and lead where its nearest enclosing folder leads: up to the first one that is live, that no
folder row moves into, and whose address no page row or statement retirement names. It reads every folder above an
address it writes, so that two moves under one folder are independent. A retirement's replacement is neither: it is
resolved by id at the end, where the check follows every chain to its live owner, so that a retirement of x for y
and one of y for z resolve x to z in either order, and one of y for x makes a loop the check refuses. Fragments that
do not interact are meant to resolve alike in either order, which the tests check on sampled histories without
proving it in general. Fragments that interact are refused:

- a new fragment that sorts before an interacting fragment of the base is restamped with `python
  scripts/card_moves.py new-moves --restamp <file>`, which renames a fragment the base lacks to the current time, or to
  one second after the latest other fragment the checkout and base hold, if that is later, keeping its slug and
  bytes, so that it sorts after every one of them, one stamped ahead of the clock or in the same second included (it
  refuses a link as the other helpers do, and a fragment that is one);
- two new fragments that interact go into one fragment, in the order the rows happened, or one change lands
  first and the other is checked again with it in its base: a stamp orders fragments by name only, so no restamp
  makes them independent.

A new fragment's stamp is no more than an hour past the check's clock; no helper names one further ahead: each
refuses then, writing nothing, and says when it can run. Nor does one name a fragment after one stamped 9999-12-31
23:59:59, the last stamp a name can have: it refuses, writing nothing, naming that fragment and saying that waiting
will not help. In the merge-group runs sampled when the ledger was split, each group's branch was built on the group
before it, which is consistent with a fragment queued earlier being in the base of the ones after it; the guard does
not rely on it, since it holds new fragments both to the published ones that sort after them and to each other.

Against the base commit, the frozen file is the base's, byte for byte, and every fragment the base has is there
under its name, unchanged: a published part is never edited, deleted, renamed or made another kind of file. A base
whose ledger cannot be read is an error, never an empty ledger. The new fragments are the ones the base lacks, found
by their paths, never by a count of rows.

The check follows every chain to its final live destination: the old path is gone; every hop keeps the id the chain
started with, so an old address always leads, through the ledger, to its own article (the site has to serve these
rows as redirects before a card change that moves a page is published); a page ends at a live statement page and a
folder at a live folder page with that id (a card's or not), or at the card a retirement row records at that path; a
card is retired once, its id is no card's or statement page's any more, and what replaces it is a live card; a
statement is retired once, at the address its page rows leave it at, its page gone and its id no live page's or
folder's any more, and what replaces it is a live statement page or folder page, reached through any statement or
card retired on the way; nothing goes round. An article moves into an address once, as a page or as a folder: a
second move of it there, from another old address, would give it two histories, as it could not leave the address in
between. An address has one owner: it moves once, as a page or as a folder, or is the last address of retired cards or
of retired statements, each replaced in place by the next in the ledger's
order (two retirements there that are not are two owners, whatever their order), and no live page or folder of
another article takes it (the final replacement may live at its address, and a declassified folder keeps its own); a
page or folder page with no `id` is another article; a page `b.md` and a folder `b/` would share one address, so no
change leaves both.

`python scripts/card_moves.py check [--base <commit>]` runs the part of these checks that needs no other file: each
row's shape and the rules among the rows (an address moves once, as a page or as a folder, and is no retirement's
once it moved; an article moves into an address once; the retirements at an address hand it on in place; no chain of
moves or of replacements goes round, and every hop of a move keeps its article; each article has one history, its
moves ending where its retirement says, as the kind it is retired as, or at one address if it is retired as neither;
a card's replacements end at no retired statement and no page; what ends at a retired address is its final
replacement; no two articles' moves end at one address, nor at one another moved away from, page and folder alike;
every row comes after the rows it builds on), and, with `--base`, the base's frozen file and fragments unchanged,
the stamp bound and the independence of the new fragments. It reads the ledger's files and, for the independence of
the new fragments, which folders of `blueprint/roadmap/` the commit checked out has a folder page in, a regular
file, from Git's tree entries alone, their names, modes and types: no file of the roadmap, and nothing else; it
needs no package and writes nothing. CI's required `check the graph` job runs it on every pull request, with
`--base` the merge commit's first parent, and on every merge group, with `--base` the group's base commit, and stops
when that base cannot be read; a push to main and a manual run check the combined ledger alone, since a push carries
fragments that merge groups checked, which may build on one another. What needs the rest of the tree is not
required: `scripts/cards.py moves`, which the wiki job runs for the moved addresses its site keeps, also checks
where each chain ends, what holds a moved or retired address and that an id names one article, and writes the
receipt; `check the cards` also checks that every move since the base has its row; neither job gates a merge.

`python scripts/cards.py moves OUTPUT.json` checks the ledger alone, as above: the required check's rules, then each
chain against the annotations and the roadmap as checked out, with no card or dependency check. Without `--base` it
certifies the present snapshot only. With `--base <commit>` it also holds the ledger to that commit's: the frozen
file and the commit's fragments unchanged, and the new fragments independent, as above; it reads the base's ledger
from Git's trees alone, the checkout's identical files standing for the base's. It does not replay the changes since
that commit against the new fragments' rows: that reconciliation, below, is the strict check's alone. A missing
frozen file is an error, and so is a checkout with no commit to name; an empty ledger has no row. An id the ledger
names must be the id of one article. Reading each input file once, it removes its output first and, only when the
ledger is valid, writes its receipt, the same with `--base` or without, schema `atlas-card-moves/v3`, through a
temporary file: `commit`, the commit checked; `ledger_sha256`, a digest of the ledger's files it read, sha256 over
each in logical order as its path in the repository, a NUL, its length in bytes in decimal, a NUL and its bytes;
`annotations_sha256`, a digest of the bytes of `blueprint/links/` it read, sha256 over each `*.jsonl` file and
`_defaults.json`, in sorted order of name, as its name, a NUL, its length in bytes (`-` for a defaults file that is
no regular file), a NUL and its bytes; `cards`, each card by id with its folder, listing only a card whose id is an
article id no other article has and whose folder is an address as the ledger writes one (a path below `roadmap/`
without `.md`, `.` or `..` parts), which the hook requires too, and `cards_complete`, whether that lists every card;
and `replacements`, the live article each retirement's replacements end at, by id, with its kind (`page` or
`folder`) and node, each at such an address, or there is no receipt. The digests bind the receipt to the inputs it
checked, so that a receipt of other inputs is not taken for this one; they do not vouch for its contents, which come
from the job that makes it.

Given the base commit's ledger, its annotations and the files Git finds renamed since (`--base-ledger`, a folder
with the base's `card-moves.jsonl` and `card-moves.d/`, `--base-links` and `--renames`, which `check the cards`
gives the strict check on a pull request), the check also reconciles every change since the base with one map of who
owns what, the base's rows being published history:

- an article of the base is found in the checkout by its `id`; one without an `id` by its address (an
  `id` given in place), else by its declaration when exactly one page credits it on each side, else by
  Git's rename of its file, which never overrides a known `id` or declaration; two articles never become
  one;
- the rows of the new fragments are replayed in the ledger's order from the base: each moves what its old address
  holds at that point, with that article's `id`, or, for an article that had none, an `id` no article of the base or
  of the ledger ever had, and a folder row moves the folder alone; a retirement names the card's or the statement's
  address at that point, and a statement it retires was a statement page of the base; once retired, the address is
  free, so that the replacement may move in by a later row, never by an earlier one;
- afterwards every article stands where the rows leave it and keeps its `id`: an article of the base that
  is gone, with no row moving or retiring it, is an error, since its old address would lead nowhere (a page that
  moved with its folder but has no row of its own included); a statement a row retires is matched by Git's rename
  to nothing, since its replacements may take its prose; an address that changed hands is a retired card's or
  statement's, held by its final replacement; a new article takes an `id` no article ever had;
- but the folder page of an emptied plain folder, one that holds no page at any depth once the change is made (no
  file a page row can name, whatever folder pages are left below it; hidden files and directories, which render
  leaves out, hold none), may go with no row of its own when the file itself is removed, not its annotation row
  alone; no other article, page or folder, nor any file holds its address; a row of the ledger, the frozen file's
  or a fragment's, published or new, leaves an address below it; and the site keeps a route for its old address,
  which the check finds by replaying the ledger with the site hook's own resolution on render's index of the
  checkout. A warning then says where that route leads, as a row says it (a folder row, or the retirement of the
  card the folder was) or as the hook infers it, in the ledger's order. Otherwise its folder page stays: another
  article holding its address is said, and with no row below it the check says its old address would lead nowhere
  only when the site would keep no route for it either;
- every card of the base that is no card any more, gone or declassified, has its retirement (a
  declassified folder may keep its `id` as a plain folder).

## Reading

The site shows each card on its folder page. `build the wiki` derives the card data itself: after
`lean-facts` and before render, it runs `scripts/cards.py rollup build/cards.json` on its own checkout with
the extraction and the Mathlib registry it has just made, the inputs of `check the cards` but for the moves
since the base commit, which only that job checks. The rollup removes its output first and writes it only once the strict check
passes, whole, through a temporary file; an output inside `blueprint/` or the `--base-links` folder, one that
is one of its inputs, a symbolic link or no regular file is refused before anything is touched. A card error
cannot fail the job, which the step delays by at most
its ten-minute timeout: it leaves
no card data, the site shows no card but keeps every moved address, and `check the cards` reports the error.
In a step of its own beside it, independent of the strict check, the job runs `scripts/cards.py moves
build/card-moves.json` after removing any earlier receipt ([Move ledger](#move-ledger)). The hook itself is site
code: its tests (`scripts/test_card_pages.py`) run with the wiki job's other tests, so a regression in it fails
that job, as a change to any other part of the site does.

`hooks/card_pages.py` keeps the moved addresses only with the ledger check's receipt: an `atlas-card-moves/v3`
receipt of the commit being built whose digests are those of the ledger's files it reads (the frozen file must
exist, and every entry of `scripts/card-moves.d/` be a fragment) and of `blueprint/links/` as it is now, which shows the receipt refers to the current inputs, and only when every address
resolves to a page the site publishes, a retired card's folder or statement's page that is gone leading to the
folder or page the receipt gives its last replacement.
They need no card data. The hook shows card data only when `build/cards.json` is an `atlas-cards/v1` rollup of the
commit being built that names only pages the site publishes and whose parts agree where they restate one another:
each status with its statement's row in the `pages` table, each count with what it counts, and the clusters
with the strongly connected parts of `uses`; only with the moved addresses; and only when its cards are, folder
for folder, the receipt's, and the receipt lists them all. These checks catch a rollup that contradicts itself,
the site or the ledger check; they cannot tell a consistent rollup from the true one, which is the strict check's
work. So a card error never costs a moved address, and card data never changes where one leads.

When the hook shows neither, or has nothing to show, as on a commit with no card and no moved address, every page
is byte for byte the page of a build without it. None of this fails the build, and none of it is silent: the build
log says what is not shown and why, at INFO since `mkdocs build --strict` fails on a warning, and under GitHub
Actions so do a workflow annotation (a warning for card data, an error for moved addresses) and a line of the job
summary. Blueprint Pages nonetheless publishes nothing when the moved addresses
are not kept: a later step then fails `build the wiki`, on a pull request too,
before the site is kept or uploaded, so the last published site stays.

A card's folder page shows, before its first section, a block with:

- the card's kind, importance and level;
- its main statement with its status, as [Status](#status) gives it, and the progress of its other
  statements, or that it has none;
- the statements it presents from elsewhere (`supports`), listed apart;
- each edge derived from its statements, with the dependencies that witness it in a collapsed list: the
  cards it uses and the cards that use it, each dependency saying which statement uses which, in its
  statement or in its proof, and marked when it is not one Lean compiled between two ATLAS declarations
  (`planned`, and `bridge` or `Mathlib` for an edge the build's Mathlib registry vouches for); the cards its main
  statement needs and the cards whose main statement needs it, each with its walk, which goes through
  statements or, when one of its steps is a proof dependency, through a proof; and the cluster it belongs
  to, a group of cards that each use every other one, directly or through cards of the group, with its members
  and one cycle among them whose steps list their dependencies (no single cycle need pass through them all).

The block is plain HTML, styled by `theme/stylesheets/atlas-cards.css`: a reader without JavaScript reads it
as it is, and the explorer shows it in the page's reading.

Every address the move ledger retired keeps leading to its page. The hook resolves them all at once, by replaying
the ledger backwards from the pages the site publishes: each row's old address takes the place of its new one, so
every address a statement or a folder ever had is followed through every row after it, in order. A folder row moves
the folder alone, as the move ledger says, so no address is inferred from what a folder holds, and a page added to a
folder after it moved gets no old address. A retired card's folder that is gone leads to the live card its
replacements end at, a retired statement's page that is gone to the live statement page or folder page its
replacements end at, each where the receipt places it, and a folder that is gone with no row of its own to where its
nearest enclosing folder led at that point, a fallback. A folder whose folder page holds nothing below it any more,
such as one left when everything below it moved away, is not gone: render indexes it as a node at its own page,
plain or transparent alike, and its page keeps its address, with the old anchors of the statements that left it,
while its old explorer page, which render no longer writes, leads to that page, which loads the explorer's rewrite
table; what is bound to it leads to it, and
a retirement may be replaced by it. Such a folder holds its own address but not those above it: a folder gone above
it still gets its fallback. A folder page the site source has though render does not index it is kept as well, and
what is bound to it leads to the nearest folder above it whose page render publishes, since the explorer cannot
select it. No explorer link to an address render publishes, whatever holds it, is rewritten.
The replay keeps apart what held each folder address at each
point of the history and the route each old folder address keeps. What a folder row or a card's retirement says of a
folder is its route, whatever their order in the ledger, and no fallback replaces it; a folder that no row speaks of
keeps the fallback taken first in the history. A fallback stays bound to what held the address above it when it was
taken. A card's retirement says what the fallback in place at its folder leads to, and every fallback bound to that
one, at any depth, follows, unless a folder that a row said or the site had at that point lies between. A folder
row changes what holds its two addresses: a fallback taken below them after the change keeps what held the address
then, and a gone folder below them that is used before the change takes its fallback again, from what held the
address before it. So a fallback never follows a later or earlier holder of its parent's path. The same resolution
gives every route below.

Render publishes a statement with a declaration kind in a box on its folder's page, at
`<folder>/index.html#<file name>`, a statement without one as a page of its own, `<path>.html`, and a folder at
`<folder>/index.html`. A statement can gain or lose its declaration kind when it moves or at any later
revision, and the ledger does not record which route it had, so each old address of a statement keeps both.
From the ledger, the hook writes:

- on an old folder page that still exists, an element with the old anchor of each statement that left it,
  holding a plain link to where the statement went and shown only when the address names it, and a script
  that follows that link; an old anchor that an element of the page has now, such as a section heading, stays
  that element's, and the build log reports it;
- at the old address `<path>.html` of each statement that moved or was retired, a notice;
- of a retired statement that a statement replaces at its own address, only the route that statement does not have:
  the notice if it is boxed, the old anchor if it has a page of its own; no route redirects to itself, and an
  explorer link to the address needs no rewrite;
- at the page of a folder that is gone, a notice with a plain link to where the folder went (by its own rows,
  to the card that replaced it, or else to its nearest folder that exists) and an element for each old anchor
  of its statements, linking to where each went, and at its old explorer page
  `dependencies/scopes/<folder>.html` a notice like the ones render writes for live folders;
- `javascripts/atlas-card-moves.js`, a table of every old address and where it leads, which each folder page
  an old explorer link can reach loads first: a link `#node=<old address>` is rewritten to where the address
  leads before the explorer starts.

Notices are bare redirect pages, as `hooks/trim_pages.py` publishes render's own.
