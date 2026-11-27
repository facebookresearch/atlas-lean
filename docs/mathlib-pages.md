# Mathlib pages

The full site, which the workflow keeps as the `blueprint-site-full` artifact
for hosting outside GitHub Pages, has a page for every Mathlib module of the
graph's Mathlib layer ([`mathlib-layer.md`](mathlib-layer.md)), grouped by the
topics of `scripts/taxonomy.json`, and links the ATLAS statements to the
Mathlib declarations they use. `scripts/build_mathlib_pages.py` writes it from
the built site and the layer's `mathlib-graph` artifact of the same revision.
Like the layer, these pages are build outputs and are never committed: they
are about 1 GB of generated HTML. GitHub Pages, which publishes sites of up to
1 GB, gets the full site with its pages and the project map's data stored
gzipped ([BLUEPRINT.md](BLUEPRINT.md#the-github-pages-copy)).

## What a page shows

Each declaration of a module gets one block, in source order: its kind, its
name, a link to its source line at the pinned Mathlib revision, its signature,
its docstring, the declarations its statement uses and those its proof uses,
the declarations that use it, the ATLAS articles that use it (the layer's
bridge edges), and the ATLAS article that restates it, if one credits it with
`mathlib: true`. Uses are the layer's edges. As a display choice, used
instances are listed by name without links, after the other uses; instances
are nodes like any other and have their own blocks. The declarations and
articles that use a declaration are counted by whether they use it in their
statement or only in their proof, and up to 20 of each list are shown. A
declaration that a build has no page for is still named, and its name links to
its pinned source line.

Docstrings are rendered as Markdown with code blocks and the site's formulas,
without raw HTML, and keep only `http`, `https` and `mailto` links; a name in
code that is a declaration with a page links to it.

Pages, by site path:

| Path | Page |
|---|---|
| `mathlib/index.html` | the Mathlib pages' home: subjects with their counts |
| `mathlib/<Subject>/[<field>/[<subfield>/]]index.html` | a subject, field or subfield of the taxonomy |
| `mathlib/<Subject>/<field>/[<subfield>/]<topic>/index.html` | a topic with several modules |
| `mathlib/<Module>.html` | a module, named without its `Mathlib.` prefix (`mathlib/Topology.Basic.html`) |
| `mathlib/outside/index.html` | the modules that `mathlib_exclusions` keeps out of the taxonomy |

A topic with one module has no page of its own: the module's page carries the
topic's title. A topic or folder that also has an ATLAS folder page links to
it. A declaration's anchor is its exact name (`#Finset.sum_comm`),
percent-encoded in links; every other `id` on these pages starts with `_`,
which no declaration's name does.

One page per module keeps a declaration's address independent of the taxonomy
and the number of files within hosting limits. Measured on the layer of
21 November 2026 (306,596 declarations): a page per declaration would need
306,596 files and about 3.4 GB of page chrome alone; a page per topic gives
4,105 pages and 1.45 GB of content, because every link carries a longer page
name; a page per module gives 7,970 module pages and 10,292 pages in all,
1.07 GB.

## Linking to a Mathlib declaration

A Mathlib declaration is identified by the pinned Mathlib revision and its
exact name: the `name` of a row of the layer's `nodes.jsonl.gz`. Data that
names one stores the name in a field named `mathlib` and the revision in
`mathlib_rev`; there is no other identifier, and no URL is stored.

Article prose links to a declaration's source line at the pinned revision, with
its exact name as the link's title:

```markdown
[double sums](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean#L120 "Finset.sum_comm")
```

`python scripts/mathlib_link.py GRAPH NAME...` prints such links from the
`mathlib-graph` artifact and refuses a name that is not a node. The address
works on every site, with or without Mathlib pages. Do not link with a custom
`mathlib:` scheme, which Autoform refuses to publish, or with the Mathlib
documentation's lookup address, which fails for declarations renamed upstream
since the pin.

## What the build changes in the ATLAS pages

- A link whose title is a declaration and whose address is written exactly as
  that declaration's source line at the pinned revision points to its Mathlib
  page. One that disagrees with its title is reported and left as written;
  `--strict-links`, as a pull request's build runs it, fails the build on it.
  A pull request builds the site when it changes the wiki, among others
  ([GitHub Actions and publication](BLUEPRINT.md#github-actions-and-publication)).
- The links that Autoform's Lean code blocks make to Mathlib's documentation
  point to the Mathlib page when they name a declaration that has one, and stay
  as written otherwise. Links to the documentation elsewhere are left alone.
- A statement box whose article credits a Mathlib declaration (status
  `mathlib`) links the credited name to its page; a credited name that is not a
  node is reported.
- A statement box lists the Mathlib declarations its Lean statement and proof
  use, up to 40 of each with their count, instances aside, in its dependency
  details.
- The home page links to the Mathlib pages, and the search index gets one entry
  per Mathlib page.

Everything about ATLAS that the build shows comes from the built site itself.
An article counts only where the site publishes it: its catalog entry
(`dependencies/index.json`) must lead to a page that has exactly one statement
box with the article's id whose heading carries the entry's anchor, or, for an
article that is its own page, to that page. Its title, address and Lean names
come from that entry; nothing is read from the blueprint sources, so an article
the site does not publish is never named, credited or counted.

`check` restores each changed ATLAS page from the built one, by removing what
the build added and putting back the links it changed, and requires the
original bytes. Every link of the Mathlib pages and every link the build added
or changed must lead to an existing file and anchor, and a link named after a
declaration to that declaration's anchor; every new search entry must name a
page.

## Building

After the site and the layer are built:

```sh
python -m unittest scripts.test_build_mathlib_pages
python scripts/build_mathlib_pages.py build site mathlib-graph site-full
python scripts/build_mathlib_pages.py check site mathlib-graph site-full
```

`build` needs the site's MkDocs environment, since MkDocs renders each page's
chrome with the site's theme, and refuses a layer of another ATLAS revision
than the site's. The workflow's `build the Mathlib pages` job runs the tests,
builds and checks the full site, keeping `main`'s for three days as the
`blueprint-site-full` artifact, then packs and checks the GitHub Pages copy
([BLUEPRINT.md](BLUEPRINT.md#the-github-pages-copy)) and uploads it as a second
Pages artifact, `github-pages-full`, once `scripts/pages_size.sh` has measured
it as the upload packs it: at most 950 MB. Deployment publishes the wiki job's
site, packed the same way, as soon as it is built; then, if the Mathlib pages
job succeeded, the `publish the full site` job publishes the packed full site
in its place. The two come from the same run, and each publishes only over a
site of the run's commit or of one of its ancestors, failing otherwise, so a
later run's site is never replaced by an earlier one's. Runs of the workflow
from before that check have no such guard: do not re-run their deployment. A
failed, cancelled or timed-out Mathlib pages job leaves the wiki job's site
published.
