# Lean and Mathlib bumps

ATLAS pins Lean, Mathlib, CSLib and Physlib to one final release, `vX.Y.Z`,
that all four have tagged. This page is the routine for moving to the next one
while main takes 100 to 300 pull requests a day through the merge queue.

## What makes a bump hard

A bump touches many files, so main keeps conflicting with it, and new code on
main keeps failing on the new toolchain. Its CI also starts from nothing.
Measured on #6018 (v4.36.0) on 22 November 2026:

- At its head `ad8f8942` it changed 623 Lean files and 342 rows of
  `provenance/formal-math-sync.json`. From its base (00:20 UTC) to its sixth
  merge of main (main as of 16:00 UTC), 202 commits landed on main, 201 of
  them merged pull requests.
- Each of its first eight merges of main conflicted in the manifest, and four
  also in Lean files: docstring campaigns edit the same files and rows as the
  bump. After each of its first five merges, the next conflicting commit
  landed 5, 26, 6, 6 and 7 minutes after the newest main commit the merge had
  brought in.
- 7 of those 202 commits (3.5%) failed on the new toolchain, each fixed in one
  to four lines.
- No cached build matches the new pins, because `ci.yml` keys its cache on
  `lean-toolchain` and `lake-manifest.json`. Its only complete CI build job
  took 316 minutes against a 360-minute limit, and each new push cancelled the
  run in progress.

The merge queue solves the last-minute race: once the bump is at the front of
the queue, nothing can merge ahead of it, and every pull request behind it is
tested on top of it. The routine below makes the bump small, keeps it close to
main, and gives the queue a warm build.

## When

Lean has released about monthly (v4.34.0 on 14 September 2026, v4.35.0 on 12
October, v4.36.0 on 16 November), with the next release candidate a day or two
later. Mathlib and CSLib tagged those releases within a day of Lean, and
Physlib three to eleven days later; Physlib tagged no release candidate for
them. `guard` accepts only a forward move to a final release that every pinned
dependency has tagged, so the bump can land once the last of them, usually
Physlib, has tagged it.

## Who

Each release has one bump owner: a maintainer, or an agent working for one, on
a machine that keeps a warm build of the bump branch. A cold build of every
library takes about 45 minutes on 48 cores, and an incremental one after a
merge of main a few minutes. A maintainer decides when to queue the bump.

## Steps

1. **Start on the release candidate.** When Lean, Mathlib and CSLib have tagged
   `vX.Y.0-rc1`, build ATLAS on them in a preview branch that is never merged,
   and fix what fails. If Physlib has no matching tag yet, leave it at the
   current release and skip `PhyslibExt` until it has one. Upstream API changes
   mostly arrive with the first candidate.

2. **Land fixes that build on both toolchains.** Many fixes also build on the
   current toolchain: explicit arguments, fully qualified names, type
   ascriptions on binders, `noncomputable`. Of the 622 library files #6018
   changed, 373 (60%) built on v4.35.0 with their changes, and they hold 190 of
   its 342 manifest rows. Send such fixes to main as ordinary pull requests,
   through the queue like any other. Each one that merges is a file the bump no
   longer touches, so main conflicts with the bump less often.

3. **Open the bump** when every pinned dependency has tagged `vX.Y.Z`. Commit
   the output of `python3 scripts/bump/pinned_bump.py prepare vX.Y.Z` unchanged,
   so that `guard` accepts it. Put the remaining fixes in separate commits after
   it.

   If the bump changes `lean-toolchain` and agitate has a commit for the new
   toolchain, point `AGITATE_COMMIT` in `.github/workflows/linters.yml` at it in
   one of those later commits; until then the advisory `mathlib linters` job
   warns and skips its unused-imports check.

4. **Keep it close to main.** Merge main in, never rebase, so the first commit
   stays exactly what `pinned_bump.py` produced:

   ```sh
   git fetch origin main
   python3 scripts/bump/bump_branch.py status                 # how far behind, what conflicts
   python3 scripts/bump/bump_branch.py merge-main --adjacent  # merge, resolve, commit
   ```

   `merge-main` resolves the manifest row by row. A row that only one side
   changed takes that side's row. For a row both sides changed it looks at the
   merged file: if it is git's own merge of the two sides (or `--adjacent`'s),
   even one that comes out equal to one side, the row takes the new hash and
   both rationales: a side that rewrote the rationale keeps its account and the
   other side's added sentences follow. If both rewrote it, or both wrote a first
   one and the edits are not provably on different lines, you write one.
   If you resolved a conflict by keeping one side's version, it keeps that
   side's row, unless the other side corrected the rationale: then you write
   one. With `--adjacent` it also merges a conflict where one side
   rewrote one whole doc comment and the other changed the one line next to it
   (a non-blank line with no `/-` or `-/`), which is how docstring campaigns on
   main usually meet the bump's edits. Before committing it checks the manifest
   against main on the exact tree it would commit. It only ever replaces a file
   that is exactly as its own `git merge` left it (or its own unedited draft of
   the manifest): once you edit a file, `git add` it when it is resolved.

   For a domain-sharded ledger, stage the affected JSON shards as well as the
   resolved Lean files. Do not start an automatic bump merge across the one-time
   layout cutover. For a manual merge, keep the sharded layout and both parents'
   records, then stage the result and validate it without committing:

   ```sh
   python3 scripts/bump/bump_branch.py resolve-manifest --check-only
   ```

   The check rejects lost records from either parent before running preflight
   provenance validation against main. A v2 checkout must not restore inline rows.

   Other conflicts are yours:

   1. Resolve each conflicted file and `git add` it.
   2. Run `bump_branch.py resolve-manifest`. If it lists rows to finish (a file
      you resolved by hand needs its own rationale), record each with
      `python3 scripts/check_formal_math_sync.py --record-divergence PATH
      --rationale TEXT --backport pending`, `git add` the manifest, and run
      `resolve-manifest` again.

   Then re-run any fixer the bump needs, such as a rename script: files main
   adds or edits can bring back the old names, and a conflict resolved in
   favour of main can undo the bump's edit on that line. Then build: what fails
   is mostly new code from main, and `bump_branch.py breakage <build log>`
   lists, for each failing module, the main pull requests that changed it: the
   candidates. Fix, commit, push.

5. **Warm CI early, and keep it warm.** Dispatch `bump-cache.yml` from main
   with the pull request number and the head you reviewed:

   ```sh
   gh workflow run bump-cache.yml --repo facebookresearch/atlas-lean --ref main \
     -f pull-request=<number> -f head-sha=<full head SHA>
   ```

   It runs main's bump guard on that head first, then builds and checks it as
   CI does, and saves the build where the bump's own CI runs, its merge group
   and the groups behind it find it. Every head of the bump has the same pins,
   so a later dispatch, and the bump's own CI, start from the newest saved
   build and rebuild only what changed since.

   It runs on a 64-core runner, which GitHub bills at about $0.16 a minute:
   about $8 for a cold build. The bump's own pull request CI stays on the
   standard runner: a run of it whose "Restore local build" step found no build
   on the new pins is a cold build of several hours, so re-run it once the
   warm-up reports `Saved`.

   - Dispatch first as soon as the bump's head passes the guard. That run is a
     cold build, about 50 minutes, and nobody needs to wait for it. A run that
     runs out of time saves a checkpoint, which only a dispatch for the same
     SHA can resume, and only while that SHA is still the pull request's head.
     So leave the branch alone until the first run finishes; a dispatch for a
     newer head starts from the newest complete build on the new pins, or from
     scratch if there is none yet.
   - Dispatch again after merging main into the bump. Starting from the last
     saved build, it rebuilds only what came in since, and it keeps a recent
     build in the cache: GitHub evicts the least recently used entries first.
     On 22 November main saved a new entry every 30 to 60 minutes and about
     five fitted; if main saves one on every push, as #6159 proposes, an entry
     nobody uses may last only tens of minutes.
   - Dispatch last for the head you will queue. Queue it (step 6) once that run
     reports `Saved` (or `Already warm`, if that exact head was warmed before)
     and the required checks are green. If a merge group still builds from
     scratch, its "Restore local build" step shows which key it restored, if
     any; an evicted entry is one explanation. A new dispatch helps the next
     run, not one already building.

6. **Queue it at the front of the queue.** Queue it right after a merge of main
   whose required checks passed, at a quiet hour: 11:00 to 13:00 UTC merges
   about 4 to 7 pull requests an hour, 00:00 to 09:00 UTC 13 to 18. Queue it
   with `jump`, pinned to the head you checked:

   ```sh
   gh api graphql -f query='
     mutation($id: ID!, $head: GitObjectID!) {
       enqueuePullRequest(input: {pullRequestId: $id, expectedHeadOid: $head, jump: true}) {
         mergeQueueEntry { position }
       }
     }' -f id="$(gh pr view <number> --json id --jq .id)" -f head=<full head SHA>
   ```

   The bump's merge group is then main plus the bump, and every group already
   building is rebuilt on top of it. Jumping restarts those builds, so do it
   about once a month, not more. It needs the "Jump to the front of the queue"
   permission. Without it, queue the bump normally once the queue is short. If
   main conflicts with the bump before its checks pass, go back to step 4.

7. **After it merges.** Dispatch Blueprint Pages on main once:

   ```sh
   gh workflow run blueprint-pages.yml --repo facebookresearch/atlas-lean --ref main
   ```

   Pull request runs of Blueprint Pages never save the Mathlib graph; a run on
   main does, and later pull request runs restore what it saved. The cache key
   includes the pins, so after a bump every Blueprint Pages run builds the
   graph again until a run on main has saved it. Without a dispatch, that is
   the daily build at 03:17 UTC. Like the daily build, a dispatched run on main
   also publishes the site when Pages publishing is enabled.

   The queue removes any pull request whose merge group fails on the new
   toolchain, and its timeline says why. Its author merges main, fixes it, and
   queues it again. Post the common fixes on the bump pull request so they are
   easy to find.

   A pull request whose CI ran before the bump merged has not been tested on the
   new toolchain. Merge main into it and wait for CI and Codex before you queue
   it again. Preflight reports such a head as stale; run main's copy of it from
   a clean checkout of main, as the
   [atlas-merge-queue](../.agents/skills/atlas-merge-queue/SKILL.md) skill
   shows, never the copy on the pull request's branch. Don't queue stale heads
   in bulk. Each one that fails makes every merge group behind it fail and
   rebuild until the queue removes it.

## Contributors and agents

A bump forces a new build on every machine. Start it before the bump merges:
while the bump is in the queue, build its head in a separate worktree. Once it
has merged, merge main into your branch and copy that build's `.lake` into your
worktree (`cp -a --reflink=auto`), so only what changed since gets rebuilt. A
pull request that was queued behind the bump and fails is removed from the
queue, not merged. Watch for that and fix it as in step 7. While the bump is
queued, `scripts/queue/preflight.py` reports any other pull request whose CI
has not run on the new pins as not ready. Once the bump has merged, merge main
into your branch, wait for CI and Codex, and queue it then.
