# π scoping provenance

[`finite-session-basic.lean.txt`](finite-session-basic.lean.txt) is the exact
original Meta finite-session source used for the adapted name-scoping
transport. It retains the original Meta copyright/license header. Its
SHA-256 is:

```text
eb82d1892e50921192fb8b02a9f9424ac531cbc62a055e3282a2cd13e15da432
```

[`manifest.json`](manifest.json) records the original repository, path and
development revision, declaration line ranges and span hashes, the unchanged
Basic substrate, and how each source result relates to the canonical π API.
The origin revision is an unpublished development identifier, not a required
fetchable commit. The checked-in snapshot provides the full reproducible
source without access to unpublished history.

The asset is plaintext provenance evidence, not a compiled Lean library. Its
original `NameScoped` and finite-session declarations do not add another
scoping API or session-typing implementation to this project. Canonical
scoping remains in `CSLibExt/Languages/PiCalculus/Scoping.lean`.

## Reproduce the source check

From the repository root, with the pinned Lean toolchain and dependency cache:

```bash
snapshot="docs/provenance/pi-scoping/finite-session-basic.lean.txt"
sha256sum "$snapshot"
tmp="$(mktemp /tmp/pi-source.XXXXXX.lean)"
python3 -c 'import shutil,sys; shutil.copyfile(*sys.argv[1:])' \
  "$snapshot" "$tmp"
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false "$tmp"
```

The copy preserves every byte and gives the compiler a temporary `.lean`
filename. The temporary file can be retained for inspection; it is not added
to any project library. The snapshot's imported π Basic source is unchanged
from its origin, as bound by the manifest's substrate hash.
