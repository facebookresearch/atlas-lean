# Immutable MathlibExt source snapshot

The JSONL chunks contain the exact pre-adaptation UTF-8 Lean source for this
batch. Every row records its source-relative path, original byte count and
SHA256, followed by readable `source_text`. Original authorship and per-file
notices remain in that text. The manifest binds each file to its chunk and
one-based line number.

Verify the archive:

```sh
python3 verify_snapshot.py manifest.json
```

Rehydrate its original source tree and verify every file:

```sh
python3 verify_snapshot.py manifest.json --output restored-source
```

The verifier uses only the Python standard library. It checks chunk hashes,
row counts, unique source paths, exact original hashes and bytes, and manifest
line bindings. Standard JSON string escaping preserves line endings and
Unicode; no compression or base64 encoding is used. Production-file changes
are described in the adjoining batch provenance, separately from these
unchanged archive bytes.
