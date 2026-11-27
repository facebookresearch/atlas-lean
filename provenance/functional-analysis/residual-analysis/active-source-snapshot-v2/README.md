# Eight original Gaussian and parabolic-cylinder sources

This versioned snapshot contains only the eight original MathlibExt source files
installed by this slice. Each JSONL row preserves its exact UTF-8 `source_text`,
original author notices, byte count and SHA256. The manifest records the new
chunk position and the preceding position in the complete original archive.
Current production sources may differ through the explicitly recorded export
adaptations; this archive contains their unchanged original source versions.

Verify every original row and its manifest binding:

```sh
python3 verify_snapshot.py manifest.json
```

Restore the verified original files into a fresh directory:

```sh
python3 verify_snapshot.py manifest.json --output restored-source
```

The verifier uses only the Python standard library and rejects unsafe paths,
duplicate or missing rows, changed bytes and inconsistent chunk positions. The
preceding complete 56-source archive remains preserved in private publication
custody and in the destination records of the other source slices; it is not the
installed-source scope of this eight-file package.
