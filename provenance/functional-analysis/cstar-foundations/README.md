# C-star and operator foundation source snapshots

The `source/MathlibExt/` tree contains byte-for-byte immutable snapshots of the
265 original MathlibExt source files. Each `.lean.txt` file stores the original
Lean text without alteration. It is reference material rather than an active
Lean module. The original copyright and author notices are retained.

The `files-*.jsonl` records give the original library path, original SHA-256,
Git blob identifier and snapshot path, together with the exported file hash
and an array of adaptation descriptions. The committed snapshot bytes make
every original hash resolvable within this contribution. Compare each snapshot
with its recorded exported MathlibExt path to inspect the exact statement,
proof, import and documentation differences.

The exports preserve mathematical hypotheses, domains, norms, universes, zero
and empty cases and attribution. Their records distinguish documentation and
header changes from the Lean 4.36 compatibility repairs. Native verification
is reported by the pull-request checks. Source-organized textbook and paper
modules are excluded.
