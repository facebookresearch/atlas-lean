# Kernel, spectral, and Hilbert tensor API source snapshots

The source/MathlibExt/ tree stores readable byte-exact original snapshots of the eight
MathlibExt files in this contribution. Each .lean.txt file is reference text, preserving
all original author notices and mathematical documentation.

The files.jsonl records identify each original library path and its source version by
SHA-256 and Git blob hash. Each row binds that source to its snapshot path and contributed
MathlibExt file hash. The source and documentation revisions are recorded as content
identifiers; the committed snapshot bytes provide the reproducible source within this
contribution.

The exports add the required Meta header and preserve every original source byte after
that header: imports, domains, norms, scalar actions, independent universes, zero/empty
cases, declarations and proofs. Adaptations use a uniform array schema.

The reusable scope covers GNS null kernels/submodules, rectangular Hilbert closed-graph
transforms, adjoint restrictions, continuous-functional-calculus spectral projections,
completed tensor Hilbert bases, and bounded measurable reciprocal cuts. The contribution
contains only MathlibExt production sources and their readable snapshots.
