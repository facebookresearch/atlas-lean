# Source-text dependencies for the v1 wiki

`blueprint/sources/v1/book-dependencies/<Book>.json` records which earlier
statements each ATLAS v1 target uses, read from the book's own text rather
than from the Lean code. `scripts/generate_wiki.py` draws them as roadmap
edges alongside the Lean dependency closure. Every edge carries the source
file, line, and a verbatim quote that shows the use.

## Pipeline

Pick a work directory outside the repository (`WORK` below). Source documents
are downloaded there and never committed.

1. Fetch the source into `WORK/sources/<Book>/raw/` (see the table below;
   `fetch_ocw_lectures.py WORK` handles the per-lecture courses) and convert
   PDFs with `pdf_to_text.py WORK/sources/<Book>/text WORK/sources/<Book>/raw/*.pdf`
   (needs `pypdf`; run it with `python -I`, since the inputs are untrusted).
2. `write_targets.py WORK <Book>` writes the target list from `v1/Atlas/<Book>/report.json`.
3. An extraction agent follows [`EXTRACT.md`](EXTRACT.md) and writes
   `WORK/book-deps/<Book>.proposed.json`. Books above about 200 targets were
   split by idx range into `<Book>.partN.proposed.json`.
4. An independent verification agent follows [`VERIFY.md`](VERIFY.md) and
   writes the matching `.verified.json`, one verdict per proposed edge plus a
   recall sample.
5. `merge_book_dependencies.py WORK <Book>` keeps confirmed edges (reclassified
   ones under their corrected kind), drops rejected ones, and writes the vault
   file.

The 2026-10 run proposed 8,598 edges, rejected 71, and kept 7,961. Recall
samples put recall at roughly 63-95% per book, most often around 80%; the
misses are mostly proofs that write out a definition or use a result without
naming it.

## Sources

| Book | Source text |
| --- | --- |
| AlgebraNotes | OCW RES.18-011 `mit18_701f21_full_lec_new.pdf` and RES.18-012 `mit18_702s22_full_lec.pdf` (targets 82 and 84-175 are 18.702) |
| AlgebraicCombinatorics | OCW 18.318 topic notes: notes2, boolean, hadamard, sperner, young |
| AlgebraicGeometryI | OCW 18.725 `MIT18_725F15_notes.pdf` |
| AlgebraicTopologyI | OCW 18.905 `MIT18_905F16_lecture_notes.pdf` |
| AnAlgorithmistsToolkit | OCW 18.409 scribe notes 1-25 and Spielman's notes for lectures 2, 4, 7 |
| ArithmeticGeometry | OCW 18.782 lecture notes (no lecture 6 on OCW) |
| BooleanFunctions | OCW 18.218 lecture notes |
| Buildings | Paul Garrett, *Buildings and Classical Groups*, <https://www-users.cse.umn.edu/~garrett/m/buildings/book.pdf> |
| CombinatorialOptimization | OCW 18.433 lecture notes (11 of 13 PDFs extract as TeX glyph codes) |
| ComplexVariables | OCW 18.112 "Remarks on Lecture N"; they supplement Ahlfors, which is not available, so 8 targets are unlocated |
| DifferentialAnalysis | OCW 18.155 `lecture_notes.pdf` |
| DifferentialGeometry | OCW 18.950 chapter notes ch1-ch4 |
| EllipticCurves | OCW 18.783 lecture notes |
| FourierAnalysis | OCW 18.103 topic notes |
| GeometryOfManifolds | OCW 18.966 lecture notes |
| HighDimensionalStatistics | OCW 18.S997 `MIT18_S997S15_CourseNotes.pdf` |
| IntroductionToFunctionalAnalysis | OCW 18.102 `MIT18_102s21_full_lec.pdf` |
| IntroductionToPartialDifferentialEquations | OCW 18.152 notes for class meetings 1-12, 15, 24 only; 42 targets are unlocated |
| LieGroups | OCW 18.757 `mit18_757_f23_lec_full.pdf` |
| NumberTheoryI | OCW 18.785 `mit18_785f21_full_lec.pdf` plus `mit18_785f21_lec17.pdf` (the combined PDF repeats lecture 16 and omits 17) |
| ProbabilisticMethodsInCombinatorics | OCW 18.226 `mit18_226_f22_lec_full.pdf` |
| ProjectionTheory | OCW 18.156 `mit18_156_s25_lec_full.tex` |
| RealAnalysis | OCW 18.100A LaTeX source `mit18_100af20_notes_tex2.zip` |
| TensorCategories | OCW 18.769 `MIT18_769S09_notes.pdf` |
| TheoryOfComputation | OCW 18.404J lecture slides (no lecture 1, 13 or 26 on OCW) |
| TheoryOfProbability | OCW 18.175 lecture notes 1-39 (no lecture 19; 21, 22, 24 unposted) |
