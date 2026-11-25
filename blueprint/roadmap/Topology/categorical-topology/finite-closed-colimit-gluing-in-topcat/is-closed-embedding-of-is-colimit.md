# Is Closed Embedding of is Colimit

Generic finite closed-colimit descent: a map out of a finite
`TopCat` colimit whose composites with the colimit legs are closed
embeddings is itself a closed embedding once it is globally injective.
The proof splits as the inducing part (`isInducing_of_isColimit` via the
sup-coinduced topology) and the closed-range part
(`isClosed_range_of_isColimit` via the finite union of composite ranges).
This is the smallest reusable current-Mathlib lemma that closes the
boundary worker's genuine API gap without specializing to simplicial
boundaries; `Boundary.lean` is untouched in this worker.
