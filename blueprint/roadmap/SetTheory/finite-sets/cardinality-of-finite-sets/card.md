# Cardinality of a finite set

Let $\alpha$ be a type. The cardinality $|s|$ of a finite set $s$ of elements of $\alpha$ (a term of `Finset α`) is
the number of its elements, a natural number. Mathlib defines it as the cardinality of the multiset underlying $s$,
whose elements are the elements of $s$, each taken once; it is written `s.card`, or `#s` with the scoped notation of
the `Finset` locale, available after `open scoped Finset`.
