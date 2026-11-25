# Left Derived Coinvariants Trivial Iso

The canonical object-level comparison from left-derived coinvariants of
the trivial representation to native group homology.

Both calculations use `Rep.barResolution k G`; the middle isomorphism is the
degreewise tensor-unit comparison `coinvariantsTensorTrivialIso`. Mathlib's bar
resolution currently requires the coefficient ring and group in the same
universe, which is the only reason for the shared universe in this signature.
