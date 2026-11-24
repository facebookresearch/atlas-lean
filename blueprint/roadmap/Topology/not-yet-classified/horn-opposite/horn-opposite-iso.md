# Horn Opposite Iso

The opposite of the `i`-th horn is the `i.rev`-th horn. The
subcomplex-level equation is Mathlib's `SSet.op_horn`; the opposite
subcomplex coerced to `SSet` is definitionally the opposite of the
coerced subcomplex, so only the preimage-along-iso step is new.
