# Sorting identifies symmetric words with monotone tuples

For a linearly ordered type `α` and `n : ℕ`, `sortedTupleEquiv n : Sym α n ≃ {f : Fin n → α //
Monotone f}` sends a multiset to its ascending sorted entries. Its inverse sends a monotone
tuple `f` to the multiset of `List.ofFn f`.
