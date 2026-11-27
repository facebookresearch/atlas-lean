# Removing a required submultiset

For a type `α`, a multiset `t : Multiset α`, and `k : ℕ`, there is an equivalence `{s : Sym α
(k+t.card) // t ≤ s.val} ≃ Sym α k`. It sends `s` to the multiset difference `s.val - t`, and
its inverse sends `u` to `u.val + t`.
