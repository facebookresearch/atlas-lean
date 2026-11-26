# Counting symmetric words containing a fixed multiset

Let `n,m : ℕ` and `t : Multiset (Fin(n+1))` satisfy `t.card ≤ n`. Then the set of length-`m`
symmetric words containing `t` has cardinality `Fintype.card {s : Sym (Fin(n+1)) m // t ≤
s.val} = Nat.choose (n+m-t.card) n`. This includes the zero count when `m < t.card`.
