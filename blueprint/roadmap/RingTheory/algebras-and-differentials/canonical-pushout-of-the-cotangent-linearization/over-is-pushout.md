# The pushed-out source is an algebra tensor pushout

For commutative `k`-algebras `K,A` and `P∈Over A`, the square with maps `k→K`, `k→P.left`,
`K→K ⊗_k P.left`, and `P.left→K ⊗_k P.left` is an algebra pushout. This is `Algebra.IsPushout
k K P.left ((overFunctor k K A).obj P).left`.
