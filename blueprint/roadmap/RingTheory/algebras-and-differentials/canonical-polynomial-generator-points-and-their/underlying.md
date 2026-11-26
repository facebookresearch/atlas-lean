# Underlying simplicial set of the polynomial resolution

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The simplicial set
`underlying k A` is the entire polynomial-resolution simplicial algebra followed by `forget
(CommAlgCat k)`. In degree `n` it has all elements of `T^{n+1}A`, and its faces include the
outer polynomial evaluation map.
