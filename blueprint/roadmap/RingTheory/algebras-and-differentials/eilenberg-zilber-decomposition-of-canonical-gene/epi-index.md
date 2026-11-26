# Generator-index map for a simplex epimorphism

Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and `P` its
polynomial-comonad resolution. For an epimorphism `e : [n] → [m]` and an index `x∈T^m A`,
`epiIndex k A e x` is `indexHom_n(P(e.op)(point_m x)) ∈ T^n A`. Here `point_m` includes a
polynomial generator and `indexHom_n` evaluates the outer polynomial layer.
