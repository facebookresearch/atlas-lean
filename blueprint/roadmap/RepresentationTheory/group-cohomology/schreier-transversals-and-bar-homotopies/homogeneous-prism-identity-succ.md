# Alternating boundary identity for the homogeneous prism

Let `X,Y` be types, `M` an abelian group, `f,g : X → Y`, `n : ℕ`, and `c : (Fin (n + 2) → Y) →
M`. Define `K_n c(x) = ∑ i : Fin (n + 1), (-1)^i • c(vertices (f ∘ x) (g ∘ x) i)`, and let `d`
be the alternating sum over vertex deletions. For `x : Fin (n + 2) → X`, `(d K_n c)(x) +
(K_{n+1} d c)(x) = c(g ∘ x) - c(f ∘ x)`. The two sums have signs `(-1)^(j+i)` for deletion
followed by insertion and insertion followed by deletion.
