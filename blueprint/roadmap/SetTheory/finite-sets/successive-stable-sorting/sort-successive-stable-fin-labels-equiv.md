# Flattening preserves the sorting product

Let `n,a,b : ℕ` and `z = (f,g) : (Fin n → Fin a) × (Fin n → Fin b)`. The flattened combined
labeling satisfies `Tuple.sort (successiveStableFinLabelsEquiv n a b z) = Tuple.sort f *
Tuple.sort g`, using `(p*q)(i) = p(q(i))`.
