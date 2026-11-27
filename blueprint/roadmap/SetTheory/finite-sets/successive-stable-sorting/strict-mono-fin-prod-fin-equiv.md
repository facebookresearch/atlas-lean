# Finite-product flattening preserves order

For `a,b : ℕ`, the map `Fin a ×ₗ Fin b → Fin(a*b)` obtained from `finProdFinEquiv` is strictly
increasing for lexicographic order. Its value on `(i,j)` is the finite index with
natural-number value `b*i.val + j.val`.
