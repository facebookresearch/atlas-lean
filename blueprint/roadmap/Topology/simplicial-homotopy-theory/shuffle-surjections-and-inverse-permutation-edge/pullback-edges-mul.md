# Complementary rank pullbacks reconstruct the permuted word

Let A be a type with multiplication and a two-sided unit, let s be an ordered (p, q)-shuffle
with permutation σ, and let a : Fin p → A and b : Fin q → A be words. For each i : Fin (p +
q), pullbackEdges s.leftHom a i * pullbackEdges s.rightHom b i = Fin.append a b (σ.symm i).
The factor from the block not occupying i is 1, so the multiplication order is left pullback
followed by right pullback.
