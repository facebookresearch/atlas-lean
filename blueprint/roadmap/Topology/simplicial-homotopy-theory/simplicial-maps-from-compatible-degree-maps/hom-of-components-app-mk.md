# The constructed simplicial morphism has the prescribed components

Let X and Y be simplicial objects in a category C. Suppose f_n : X_n ⟶ Y_n satisfies f_(n+1) ≫
δ_i^Y = δ_i^X ≫ f_n for i : Fin (n + 2), and f_n ≫ σ_i^Y = σ_i^X ≫ f_(n+1) for i : Fin (n +
1). For every n : ℕ, the component of homOfComponents f hδ hσ at op (SimplexCategory.mk n) is
f_n.
