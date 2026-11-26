# Group homomorphisms preserve finite prefix products

Let `G,H` be groups, `f : G →* H`, `n : ℕ`, `x : Fin n → G`, and `i : Fin (n + 1)`. Then `f
(Fin.partialProd x i) = Fin.partialProd (fun j => f (x j)) i`. Thus applying `f` to the
ordered product of the first `i` entries equals the ordered product of their images, including
the empty product at `i = 0`.
