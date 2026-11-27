# Eval Order Hom

Evaluated order-preserving map of a face chain in `SimplexCategory`.

For `c : DeltaChain n m`, this is `(toSimplexCategory.map c.eval).toOrderHom`,
viewed as an order-homomorphism `Fin (n+1) →o Fin (m+1)`.
