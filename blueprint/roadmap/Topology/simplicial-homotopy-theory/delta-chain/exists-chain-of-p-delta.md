# Exists chain of P delta

Source-general existence: a `P_δ` morphism from an arbitrary source
that is known to be `mk n` is represented by a `DeltaChain n m` up to
outer `eqToHom` transports. The proof is by direct induction on the
`multiplicativeClosure` witness for `P_δ`, using `snoc` for the face
step and keeping all transports at the boundary.
