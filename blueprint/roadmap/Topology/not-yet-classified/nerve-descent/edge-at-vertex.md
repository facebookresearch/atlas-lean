# Edge At Vertex

The edge in a nerve obtained by evaluating an edge `e` of the
simplicial functor object `Fun(Z, nerve D)` at a vertex `z` of `Z`:
precompose `e` with the constant map at `z` and evaluate at `Δ[0]`. Its
morphism in `D` under `CategoryTheory.nerve.homEquiv` is the
`z`-component of the natural transformation classified by `e`.
