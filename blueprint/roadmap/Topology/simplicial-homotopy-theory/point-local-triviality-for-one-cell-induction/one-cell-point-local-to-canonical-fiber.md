# Triviality of a further pullback over a subspace

In `TopCat.{u}`, let `p : E ⟶ X₄`, `U : Set X₄`, and let `h_over` trivialize a pullback
presentation of `p` over `U` with fixed fiber `F`. Assume the canonical pullback `Q = pullback
p (subspaceIncl U)` exists, with projection `Q ⟶ TopCat.of U`. For objects `P, B'`, maps `s :
P ⟶ Q`, `q : P ⟶ B'`, and `f : B' ⟶ TopCat.of U`, suppose their square with that projection is
a pullback. The induced datum `TrivialBundleWithFiber F q` exhibits `P`, with projections to
`B'` and `F`, as their product.
