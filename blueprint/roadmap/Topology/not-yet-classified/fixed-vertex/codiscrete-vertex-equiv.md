# Codiscrete Vertex Equiv

The codiscrete simplicial set on a type `S` is the nerve of the
codiscrete (indiscrete) category on `S`, i.e.
`CategoryTheory.Codiscrete.functorToSSet.obj S` (see
`MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteNerve`). Its
`n`-simplices are identified with tuples `Fin (n + 1) → S` by
`CategoryTheory.Codiscrete.equivFun` (`equivFun c i = (c.obj i).as`),
and the vertex identification and terminal-map API below are
formulated through `equivFun`.
