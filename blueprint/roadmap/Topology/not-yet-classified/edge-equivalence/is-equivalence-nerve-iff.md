# Is Equivalence nerve iff

Nerve gate: an edge in the nerve of a category is an equivalence
if and only if the corresponding morphism of the category, obtained
via `nerve.homEquiv`, is an isomorphism. Both directions are proved:
the forward direction maps along `nerveHoFunctorToCat`, and the
reverse direction uses the inverse morphism to build an
`Edge.InvStruct`.
