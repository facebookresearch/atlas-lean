# Eval To Simplicial map eq

Evaluation commutes with promotion on arbitrary morphisms: for any
`f : m ⟶ n` in `SimplexCategory`, the two routes agree.

Specialization of the generic `toSimplicialObject_mapObj_map` to the
evaluation functor; `mapObj ((evaluation A D).obj a) X` is definitionally
`(evalFunctor a).obj X`.
