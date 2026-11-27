# Ho Pre nerve is Equivalence

A categorical equivalence tested against a nerve: precomposition
with a categorical equivalence induces an equivalence of homotopy
categories of functor objects into every nerve, since nerves are
quasicategories. This is the input to the proof of
TODO(T20-hoFunctor) recorded in the module header. The
`Category.{u}` restriction on `D` is forced here: testing
`categoricalEquivalences.{u} f` against `nerve D` requires
`nerve D : SSet.{u}`.
