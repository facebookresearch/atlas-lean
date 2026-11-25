# Subcomplex Directed Sup

Finite simplicial sets factor through some stage of a directed supremum of
subcomplexes.

Given:

* `X : SSet`,
* a directed nonempty index preorder `J`,
* a monotone family `F : J → X.Subcomplex`,
* a finite simplicial set `A` and a map `f : A ⟶ ⨆ j, F j`,

there exist `j : J` and `g : A ⟶ F j` such that `g ≫ homOfLE (le_iSup F j) = f`.

The proof proceeds via the categorical colimit description of `⨆ F`,
preservation of filtered colimits by `Subcomplex.toSSetFunctor`, and finite
presentability of finite simplicial sets.

This is the pure-`SSet` provider required by the minimal-subfibration chain-closure
packet; it makes no fibration or minimality claim.
