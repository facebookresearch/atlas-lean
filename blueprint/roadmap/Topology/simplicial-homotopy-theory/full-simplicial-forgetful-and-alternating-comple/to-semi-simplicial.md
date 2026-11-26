# A simplicial homotopy restricts to a semisimplicial homotopy

Let H be a simplicial homotopy between f, g : X ⟶ Y in a category C. Precomposing X, Y, f and
g with SemiSimplexCategory.toSimplexCategory.op gives semisimplicial objects and maps. The
same maps H.h i : X_n ⟶ Y_(n+1) satisfy the semisimplicial endpoint and face conditions,
defining a homotopy between the restricted f and g.
