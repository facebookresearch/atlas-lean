# A degeneracy inserts one in its repeated-vertex edge

For a type A with an element 1, f : X ⟶ Y in the simplex category, i : Fin (X.len + 1) and a :
Fin Y.len → A, one has pullbackEdges (σ i ≫ f) a = Fin.insertNth i 1 (pullbackEdges f a). Thus
the repeated-vertex edge has label 1 and every other edge keeps the corresponding coordinate
for f.
