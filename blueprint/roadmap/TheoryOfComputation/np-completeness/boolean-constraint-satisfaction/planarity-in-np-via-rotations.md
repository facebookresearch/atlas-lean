# Planarity of multigraphs is in NP via rotation systems

A **rotation system** of a finite multigraph (loops and parallel edges allowed) assigns to each vertex a cyclic order of its incident darts (half-edges); its faces are the orbits of the permutation 'reverse the dart, then take the next dart in the rotation at its head'. A connected multigraph with at least one edge, with $V$ vertices, $E$ edges and a rotation system with $F$ faces, is planar iff some rotation system satisfies Euler's formula $V-E+F=2$ (for $c$ components, none an isolated vertex, $V-E+F=2c$ with faces counted as dart orbits). Hence planarity is in $\mathsf{NP}$: a rotation system is a certificate of polynomial size whose faces are counted in polynomial time.

## Proof sketch

A planar embedding induces a rotation system with the embedding's faces, which satisfy Euler's formula; conversely a rotation system of genus zero can be realized by gluing polygons along the face boundaries into a sphere, giving a polygonal drawing.

## Depends on

- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- Michael R. Garey and David S. Johnson, "Computers and Intractability: A Guide to the Theory of NP-Completeness", W. H. Freeman, 1979.
- Bojan Mohar and Carsten Thomassen, "Graphs on Surfaces", Johns Hopkins University Press, 2001.
