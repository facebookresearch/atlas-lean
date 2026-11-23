# Simplicial complexes from point clouds

Topological data analysis treats a data set as a finite metric space and builds from it, at every
scale $\varepsilon$, a simplicial complex whose homology can be computed by linear algebra (G. Carlsson,
*Topology and data*, Bull. AMS 46 (2009), §2.1–2.2). The basic construction is the nerve of a
covering; the Čech complex is the nerve of the covering by $\varepsilon$-balls, and the Vietoris–Rips
complex is the cheaper complex determined by its edges alone. The two are interleaved,
$\check{C}(X, \varepsilon) \subseteq VR(X, 2\varepsilon) \subseteq \check{C}(X, 2\varepsilon)$, and both grow with $\varepsilon$, so they form filtrations: the
$\mathbb{R}$-persistence simplicial complexes whose homology is studied in
[persistence modules and barcodes](../persistence-modules-and-barcodes/README.md).

The nerve theorem (Carlsson, Thm. 2.3: a numerable open covering whose nonempty finite
intersections are contractible has nerve homotopy equivalent to the space) relates these
complexes to the space they are built from; its statement involves the geometric realization of
an abstract simplicial complex.

- [Nerve of a family of sets](nerve.md)
- [Čech complex](cech-complex.md)
- [Vietoris–Rips complex](rips-complex.md)
- [The $\varepsilon$-neighbourhood graph](rips-graph.md)
- [The Vietoris–Rips complex is the clique complex of its one-skeleton](mem-rips-complex-iff-is-clique.md)
- [The Čech complex is a filtration](cech-complex-mono.md)
- [The Vietoris–Rips complex is a filtration](rips-complex-mono.md)
- [Čech inside Rips at twice the scale](cech-complex-le-rips-complex-two-mul.md)
- [Rips inside Čech at the same scale](rips-complex-le-cech-complex.md)
- [The Rips–Čech interleaving](cech-complex-le-rips-complex-le-cech-com.md)

## Related topics

- [Persistence modules and barcodes](../persistence-modules-and-barcodes/README.md): the homology
  of these filtrations is a persistence module, summarised by its barcode.
- [Single-linkage hierarchical clustering](../../../ComputerScience/machine-learning/unsupervised-learning/single-linkage-hierarchical-clustering/README.md):
  the connected components of the Vietoris–Rips complex at scale $\varepsilon$ are the single-linkage
  clusters, the zero-dimensional shadow of these complexes.
- [Mapper](../mapper/README.md): another nerve construction on data, built from a filter function
  and a clustering.
