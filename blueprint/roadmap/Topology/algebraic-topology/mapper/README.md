# Mapper

Mapper (G. Singh, F. Mémoli and G. Carlsson, 2007) produces a simplicial complex summarising a
data set instead of embedding it: choose a filter function $f \colon X \to Z$ to a reference space,
cover $Z$, cluster each preimage of a cover element, and take the nerve of the resulting covering
of $X$ (G. Carlsson, *Topology and data*, Bull. AMS 46 (2009), §3.2). When the reference space is
$\mathbb{R}$ it is closely related to the Reeb graph of the filter (Carlsson, §3.2, Remark), and maps of coverings give
simplicial maps between Mapper complexes, a multiresolution picture of the data. Here the
clustering is single linkage.

- [Single-linkage clusters of a subset](sl-clusters.md)
- [Clusters of a subset are disjoint or equal](eq-of-mem-sl-clusters.md)
- [The clusters of a subset cover it](exists-mem-sl-clusters.md)
- [Mapper complex](mapper.md)
- [Dimension of the Mapper complex](mapper-card-le.md)

## Related topics

- [Simplicial complexes from point clouds](../simplicial-complexes-from-point-clouds/README.md):
  the nerve construction that Mapper applies to a covering by clusters.
- [Single-linkage hierarchical clustering](../../../ComputerScience/machine-learning/unsupervised-learning/single-linkage-hierarchical-clustering/README.md):
  the clustering used on each preimage.
