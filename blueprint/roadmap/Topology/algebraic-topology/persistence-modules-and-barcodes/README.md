# Persistence modules and barcodes

A persistence module is a functor from an ordered set, viewed as a category, to vector spaces:
applying homology to a filtration of simplicial complexes gives one (G. Carlsson, *Topology and
data*, Bull. AMS 46 (2009), Def. 2.9 and §2.3). The building blocks are the interval modules
$k_I$, and the structure theorems say that, under finiteness hypotheses, every persistence
module is a direct sum of interval modules in an essentially unique way; the multiset of
intervals is the barcode (Carlsson, Prop. 2.12, for tame $\mathbb{N}$-modules via graded modules over
$k[t]$; W. Crawley-Boevey, J. Algebra Appl. 14 (2015), Thm. 1.1, for pointwise
finite-dimensional modules over $\mathbb{R}$). Distances make barcodes usable on noisy data: for q-tame
modules (for instance pointwise finite-dimensional ones) the interleaving distance between
modules and the bottleneck distance between their barcodes coincide (the isometry theorem, F. Chazal, V. de Silva, M. Glisse and S. Oudot, *The structure and
stability of persistence modules*, arXiv:1207.3674, Thm. 4.11), so small perturbations of the
data move the barcode by small amounts.

The pages below give the definitions, the symmetry of interleavings and of matchings, the
triangle inequality for interleavings and the stability of zero-dimensional persistence
(single-linkage clusters) under perturbation of the dissimilarity, together with the
decomposition, uniqueness and stability theorems.

- [Interval module](interval-module.md)
- [Structure maps of an interval module](interval-module-map.md)
- [Crawley-Boevey's decomposition theorem](exists-iso-sigma-interval-module.md)
- [Barcodes of tame $\mathbb{N}$-persistence modules (Zomorodian–Carlsson)](exists-iso-sigma-interval-module-nat-of.md)
- [The barcode is unique (Krull–Remak–Schmidt–Azumaya)](interval-module-decomposition-unique.md)
- [$\delta$-interleaving](interleaving.md)
- [Every functor is $\delta$-interleaved with itself for every $\delta \ge 0$](interleaving-refl.md)
- [Interleaving is symmetric](interleaving-symm.md)
- [Triangle inequality for interleavings](interleaving-trans.md)
- [$\delta$-matching of barcodes](is-matching.md)
- [Matchings are symmetric](is-matching-symm.md)
- [Hausdorff distance between closed intervals](hausdorff-edist-icc-icc.md)
- [Algebraic stability theorem](is-matching-of-interleaving.md)
- [Converse stability for decomposable modules](interleaving-of-is-matching.md)
- [The cluster functor (zero-dimensional persistence)](cluster-functor.md)
- [Stability of zero-dimensional persistence](cluster-functor-interleaving.md)

## Finite graded barcodes

- [Persistence barcode](barcode.md)
- [Rank function of a barcode](barcode-rank.md)
- [Distance between extended death values](with-top-dist.md)
- [Distance of a persistence bar to the diagonal](dist-to-diagonal.md)
- [Distance between two persistence bars](dist.md)
- [Partial matching of barcodes](matching.md)
- [The empty matching](empty.md)
- [Bottleneck cost of a matching](cost.md)
- [Bottleneck distance between barcodes](bottleneck-dist.md)
- [Wasserstein distance between barcodes](wasserstein-dist.md)
- [Erosion distance between barcodes](erosion-dist.md)
- [Persistence landscape](persistence-landscape.md)

## Related topics

- [Simplicial complexes from point clouds](../simplicial-complexes-from-point-clouds/README.md):
  the Čech and Vietoris–Rips filtrations whose homology gives the persistence modules of data.
- [Smith normal form](../../../LinearAlgebra/eigenvalues-and-canonical-forms/smith-normal-form/README.md):
  barcodes of finite filtrations are computed by reducing boundary matrices over the principal
  ideal domain $k[t]$ to Smith normal form (Carlsson, *Topology and data*, §2.3).
- [Single-linkage hierarchical clustering](../../../ComputerScience/machine-learning/unsupervised-learning/single-linkage-hierarchical-clustering/README.md):
  the zero-dimensional barcode of the Vietoris–Rips filtration records when single-linkage
  clusters merge.
