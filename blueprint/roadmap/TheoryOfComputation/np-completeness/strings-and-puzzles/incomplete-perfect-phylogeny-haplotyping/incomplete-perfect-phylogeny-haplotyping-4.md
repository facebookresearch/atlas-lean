# INCOMPLETE PERFECT PHYLOGENY HAPLOTYPING is NP-complete

The decision problem INCOMPLETE PERFECT PHYLOGENY HAPLOTYPING belongs to NP, and every decision
problem in NP has a polynomial-time many-one reduction to it.

The language uses indexed leaves and the [perfect phylogeny](../../../../Biology/phylogenetics/splits-compatibility-ultrametrics-and-upgma/is-perfect-phylogeny.md) predicate, which accepts constant sites and edges without a site; the hardness references use one leaf per distinct haplotype and a site on every edge. Both formulations are equivalent to the four-gamete condition on the haplotype matrix (no two sites show all four gametes), so the cited hardness applies to this language.

## Sources

- G. Kimmel and R. Shamir, "The incomplete perfect phylogeny haplotype problem", Journal of Bioinformatics and Computational Biology 3 (2005), 359-384, doi:10.1142/S0219720005001090, Problem 2 (IPPH), Section 1 (the unrooted problem is NP-hard by Steel's result for partial binary characters) and Section 3, Theorems 1 and 2 (the rooted problem is NP-complete).
- M. A. Steel, "The complexity of reconstructing trees from qualitative characters and subtrees", Journal of Classification 9 (1992), 91-116, doi:10.1007/BF02618470.
