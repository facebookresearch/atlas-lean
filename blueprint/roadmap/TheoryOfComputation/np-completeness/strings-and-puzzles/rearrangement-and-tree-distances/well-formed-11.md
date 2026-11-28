# Well-formed instances of UNSIGNED TRANSLOCATION DISTANCE

An instance $(A, B, K)$, with $A$ and $B$ lists of chromosomes, each a list of natural numbers, is well-formed when every chromosome of $A$ and $B$ is nonempty with only positive entries, the concatenation of the chromosomes of $A$ has no repeated entry, and the concatenation of the chromosomes of $B$ is a permutation of it, with multiplicities. Having the same set of genes is not enough: $[[1]]$ and $[[1, 1]]$ have the same genes, but $[1, 1]$ is not a permutation of $[1]$.
