# VECTOR BIN PACKING is NP-complete

The [decision problem](vector-bin-packing-dec.md) VECTOR BIN PACKING belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Hardness comes from BIN PACKING, already for dimension $d = 2$ (the instances require $d \ge 2$, so dimension $1$ is not available): for capacity $B > 0$, send each piece of size $s \le B$ to the vector $(s/B, 0)$, and map an instance with a piece larger than $B$ to a fixed no-instance. The cited NP-completeness of vector packing is the observation that bin packing is this special case, not a separate reduction.

## Sources

- G. J. Woeginger, "There is no asymptotic PTAS for two-dimensional vector packing", Information Processing Letters 64 (1997), 293-297, doi:10.1016/S0020-0190(97)00179-8 (problem statement: "the input consists of a list L of vectors in [0, 1]^d. The goal is to partition the vectors in L into the minimum number of subsets, such that in every subset the sum of all vectors is at most one in every coordinate"; "The vector packing problem is easily seen to be NP-complete, since it contains classical bin packing as a special case").
- M. R. Garey, R. L. Graham, D. S. Johnson and A. C.-C. Yao, "Resource constrained scheduling as generalized bin packing", Journal of Combinatorial Theory, Series A 21 (1976), 257-298, doi:10.1016/0097-3165(76)90001-7 (the model).
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR1] BIN PACKING (embedded in dimension $2$ as above).
