# The palindrome separates non-commutative ABPs from circuits

Over $n$ variables, the *palindrome* $\mathrm{Pal}_{2m}=\sum_{|w|=m}w\cdot w^{\mathrm{rev}}$ requires homogeneous non-commutative ABPs of size at least $n^m$ (its middle matrix $M_m$ is a permutation matrix of size $n^m$), while it has non-commutative arithmetic circuits of size $O(nm)$; since a non-commutative formula of size $s$ for a homogeneous polynomial of degree $2m$ converts to a homogeneous ABP of size $s\cdot\mathrm{poly}(m)$, its non-commutative formulas have size at least $n^m/\mathrm{poly}(m)$. The same lower bound holds for $\mathrm{Doub}_{2m}=\sum_{|w|=m}w\cdot w$.

## Proof sketch

For $\sum_uu\,\sigma(u)$ with $\sigma$ a permutation of the words of length $m$, the middle Nisan matrix is the identity with rows permuted by $\sigma$, of full rank $n^m$. The palindrome has the recursive formula $\mathrm{Pal}_{2m}=\sum_ix_i\,\mathrm{Pal}_{2m-2}\,x_i$.

## Depends on

- [Non-commutative arithmetic circuits and algebraic branching programs](non-commutative-circuits-and-abps.md)

## Proof depends on

- [Nisan's characterization of non-commutative ABP size](nisan-characterization-of-abp-size.md)

## Sources

- Noam Nisan, "Lower Bounds for Non-Commutative Computation", Proceedings of the 23rd Annual ACM Symposium on Theory of Computing, 1991.
- Ramprasad Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", version 9.0.3, 2021, Chapter 11.
