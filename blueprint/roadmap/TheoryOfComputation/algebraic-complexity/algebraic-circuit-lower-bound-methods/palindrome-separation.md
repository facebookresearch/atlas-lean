# The palindrome separates non-commutative ABPs from circuits

Over $n$ variables, every non-commutative algebraic branching program computing the *palindrome* $\mathrm{Pal}_{d}=\sum_{|w|=d/2}w\cdot w^{\mathrm{rev}}$ (for even $d$, the sum over words $w$ of length $d/2$ in the variables) or the double polynomial $\mathrm{Doub}_{d}=\sum_{|w|=d/2}w\cdot w$ has size $n^{\Omega(d)}$, while $\mathrm{Pal}_d$ is computed by a non-commutative arithmetic circuit of size $\mathrm{poly}(n, d)$. Thus non-commutative circuits are exponentially more powerful than non-commutative ABPs.

## Proof sketch

For $\sum_u u\,\sigma(u)$ with $\sigma$ a permutation of the words of length $d/2$, the middle Nisan matrix $M_{d/2}$ is the identity with rows permuted by $\sigma$, of full rank $n^{d/2}$, and Nisan's characterization bounds the size of a homogeneous ABP below by this rank. The palindrome has the recursive formula $\mathrm{Pal}_{d}=\sum_ix_i\,\mathrm{Pal}_{d-2}\,x_i$. (Derived, not stated in this form by the sources: with $d = 2m$, the middle-matrix rank gives homogeneous ABPs of size at least $n^m$; reusing $\mathrm{Pal}_{2m-2}$ once per level in the recursion gives circuits of size $O(nm)$; and since a non-commutative formula of size $s$ for a homogeneous polynomial of degree $2m$ converts to a homogeneous ABP of size $s\cdot\mathrm{poly}(m)$, non-commutative formulas for $\mathrm{Pal}_{2m}$ and $\mathrm{Doub}_{2m}$ have size at least $n^m/\mathrm{poly}(m)$.)

## Depends on

- [Non-commutative arithmetic circuits and algebraic branching programs](non-commutative-circuits-and-abps.md)

## Proof depends on

- [Nisan's characterization of non-commutative ABP size](nisan-characterization-of-abp-size.md)

## Sources

- Noam Nisan, "Lower Bounds for Non-Commutative Computation", Proceedings of the 23rd Annual ACM Symposium on Theory of Computing, 1991.
- Ramprasad Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", version 9.0.3, 2021, Section 11.1.2: Theorem 11.4 and the remarks after it.
