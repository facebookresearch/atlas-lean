# Succinct PCPs for SAT and self-compression

SAT has PCPs whose proof length is polynomial in the number of variables, rather than in the formula size, essentially iff SAT is self-compressible; hence SAT has no such succinct PCPs unless $\mathsf{NP}\subseteq\mathsf{coNP}/\mathrm{poly}$ and the polynomial hierarchy collapses.

A parametric problem $L$ has succinct PCPs with completeness $c$, soundness $s$, proof size $S$ and query complexity $q$ if a probabilistic polynomial-time oracle machine $V$ satisfies, for every instance $\langle x,1^n\rangle$: if $\langle x,1^n\rangle\in L$, some proof $y$ of size $S(n)$ makes $V^y$ accept with probability at least $c$; if $\langle x,1^n\rangle\notin L$, every $y$ of size $S(n)$ makes $V^y$ accept with probability at most $s$; and $V$ makes at most $q$ queries on every computation path. $L$ has succinct PCPs if this holds with $c=1$, $s=1/2$, $S=\mathrm{poly}(n)$ and $q=O(1)$. Then:

1. If SAT has succinct PCPs, then SAT is self-compressible with error less than $2^{-m}$, where $m$ is the instance size.
2. If SAT has succinct PCPs with completeness $c$, soundness $s$, proof size $\mathrm{poly}(n)$ and query complexity $O(1)$, where $c+s$ is computable in time $\mathrm{poly}(m)$ and $c-s>1/\mathrm{poly}(n)$, then SAT is self-compressible.
3. SAT does not have succinct PCPs unless $\mathsf{NP}\subseteq\mathsf{coNP}/\mathrm{poly}$ and $\mathsf{PH}$ collapses.
4. Conversely, every parametric problem in $\mathsf{NP}$ that is compressible within $\mathsf{NP}$ has succinct PCPs; in particular, if SAT is self-compressible it has succinct PCPs, and vertex cover has succinct PCPs.

## Expansion

For item 1, let the verifier have proof size $n^C$, $q=O(1)$ queries and randomness $R=\mathrm{poly}(m)$. Sample $N=n^C+m+1$ random strings (still polynomial in $m$ since $n\le m$; the source's printed proof takes $m^2$ samples without union-bounding over all proofs); each fixes a test function on $q$ proof bits, written as a canonical CNF of size $O(q2^q)$. Output the conjunction of these CNFs without repetition. There are at most $n^{Cq}2^{2^q}$ distinct test functions, so the output still has size $\mathrm{poly}(n)$; satisfiable inputs give satisfiable outputs by perfect completeness, and for unsatisfiable inputs each of the at most $2^{n^C}$ proofs of size $n^C$ is rejected by at least half of the random strings, so by a union bound over all proofs the output is satisfiable with probability at most $2^{n^C-N}<2^{-m}$. Item 2 keeps weighted constraints and a threshold $(c+s)/2$ and then applies the Cook–Levin reduction. Item 3 combines item 1 with the infeasibility of compressing OR-SAT, even with error below $2^{-m}$, unless $\mathsf{NP}\subseteq\mathsf{coNP}/\mathrm{poly}$. Item 4 composes the compression map with a standard PCP for the compressed instance.

## Depends on

- [Instance compression of parametric problems](instance-compression-of-parametric-problems.md)
- [OR-SAT is not compressible unless NP ⊆ coNP/poly](or-sat-is-not-compressible-unless-np-in-conp-poly.md)
- [The complexity class NP](../the-classes-p-np-and-conp/np.md)
- [The polynomial hierarchy](../time-and-space-complexity-classes/ph.md)

## Proof depends on

- [OR-SAT is not compressible unless NP ⊆ coNP/poly](or-sat-is-not-compressible-unless-np-in-conp-poly.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../../pcp-and-inapproximability/pcp-theorem.md)
- [Cook–Levin theorem: SAT is NP-complete](../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Lance Fortnow and Rahul Santhanam, "Infeasibility of Instance Compression and Succinct PCPs for NP", *Journal of Computer and System Sciences* 77(1), 2011, pp. 91–106, https://doi.org/10.1016/j.jcss.2010.06.007, read in the authors' version of March 19, 2010 <https://lance.fortnow.com/papers/files/compress.pdf>, whose numbering is cited (Definition 4.1, Theorems 4.2, 4.3, 4.5 and 4.6, Corollaries 4.4 and 4.7, Theorem 3.3).
