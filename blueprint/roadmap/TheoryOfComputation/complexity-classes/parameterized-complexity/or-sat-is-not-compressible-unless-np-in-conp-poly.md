# OR-SAT is not compressible unless NP ⊆ coNP/poly

If OR-SAT, a disjunction of many formulas parameterized by the size of each, can be compressed to instances of size polynomial in that parameter, deterministically or even probabilistically with error below $2^{-m}$, then $\mathsf{NP}\subseteq\mathsf{coNP}/\mathrm{poly}$ and the polynomial hierarchy collapses.

Use the parametric problems and the notions of compressibility of instance compression, with $\text{OR-SAT}=\{\langle\{\varphi_i\},1^n\rangle:\text{some }\varphi_i\text{ is satisfiable and each }|\varphi_i|\le n\}$ and $m$ the instance size. Let $\mathsf{NP}/\mathrm{poly}$ ($\mathsf{coNP}/\mathrm{poly}$) be the class of languages decided by a nondeterministic (co-nondeterministic) polynomial-time machine with an advice string of polynomial length that depends only on the input length; $\mathsf{coNP}\subseteq\mathsf{NP}/\mathrm{poly}$ holds iff $\mathsf{NP}\subseteq\mathsf{coNP}/\mathrm{poly}$. Then:

1. If OR-SAT is compressible, then $\mathsf{coNP}\subseteq\mathsf{NP}/\mathrm{poly}$, and hence $\mathsf{PH}$ collapses.
2. If SAT is compressible, then $\mathsf{coNP}\subseteq\mathsf{NP}/\mathrm{poly}$ and $\mathsf{PH}$ collapses; the same holds if Clique, Dominating Set or Integer Programming is compressible.
3. If OR-SAT is compressible with error less than $2^{-m}$, then $\mathsf{NP}\subseteq\mathsf{coNP}/\mathrm{poly}$ and $\mathsf{PH}$ collapses.
4. If OR-SAT is non-uniformly compressible, then $\mathsf{NP}\subseteq\mathsf{coNP}/\mathrm{poly}$ and $\mathsf{PH}$ collapses.

In each case the collapse is to the third level, by Yap's theorem. Item 1 is the compression form of the theorem that no polynomial-time map sends a disjunction of formulas of size at most $n$ to an equivalent instance of length polynomial in $n$ unless $\mathsf{NP}\subseteq\mathsf{coNP}/\mathrm{poly}$.

## Expansion

Fix a compression $f$ of OR-SAT into a set $A$, with compressed length $k\le(n+\log m)^c$. Let $S$ be the unsatisfiable formulas of size at most $n$ and $T$ the strings of length at most $k$ outside $A$; then $f$ maps every tuple in $S^{m/n}$ into $T$. Pick strings of $T$ greedily, each time the one with the most preimages among tuples of formulas not yet covered. By the pigeonhole principle each pick covers at least half of the remaining formulas once $m=n^{c'}$ with $(k+1)n<m$, so $O(n)$ picks suffice. With these strings as advice, a formula of size $n$ is certified unsatisfiable by guessing a tuple that contains it and checking that $f$ maps the tuple to one of them, while a tuple containing a satisfiable formula maps into $A$. Item 2 follows because OR-SAT W-reduces to SAT, Clique, Dominating Set and Integer Programming. For items 3 and 4, a union bound gives one random string that is correct for every instance of size $m$, and it is added to the advice.

## Depends on

- [Instance compression of parametric problems](instance-compression-of-parametric-problems.md)
- [The class coNP](../the-classes-p-np-and-conp/co-np.md)
- [The polynomial hierarchy](../time-and-space-complexity-classes/ph.md)

## Proof depends on

None.

## Sources

- Lance Fortnow and Rahul Santhanam, "Infeasibility of Instance Compression and Succinct PCPs for NP", *Journal of Computer and System Sciences* 77(1), 2011, pp. 91–106, https://doi.org/10.1016/j.jcss.2010.06.007 (Theorem 1.2, Theorem 3.1 with Corollary 3.2, Theorem 3.3, Corollary 3.4, Section 3).
