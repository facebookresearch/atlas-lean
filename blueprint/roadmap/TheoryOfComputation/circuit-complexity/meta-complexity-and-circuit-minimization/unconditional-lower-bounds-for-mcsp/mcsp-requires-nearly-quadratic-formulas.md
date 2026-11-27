# MCSP requires nearly quadratic De Morgan formulas

For the size threshold $s(n)=2^{\sqrt{\log n}/2}$, every De Morgan formula computing MCSP on truth tables of length $n$ has size $n^{2-O(1/\sqrt{\log n})}$, nearly matching the best formula lower bounds known for any explicit function.

Let $L(f)$ denote the minimum leaf size of a De Morgan formula computing $f$, and let $\mathrm{MCSP}[s]$ on inputs of length $n$ ask whether the truth table has circuit size at most $s(n)$.

**Theorem (Hirahara–Santhanam).** For $s(n)=n^{1/(2\sqrt{\log n})}=2^{\sqrt{\log n}/2}$, $\mathrm{MCSP}[s]$ requires De Morgan formulas of size $n^{2-O(1/\sqrt{\log n})}$; that is, $L(\mathrm{MCSP}[s])\ge n^{2-O(1/\sqrt{\log n})}$, where $n$ is the input length.

**Key lemma.** If a restriction $\rho:[n]\to\{0,1,*\}$ is computable by a circuit of size $s$ and $V=\rho^{-1}(*)$, then for $f=\mathrm{MCSP}[s]$ one has $L(f|_{\rho})\ge|V|-O(s\log s)$.

## Expansion

Impagliazzo, Meka and Zuckerman showed that compositions of $r$ $q$-regular $\ell$-wise independent restrictions shrink formulas like truly random ones: $\mathbb{E}[L(f|_{\rho})]\le c^r p^{\Gamma}L(f)$ with shrinkage exponent $\Gamma=2$. Such restrictions use few random bits, so as truth tables they have circuit size $s$ much smaller than the expected number $pn$ of free variables. The key lemma says MCSP does not shrink under them: setting all free variables to $0$ yields a yes-instance, and if $f|_{\rho}$ ignored a set $V_0$ of free variables, all $2^{|V_0|}$ settings of $V_0$ would be yes-instances, while only $s^{O(s)}$ truth tables have circuits of size $s$. Comparing $pn/8\le c^rp^{\Gamma}L(f)$ with $p=2^{\sqrt{\log n}}/n$ and $r=\Theta(\sqrt{\log n})$ gives the bound.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Circuit complexity of a Boolean function and truth tables](../../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)

## Proof depends on

None.

## Sources

- Shuichi Hirahara, Rahul Santhanam, "On the Average-Case Complexity of MCSP and Its Variants", *Computational Complexity Conference (CCC)*, 2017, https://doi.org/10.4230/LIPIcs.CCC.2017.7 (Theorem 26, Lemma 29, Theorem 28, Section 4).
