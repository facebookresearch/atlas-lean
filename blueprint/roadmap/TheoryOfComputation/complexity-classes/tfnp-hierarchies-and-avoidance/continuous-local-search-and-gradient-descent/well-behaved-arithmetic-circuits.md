# Well-behaved arithmetic circuits and Lipschitz violation witnesses for continuous total search problems

An **arithmetic circuit** with $n$ inputs is a directed acyclic graph whose internal gates are binary gates from $\{+,-,\times,\max,\min,<\}$ (the gate $u<v$ outputs $1$ if $u<v$ and $0$ otherwise) together with $0$-ary gates outputting rational constants; it computes a map $\mathbb{R}^n\to\mathbb{R}^k$. Rationals are written as irreducible fractions in binary and $\mathrm{size}(\cdot)$ counts bits. A multiplication gate is **true** if both of its inputs are non-constant gates; multiplication by a constant is unrestricted. A circuit $f$ is **well-behaved** if every directed path ending at an output passes through at most $\log \mathrm{size}(f)$ true multiplication gates.

Facts: well-behavedness is checkable in polynomial time, and for every rational $x$ the value $f(x)$ is computable in time $\mathrm{poly}(\mathrm{size}(f),\mathrm{size}(x))$. Without the restriction, $n$ chained squarings compute $x^{2^n}$, whose bit length is exponential, so problems defined by unrestricted circuits need not lie in FNP; an alternative repair adds a unary bound $K$ and accepts as a solution any input on which some gate value $a/b$ has $|a|$ or $b$ longer than $K\cdot\mathrm{size}(x)$ bits.

**Violation convention.** A continuous total search problem receives a purported Lipschitz constant $L>0$ in binary; for a circuit $h$ on domain $D$, any pair $x,y\in D$ with $\|h(x)-h(y)\|>L\|x-y\|$ is accepted as a solution (a *violation*). A reduction is **promise-preserving** if every violation of the target instance is mapped back to a violation of the source instance.

## Depends on

- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
- Constantinos Daskalakis and Christos H. Papadimitriou, "Continuous Local Search", SODA (2011).
