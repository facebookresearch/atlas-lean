# Error reduction for BPP

**Theorem.** Let $L \subseteq \{0,1\}^*$ and suppose a polynomial-time probabilistic Turing machine $M$ satisfies $\Pr[M(x) = L(x)] \ge \tfrac12 + 1/p(|x|)$ for every $x$, for some
polynomial $p$ with $p(n) \ge 2$ for all $n$. Then for every constant $d > 0$ there is a polynomial-time probabilistic Turing machine $M'$ with $\Pr[M'(x) = L(x)] \ge 1 - 2^{-|x|^d}$ for every $x$.

The machine $M'$ runs $M(x)$ independently $k = \lceil 8\, p(|x|)^2\, |x|^d \rceil$ times and outputs the majority answer; the error bound follows from the Chernoff bound for the
independent indicators of the runs that answer correctly. In particular, the error $1/3$ in the definition of $\mathsf{BPP}$ can be replaced by $2^{-|x|^d}$ for any
constant $d$, or by any constant in $(0, 1/2)$.

## Depends on

- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [Hoeffding lower-tail bound for Bernoulli sums](../../../Probability/concentration-inequalities/hoeffding-s-inequality/hoeffding-binomial-lower-tail.md)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Theorem 7.10 (error reduction) with its proof.
