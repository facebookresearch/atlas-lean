# Repeated measurement of an isometry on entangled inputs

Let $A:\mathbb{C}^\beta\to\mathbb{C}^\kappa$ be an isometry and $T\subseteq\kappa$ a set of outcomes with $\sum_{a\in T}|(A\phi)_a|^2\le s\|\phi\|^2$ for every $\phi$. For $k$ copies and any (possibly entangled) $\Phi\in(\mathbb{C}^\beta)^{\otimes k}$, let $\Psi = A^{\otimes k}\Phi$. Then:

1. for each copy $j$ and each nonnegative weight $g(u)$ on outcome words that does not depend on $u_j$, $\sum_{u: u_j\in T}g(u)|\Psi_u|^2\le s\sum_ug(u)|\Psi_u|^2$;
2. for $t\ge1$, $\sum_ut^{|\{j:u_j\in T\}|}|\Psi_u|^2\le(1+(t-1)s)^k\|\Phi\|^2$;
3. if $s\le1/3$ and $k = 2r$, the probability that at least $r$ copies land in $T$ is at most $(8/9)^r\|\Phi\|^2$.

## Proof sketch

Part 1 splits off coordinate $j$: $A^{\otimes k}$ is $A$ on copy $j$ after $A^{\otimes(k-1)}$ on the rest, and conditioning on the other outcomes leaves an arbitrary input to the single-copy bound. Iterating part 1 over the copies gives the exponential moment of part 2, exactly as for independent trials. Part 3 is Markov's inequality with $t = 2$: $(1+s)^{2r}/2^r\le(16/9)^r/2^r = (8/9)^r$.

## Depends on

- [Density matrices, pure states and reduced states](../../../QuantumInformation/quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)

## Sources

- A. Yu. Kitaev, A. H. Shen and M. N. Vyalyi, "Classical and Quantum Computation", Graduate Studies in Mathematics 47, American Mathematical Society, 2002.
- C. Marriott and J. Watrous, "Quantum Arthur-Merlin games", Computational Complexity 14:122-152, 2005.
