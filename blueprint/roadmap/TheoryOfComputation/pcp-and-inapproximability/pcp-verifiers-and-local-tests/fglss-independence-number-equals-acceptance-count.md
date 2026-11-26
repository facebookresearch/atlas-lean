# Independence number of the FGLSS graph equals the best acceptance count

For every nonadaptive PCP verifier $V$ with $r$ random bits and every input $x$,

$$\alpha(G_{V,x}) = \max_{\pi} \big|\{\rho \in \{0,1\}^r : V^\pi(x, \rho) = 1\}\big| = 2^r \max_\pi \Pr_\rho[V^\pi(x,\rho) = 1],$$

the maximum being attained by a finite proof. Hence $\alpha(G_{V,x}) \le 2^r$; if $V$ has perfect completeness for $L$ then $\alpha(G_{V,x}) = 2^r$ for $x \in L$, and if $V$ has soundness $1/2$ then $2\alpha(G_{V,x}) \le 2^r$ for $x \notin L$.

## Proof sketch

A proof $\pi$ selects one accepting view per random string it makes $V$ accept; these views are pairwise consistent, hence independent. Conversely an independent set contains at most one view per random string and its views are pairwise consistent, so they extend to a common proof accepted on all their random strings.

## Depends on

- [FGLSS graph of a nonadaptive PCP verifier](fglss-graph-of-a-pcp-verifier.md)

## Sources

- U. Feige, S. Goldwasser, L. Lovász, S. Safra and M. Szegedy, "Interactive Proofs and the Hardness of Approximating Cliques", Journal of the ACM 43(2), 1996.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
