# The integer permanent reduces to the 0/1 permanent

There are polynomial-time maps $M\mapsto B_M$, sending an $n\times n$ integer matrix to a $0/1$ matrix, and a polynomial-time recovery function $\rho$, such that $\operatorname{perm}(M)=\rho\bigl(M,\operatorname{perm}(B_M)\bigr)$ for every integer matrix $M$. Hence computing the permanent of integer matrices is metric (one-query) reducible to the $0/1$ permanent, i.e. to counting perfect matchings of bipartite graphs.

## Proof sketch

Reduce entries modulo $Q=2\,n!\,\|M\|_\infty^{n}+1$ ($\|M\|_\infty$ the largest absolute entry; then $|\operatorname{perm}(M)|<Q/2$), making them nonnegative while $\operatorname{perm}\bmod Q$ still determines $\operatorname{perm}$. Replace each entry $w$ by a gadget of $O(\log w)$ vertices whose cycle covers number $w$ (binary expansion with chains of weight-$2$ gadgets), and each weight-$2$ edge by a $0/1$ gadget with two covers.

## Depends on

- [The 0-1 permanent counts perfect matchings](../complexity-of-the-permanent/permanent-boole-eq-card.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Proposition 6.22.
