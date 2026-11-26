# Kolmogorov complexity relative to a universal Turing machine

Let $U$ be a deterministic multi-tape Turing machine that is universal in the sense that on input the pair $(\langle M \rangle, x)$, encoded by writing each bit $b$ of the description $\langle M \rangle$ as $1b$ followed by the terminator $0$ and then $x$, it halts with output $o$ exactly when $M$ halts on $x$ with output $o$. For a machine $M$ write $K_M(x)$ for the length of a shortest binary input on which $M$ halts with output $x$ (plain description complexity, not the prefix-free complexity of the neighbouring pages). Then for every Turing machine $M$ with binary description $\langle M \rangle$ and every $x$,

$$K_U(x) \le K_M(x) + 2|\langle M \rangle| + 1.$$

## Proof sketch

Prefix a shortest $M$-description of $x$ with the self-delimiting encoding of $\langle M\rangle$, of length $2|\langle M\rangle| + 1$; universality makes $U$ output $x$ on it.

## Depends on

- [Kolmogorov complexity](../k.md)
- [The universal description method](../u.md)

## Proof depends on

- [Optimality (the invariance theorem)](../exists-k-le-of-partrec.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
