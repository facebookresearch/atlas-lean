# Polynomial time with exact-length advice

For $a:\mathbb{N}\to\mathbb{N}$, $\mathsf{P}/a$ is the class of languages $L\subseteq\{0,1\}^*$ for which there are a polynomial-time machine $M$ and an advice sequence $(\alpha_n)_{n\ge0}$ with $|\alpha_n|=a(n)$ **exactly**, such that $x\in L\iff M(\alpha_{|x|},x)=1$ for every $x$. The advice is arbitrary (not required to be computable). $\mathsf{P}/\mathrm{poly}=\bigcup_k\mathsf{P}/n^k$ up to padding of the advice.

## Depends on

- [The complexity class P](../../the-classes-p-np-and-conp/p.md)
- [Polynomial time with polynomial advice](../../time-and-space-complexity-classes/ppoly.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Section 3.1.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
