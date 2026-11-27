# Robustness of the RP and BPP success thresholds

Let $c,d>0$ be constants. If a polynomial-time probabilistic machine $M$ accepts every $x\in L$ with probability at least $|x|^{-c}$ and accepts no $x\notin L$, then there is a polynomial-time probabilistic machine $M'$ that accepts every $x\in L$ with probability at least $1-2^{-|x|^{d}}$ and accepts no $x\notin L$; so the success threshold in the definition of $\mathsf{RP}$ can be replaced by any positive constant, and even by $|x|^{-c}$, without changing the class. Likewise, if $\Pr[M(x)=L(x)]\ge\frac12+|x|^{-c}$ for every $x$, there is a polynomial-time $M'$ with $\Pr[M'(x)=L(x)]\ge1-2^{-|x|^{d}}$ for every $x$; in particular the class $\mathsf{BPP}_{n^{-c}}$ defined with success probability $\frac12+|x|^{-c}$ equals $\mathsf{BPP}$.

## Proof sketch

Repeat the algorithm independently on disjoint blocks of the random string: for one-sided error accept if any run accepts, so $k$ runs fail together with probability at most $(1-|x|^{-c})^{k}$; for two-sided error take the majority vote and apply the Chernoff bound.

Derived here (not stated in the cited source): the same repetition handles thresholds $1/q(n)$ and $1-2^{-q(n)}$ for any polynomial $q$ with $q(n)\ge2$ (respectively $q(n)\ge1$) for all $n$, with finitely many short instances handled by table lookup (at $q=1$ the threshold $1/q=1$ forbids errors and gives $\mathsf{P}$), and the BPP statement holds with error $1/2-1/q(n)$ for $q(n)>2$. Since $\mathsf{ZPP}=\mathsf{RP}\cap\mathsf{coRP}$, the thresholds for $\mathsf{ZPP}$ are equally robust.

## Depends on

- [The class RP](../../time-and-space-complexity-classes/rp.md)
- [BPP](../../time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [ZPP](../../time-and-space-complexity-classes/zpp.md)
- [Error reduction for BPP](../../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/error-reduction-for-bpp.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009; web draft of January 2007, Section 7.4.1, Lemma 7.9, Theorem 7.10 and Theorem 7.12 with the sentence before it.
- John Gill, "Computational Complexity of Probabilistic Turing Machines", SIAM Journal on Computing 6(4), 1977.
