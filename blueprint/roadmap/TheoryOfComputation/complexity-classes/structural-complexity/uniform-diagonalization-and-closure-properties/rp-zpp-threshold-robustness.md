# Robustness of the RP and ZPP thresholds

The success threshold $1/2$ in the definitions of $\mathsf{RP}$ and $\mathsf{ZPP}$ (probability of a definite correct answer) can be replaced by $1/q(n)$ for any polynomial $q$ with $q(n)\ge2$ for all $n$, and equally by $1-2^{-q(n)}$ for any polynomial $q$ with $q(n)\ge1$ for all $n$, without changing the classes (at $q=1$ the threshold $1/q=1$ forbids errors and gives $\mathsf{P}$); finitely many short instances may be handled by table lookup. The analogous statement for $\mathsf{BPP}$ holds with error $1/2-1/q(n)$ for any polynomial $q$ with $q(n)>2$ for all $n$ (so that the error is positive).

## Proof sketch

Repeat the algorithm $O(q(n)\cdot r(n))$ times independently on disjoint blocks of the random string and accept if any run gives a certain answer; the probability that all runs fail is at most $(1-1/q)^{qr}\le e^{-r}$.

## Depends on

- [The class RP](../../time-and-space-complexity-classes/rp.md)
- [ZPP](../../time-and-space-complexity-classes/zpp.md)

## Proof depends on

- [Error reduction for BPP](../../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/error-reduction-for-bpp.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- John Gill, "Computational Complexity of Probabilistic Turing Machines", SIAM Journal on Computing 6(4), 1977.
