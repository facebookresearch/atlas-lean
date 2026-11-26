# Kleene–Post: there are Turing-incomparable sets below the halting set

There are sets $A,B\subseteq\mathbb{N}$ with $A\not\le_T B$ and $B\not\le_T A$; hence there are incomparable Turing degrees. Moreover $A$ and $B$ can be chosen with $A,B\le_T\emptyset'$, the halting set, so incomparable degrees exist below $\mathbf{0}'$.

## Proof sketch

Finite extension: build initial segments $\sigma_s,\tau_s$ of the characteristic functions. At stage $2e$ make $\Phi_e^{B}\ne A$: extend $\tau$ to some $\tau'$ with $\Phi_e^{\tau'}(n)\downarrow$ for a fresh $n$ if possible and set $A(n)$ to differ; otherwise $\Phi_e^{B}(n)$ diverges. Odd stages are symmetric. Each question 'does some extension make the computation converge?' is $\Sigma_1$, hence decidable relative to $\emptyset'$, so the construction is computable in $\emptyset'$.

## Depends on

- [Turing reducibility of predicates](../turing-degrees-and-the-turing-jump/turing-reducible-pred.md)
- [Turing degree of a predicate](../turing-degrees-and-the-turing-jump/turing-degree-of.md)
- [Halting set](../turing-reducibility/halting-set.md)

## Proof depends on

- [The Turing jump](../turing-degrees-and-the-turing-jump/jump.md)

## Sources

- Stephen Cole Kleene and Emil L. Post, "The Upper Semi-Lattice of Degrees of Recursive Unsolvability", Annals of Mathematics (2) 59(3), 1954.
- Robert I. Soare, "Recursively Enumerable Sets and Degrees", Springer, 1987.
- Stephen G. Simpson, "Topics in Logic and Foundations: Spring 2004", 2005, Theorem 2.6.4.
