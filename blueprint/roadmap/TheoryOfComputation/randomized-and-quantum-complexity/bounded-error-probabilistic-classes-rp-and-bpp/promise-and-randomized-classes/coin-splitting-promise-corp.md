# Splitting the coins of a very-low-error BPP algorithm reduces it to promise-coRP

Let $A$ be a probabilistic polynomial-time algorithm using $2p(n)$ coins whose error on every input of length $n$ is below $2^{-(p(n)+1)}$. Consider the promise problem $\Pi'$ on pairs $(x,r)$ with $|r|=p(|x|)$: yes-instances are pairs for which $A(x,rs)$ is correct for **all** $s$, no-instances those for which it errs for **some** $s$. Then $\Pi'\in\mathrm{promise}\text{-}\mathsf{coRP}$, and the map $x\mapsto(x,r)$ with uniform $r$ is a one-sided randomized reduction of $L(A)$ to $\Pi'$: for $x$ in the language the sample hits $\Pi'_{\mathrm{yes}}$ with probability $>1/2$.

## Proof sketch

By counting, fewer than a $2^{-(p+1)}\cdot 2^{p}=1/2$ fraction of first halves $r$ have any bad completion $s$. For fixed $r$, a uniform $s$ exposes an error with positive probability exactly on no-instances, giving one-sided error.

## Depends on

- [Promise problems and promise classes](promise-problems.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [The class coRP](../../../complexity-classes/time-and-space-complexity-classes/co-rp.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 6–7", 2007, Exercise 6.11.
