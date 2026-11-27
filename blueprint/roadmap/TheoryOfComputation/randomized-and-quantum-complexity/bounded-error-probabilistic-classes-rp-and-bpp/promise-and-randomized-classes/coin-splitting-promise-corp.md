# Splitting the coins of a very-low-error BPP algorithm reduces it to promise-coRP

Let $A$ be a probabilistic polynomial-time algorithm using $2p(n)$ coins whose error on every input of length $n$ is below $2^{-(p(n)+1)}$. Consider the promise problem $\Pi'$ on pairs $(x,r)$ with $|r|=p(|x|)$: yes-instances are pairs with $A(x,rs)=1$ for **all** $s$, no-instances those with $\Pr_s[A(x,rs)=1]\le 1/2$. Then $\Pi'\in\mathrm{promise}\text{-}\mathsf{coRP}$ (run $A(x,rs)$ on a uniform $s$), every $(x,r)$ with $x\notin L(A)$ is a no-instance, and the map $x\mapsto(x,r)$ with uniform $r$ is a one-sided randomized reduction of $L(A)$ to $\Pi'$: for $x$ in the language the sample hits $\Pi'_{\mathrm{yes}}$ with probability $>1/2$.

## Proof sketch

Fewer than $2^{-(p+1)}\cdot2^{2p}=2^{p-1}$ coin strings $rs$ make $A$ err on $x$. For $x\notin L(A)$ this leaves fewer than $2^{p-1}$ accepting completions $s$ of every $r$, so every $(x,r)$ is a no-instance; for $x\in L(A)$ fewer than $2^{p-1}$ first halves $r$ have a rejecting completion, so more than half of them give yes-instances. On a yes-instance $A(x,rs)$ accepts for every $s$, and on a no-instance it rejects with probability at least $1/2$, which is one-sided error of the coRP kind.

## Depends on

- [Promise problems and promise classes](promise-problems.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [The class coRP](../../../complexity-classes/time-and-space-complexity-classes/co-rp.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Section 6.1.3.2 ("Relating BPP to RP"), the paragraph "An illustration" preceding the proof of Theorem 6.9: for an algorithm using $2p'(|x|)$ coins with error below $2^{-(p'(|x|)+1)}$, every $x \in S$ has $\Pr_{r'}[(\forall r'')\,A'(x, r'r'') = 1] > 1/2$, every $x \notin S$ and every $r'$ have $\Pr_{r''}[A'(x, r'r'') = 1] < 1/2$, and $x \mapsto (x, r')$ is a one-sided error randomized Karp-reduction to a coRP promise problem; numbering of the 2007 public draft on the author's homepage. Exercise 6.11 there (supplementary) asks for the details; its no-instances are all pairs $(x,r)$ with $x\notin S$, a subset of the no-instances used here.
