# Fixing the random seed of a probabilistic circuit

Let $S$ be a probabilistic circuit reading $x\in\{0,1\}^n$ and random inputs $y\in\{0,1\}^m$ that take the values $0$ and $1$ independently with probability $\tfrac12$, and let $A,B\subseteq\{0,1\}^n$. Suppose that $\Pr_y[S(x,y)=1]>1-2^{-n}$ for every $x\in A$ and $\Pr_y[S(x,y)=1]<2^{-n}$ for every $x\in B$. Then there is a deterministic circuit $S_d$ with $C(S_d)\le C(S)$ and $D(S_d)\le D(S)$ that outputs $1$ on every $x\in A$ and $0$ on every $x\in B$; it is obtained by replacing the random inputs $y$ by a suitable constant vector $y^*$.

## Proof sketch

Let $I(x)$ indicate an error of $S$ on $x\in A\cup B$. Each $x$ has error probability below $2^{-n}$, so the expected number of inputs in $A\cup B$ on which $S(\cdot,y)$ errs is below $1$; hence some $y^*$ gives zero errors. Derived here by the same union bound: if $S$ has several outputs and $\mathrm{Correct}(x)$ is any set of acceptable output strings, and for every $x$ fewer than a $2^{-n}$ fraction of the seeds give $S(x,y)\notin\mathrm{Correct}(x)$, then one seed $y^*$ is correct for all $x$ simultaneously; in a model where constants must be produced by gates, hard-wiring $y^*$ costs at most two constant gates and one extra level of depth.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- Leonard Adleman, "Two Theorems on Random Polynomial Time", 19th Annual Symposium on Foundations of Computer Science, 75–83, 1978.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987 (Chapter 12, Section 3, Definitions 3.1–3.2 and Lemma 3.1(iv), pp. 352–354).
