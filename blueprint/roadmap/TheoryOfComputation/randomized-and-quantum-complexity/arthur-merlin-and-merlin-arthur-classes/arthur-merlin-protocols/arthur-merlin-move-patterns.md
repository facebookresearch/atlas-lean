# Public-coin Arthur–Merlin games with a fixed move pattern

For a word $\pi\in\{A,M\}^*$, a language $L$ is in $\mathsf{AM}[\pi]$ if there are a polynomial $p$ and a polynomial-time predicate $V$ such that, in the game where at each $A$ position Arthur sends a uniformly random string of $p(|x|)$ bits and at each $M$ position Merlin sends a string of $p(|x|)$ bits chosen adaptively, after which $V$ is applied to $x$ and the whole transcript: if $x\in L$ some Merlin strategy makes $V$ accept with probability $\ge 2/3$, and if $x\notin L$ every strategy makes it accept with probability $\le1/3$. $\mathsf{MA}=\mathsf{AM}[MA]$, $\mathsf{AM}=\mathsf{AM}[AM]$, and $\mathsf{AM}[k]$ is the class for alternating patterns of length $k$ starting with $A$.

## Depends on

- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../../complexity-classes/time-and-space-complexity-classes/am.md)
- [The class MA (Merlin–Arthur)](../../../complexity-classes/time-and-space-complexity-classes/ma.md)
- [Public-coin interactive proofs](../../goldwasser-sipser-theorem/pub-ip.md)

## Sources

- László Babai, "Trading Group Theory for Randomness", Proceedings of the 17th Annual ACM Symposium on Theory of Computing, 421–429, 1985.
- László Babai and Shlomo Moran, "Arthur–Merlin Games: A Randomized Proof System, and a Hierarchy of Complexity Classes", Journal of Computer and System Sciences 36(2), 254–276, 1988, Section 2.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
