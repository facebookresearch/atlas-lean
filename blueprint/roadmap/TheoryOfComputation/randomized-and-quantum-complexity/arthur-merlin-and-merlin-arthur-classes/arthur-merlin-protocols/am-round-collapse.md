# Babai–Moran: AM[k] = AM for every constant k

For every constant $k\ge2$, $\mathsf{AM}[k]=\mathsf{AM}$, and $\mathsf{MA}[k]=\mathsf{AM}$ for every constant $k\ge3$. More generally every fixed pattern $\pi$ gives a subclass of $\mathsf{AM}$, and any pattern containing $AM$ as a (not necessarily contiguous) subsequence gives exactly $\mathsf{AM}$. The key step is the swap $\mathsf{AM}[\sigma M A\tau]\subseteq\mathsf{AM}[\sigma A M\tau]$.

## Proof sketch

Swap: amplify the error of the $MA$ suffix by parallel repetition so that Merlin's single message works for most random strings simultaneously; then Arthur may send all his random strings first and Merlin answers afterwards. Applying swaps moves all Arthur moves left, and consecutive moves of one player merge.

## Depends on

- [Public-coin Arthur–Merlin games with a fixed move pattern](arthur-merlin-move-patterns.md)

## Proof depends on

- [MA is contained in AM](../ma-subset-am.md)

## Sources

- László Babai and Shlomo Moran, "Arthur–Merlin Games: A Randomized Proof System, and a Hierarchy of Complexity Classes", Journal of Computer and System Sciences 36(2), 254–276, 1988, Theorem 3 (Collapse Theorem: $\mathsf{AM}=\mathsf{AM}(k)=\mathsf{MA}(k+1)$ for constant $k\ge2$) and Section 3.
- László Babai, "Trading Group Theory for Randomness", Proceedings of the 17th Annual ACM Symposium on Theory of Computing, 421–429, 1985.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
