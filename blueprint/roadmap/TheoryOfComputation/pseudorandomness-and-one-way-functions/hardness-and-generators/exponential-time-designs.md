# Exponential-time computable designs with small intersections

For every real $\gamma>0$ there are $c>0$, $k_0$ and functions $m(k)\ge ck$, $\ell(k)\ge 2^{ck}$ for $k\ge k_0$, together with sets $S(k,1),\dots,S(k,\ell(k))\subseteq[k]$ with $|S(k,i)|=m(k)$ and $|S(k,i)\cap S(k,j)|\le\gamma m(k)$ for $i\ne j$, such that the characteristic vector of $S(k,i)$ is computable from $(k,i)$ in time $2^{O(k)}$.

## Proof sketch

Greedy construction: split $[k]$ into $q$ blocks of $t\approx k/B$ elements for $B=10q^2+1$, $q=\max(2,\lceil1/\gamma\rceil)$, and repeatedly add any set choosing one element per block whose overlap with all previous sets is at most $t$. A counting argument shows that greedy never gets stuck before $2^{\Omega(k)}$ sets, and each step searches $2^{O(k)}$ candidates.

## Depends on

- [Combinatorial designs for the Nisan–Wigderson generator](../derandomization/combinatorial-designs-for-the-nisanwigderson.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 7–8", 2007, Exercise 8.19.
- Noam Nisan and Avi Wigderson, "Hardness vs Randomness", Journal of Computer and System Sciences 49(2), 1994.
