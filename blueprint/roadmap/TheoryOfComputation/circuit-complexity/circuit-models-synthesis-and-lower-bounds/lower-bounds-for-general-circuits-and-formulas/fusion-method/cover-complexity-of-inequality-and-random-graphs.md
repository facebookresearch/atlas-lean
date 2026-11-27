# Cover complexity of the inequality graph and of random bipartite graphs

For bipartite graphs on vertex sets $\{0,1\}^n\times\{0,1\}^n$ viewed as subsets of $\{0,1\}^n\times\{0,1\}^n$, with the $2N$ rows and columns as supplied sets ($N=2^n$): (i) the inequality graph $\{(u,v):u\neq v\}$ has cover complexity exactly $n$; (ii) every graph with $N$ vertices per side has a pair cover of length at most $N$, and a uniformly random such graph has cover complexity $\Theta(N)$ asymptotically almost surely. For every graph $G$ that is neither empty nor complete, a cover of the Boolean function $f_G$ (with $f_G^{-1}(1)=G$ under the identification of $\{0,1\}^{2n}$ with pairs of vertices, and the $2n$ literals as supplied sets) induces a cover of $G$ of the same length, so the cover complexity of $G$ is at most the fusion cover complexity of $f_G$; this yields lower bounds $\Omega(N)$ on the fusion cover complexity of the $2n$-variable Boolean functions $f_G$ of random graphs $G$.

## Proof sketch

(i) Here $U$ is the diagonal. The canonical semifilter at $(u,v)$, $u\ne v$, accepts the subsets of $U$ containing $(u,u)$ or $(v,v)$; a pair covers it only if one of $(u,u),(v,v)$ lies in $E\setminus H$ and the other in $H\setminus E$. So the pairs of a cover separate any two diagonal points by membership in their first components, and a cover of length $k$ labels the $2^n$ diagonal points injectively by $k$ bits; the upper bound comes from a circuit for inequality with $n$ AND gates. (ii) The upper bound follows from the construction of the graph by $N$ intersections, one per row. For the lower bound, the universal construction that rebuilds the graph from a cover of length $k$ needs only the inclusion relations among the $k$ pairs and the $2N$ rows and columns, which take $O(k(N+k))$ bits, while a random graph has description complexity $\Omega(N^2)$.

## Depends on

- [Semifilters and semifilter (fusion) covers](semifilters-and-fusion-covers.md)

## Sources

- Bruno P. Cavalar, Igor C. Oliveira, "Boolean Circuit Complexity and Two-Dimensional Cover Problems", ACM Transactions on Computation Theory, 2025 (Proposition 40, Theorem 37 and Lemma 39).
