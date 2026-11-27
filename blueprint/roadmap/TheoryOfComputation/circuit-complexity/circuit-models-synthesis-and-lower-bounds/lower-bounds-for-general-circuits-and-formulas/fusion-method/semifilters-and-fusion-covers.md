# Semifilters and semifilter (fusion) covers

Let $\Gamma$ be a finite set, $T\subseteq\Gamma$ a target set with $T\ne\emptyset$ and $T\ne\Gamma$, and $S_1,\dots,S_n\subseteq\Gamma$ supplied sets; put $U=\Gamma\setminus T$. A *semifilter* over $U$ is a nonempty family $F$ of subsets of $U$ that is upward closed and does not contain $\emptyset$ (intersection-closure is not required). $F$ is *above* $u\in T$ if $S_i\cap U\in F$ for every supplied set $S_i$ containing $u$. A pair $(E,H)$ of subsets of $U$ *covers* (defeats) $F$ if $E\in F$, $H\in F$ and $E\cap H\notin F$, that is, $F$ does not preserve the pair. A *pair cover* of $(T;S_1,\dots,S_n)$ is a family of pairs of subsets of $U$ covering every semifilter over $U$ that is above some element of $T$; the *cover complexity* $\rho(T;S_1,\dots,S_n)$ is the least size of a pair cover. For a Boolean function $f$ the relevant instance is $T=f^{-1}(1)\subseteq\{0,1\}^n$ with the $2n$ literal sets as supplied sets, so $U=f^{-1}(0)$.

## Sources

- Alexander A. Razborov, "On the Method of Approximations", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing, 167–176, 1989.
- Mauricio Karchmer, "On Proving Lower Bounds for Circuit Size", Proceedings of the 8th Annual Structure in Complexity Theory Conference, 112–118, 1993.
- Avi Wigderson, "The Fusion Method for Lower Bounds in Circuit Complexity", in Combinatorics, Paul Erdős is Eighty, Bolyai Society Mathematical Studies, 453–467, 1993.
- Bruno P. Cavalar, Igor C. Oliveira, "Boolean Circuit Complexity and Two-Dimensional Cover Problems", ACM Transactions on Computation Theory, 2025 (Definitions 18–21).
