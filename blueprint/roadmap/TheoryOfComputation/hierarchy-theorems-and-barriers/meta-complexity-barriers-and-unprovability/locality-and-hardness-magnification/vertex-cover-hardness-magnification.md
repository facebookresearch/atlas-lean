# Hardness magnification for k-Vertex-Cover against AC0

Oliveira and Santhanam show that, for polylogarithmic $k$, a barely superlinear lower bound for $k$-Vertex-Cover against constant-depth circuits of each fixed depth would separate NP from non-uniform $\mathsf{NC}^1$.

Let $k(n) = (\log n)^C$ for an arbitrary fixed $C \in \mathbb{N}$, and let $k$-Vertex-Cover be the problem of deciding whether an $n$-vertex graph, given by its adjacency matrix of bit length $m = \Theta(n^2)$, has a vertex cover of size at most $k(n)$. If for every $d \ge 1$ there is $\varepsilon > 0$ such that $k\text{-Vertex-Cover} \notin \mathsf{AC}^0_d[m^{1+\varepsilon}]$, then $\mathsf{NP} \not\subseteq \mathsf{NC}^1$, where $\mathsf{NC}^1$ is the non-uniform class of languages decided by polynomial-size De Morgan formulas, equivalently by polynomial-size fan-in-two circuits of depth $O(\log n)$.

## Proof sketch

The proof is by contraposition and uses kernelization. A kernel maps an instance with parameter $k$ to an equivalent Vertex-Cover instance of size $\mathrm{poly}(k)$. If $\mathsf{NP} \subseteq \mathsf{NC}^1$ (non-uniformly), then NP has sub-exponential-size circuits of some constant depth, so the kernel instance of size $\mathrm{poly}((\log n)^C)$ is solved by constant-depth circuits of size at most $m$. The technical part implements the kernelization itself by constant-depth circuits of almost-linear size. Under ETH, $k$-Vertex-Cover is not solvable in time $2^{o(k)}\mathrm{poly}(m)$, so the hypothesis is expected to hold with room to spare.

## Depends on

- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class AC^0](../../../complexity-classes/time-and-space-complexity-classes/ac0.md)

## Proof depends on

- [Buss's kernel for vertex cover](../../../complexity-classes/parameterized-vertex-cover/buss-s-kernel-for-vertex-cover.md)

## Sources

- Igor C. Oliveira and Rahul Santhanam, "Hardness Magnification for Natural Problems", *FOCS* 2018, DOI 10.1109/FOCS.2018.00016 (Theorem 7, Section 1, with the non-uniform reading of $\mathsf{NC}^1$ in its proof idea; proof in the full version cited there).
