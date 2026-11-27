# Alternating time and space classes ATIME, ASPACE, AP, APSPACE and AL

For $t, s:\mathbb{N}\to\mathbb{N}$, $\mathsf{ATIME}(t)$ is the class of languages $L\subseteq\{0,1\}^*$ decided by some alternating Turing machine all of whose computation paths on inputs of length $n$ halt within $c_1 t(n)+c_2$ steps, for constants $c_1,c_2$; $\mathsf{ASPACE}(s)$ is the class decided by an alternating machine every branch of which halts and which uses at most $c_1 s(n)+c_2$ work cells in every reachable configuration.

The derived classes are

$$
\mathsf{AP}=\bigcup_{k}\mathsf{ATIME}(n^k),\qquad \mathsf{APSPACE}=\bigcup_k\mathsf{ASPACE}(n^k),\qquad \mathsf{AL}=\mathsf{ASPACE}(\log n).
$$

Both families are monotone in the bound up to affine changes, and $\mathsf{ATIME}(t)\subseteq\mathsf{ASPACE}(t)$ since a machine cannot visit more cells than it takes steps.

## Depends on

- [Alternating Turing machine](alternating-turing-machine.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
