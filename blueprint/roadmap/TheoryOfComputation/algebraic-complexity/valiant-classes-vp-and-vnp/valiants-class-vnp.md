# Valiant's class VNP (p-definable families)

A family $f$ over $K$ is in $\mathsf{VNP}_K$ (is *p-definable*) if there are a polynomially bounded $m(n)$ and a family $g\in\mathsf{VP}_K$ with

$$
f_n(x)=\sum_{e\in\{0,1\}^{m(n)}}g_n(x,e)
$$

for all $n$, where the last $m(n)$ variables of $g_n$ are substituted by $0/1$ values. A family $h$ is *$\mathsf{VNP}$-complete* if $h\in\mathsf{VNP}_K$ and every family in $\mathsf{VNP}_K$ is a p-projection of $h$.

## Depends on

- [Valiant's class VP](valiants-class-vp.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Peter Bürgisser, "Completeness and Reduction in Algebraic Complexity Theory", Springer, 2000.
