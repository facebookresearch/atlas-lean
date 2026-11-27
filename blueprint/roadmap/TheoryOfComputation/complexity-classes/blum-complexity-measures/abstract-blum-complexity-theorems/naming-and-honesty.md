# Naming and honesty theorems

(Naming, McCreight–Meyer.) For every Blum measure $\Phi$ there is a **measured** family $(\nu_i)$ of partial computable functions (the predicate $\nu_i(n)=m$ is decidable uniformly in $i$, $n$ and $m$) such that every complexity class $C_t$ of a total computable $t$ equals $C_{\nu_i}$ for some $i$. (Honesty.) There is one total computable $g$ such that every such class $C_t$ has a **$g$-honest** name $t'$ with $C_{t'}=C_t$: some program computes $t'$ with cost at most $g(n,t'(n))$ for almost all $n$.

## Proof sketch

Naming: modify the union-theorem construction uniformly in a program index for $t$, producing functions whose graphs are decidable. Honesty: for a measured family, the cost of computing $\nu_i(n)$ by searching for $m$ with $\nu_i(n)=m$ is bounded by a computable function of $n$ and the output, uniformly in $i$.

## Depends on

- [Blum complexity measure](../blum-measure.md)
- [Blum complexity class](../blum-class.md)

## Proof depends on

- [McCreight–Meyer union theorem](union-theorem.md)

## Sources

- Piergiorgio Odifreddi, "Classical Recursion Theory, Volume II", North-Holland, 1999, Theorem VII.3.6, Definition VII.2.13.
- Edward M. McCreight and Albert R. Meyer, "Classes of Computable Functions Defined by Bounds on Computation: Preliminary Report", Proceedings of the First Annual ACM Symposium on Theory of Computing (STOC '69), 1969.
