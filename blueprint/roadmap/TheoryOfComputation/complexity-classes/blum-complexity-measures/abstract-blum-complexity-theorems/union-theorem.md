# McCreight–Meyer union theorem

For every Blum measure $\Phi$ and every uniformly computable family of total bounds $T_0\le T_1\le\cdots$ increasing pointwise in the index, there is a single total computable bound $t$ with

$$
C_t=\bigcup_{i}C_{T_i}.
$$

For example, for running time on Turing machines there is a computable $t$ with $C_t=\mathsf{P}$.

## Proof sketch

Define $t(n)$ by a diagonal process: guess for each program a level $i$ and lower the guess when the program exceeds $T_i$ at some argument; set $t(n)=T_{j(n)}(n)$ where $j(n)$ is the least level still 'owed' to programs $\le n$; every member of some $C_{T_i}$ is eventually bounded by $t$, and $t$ grows slowly enough to admit no new functions.

## Depends on

- [Blum complexity measure](../blum-measure.md)
- [Blum complexity class](../blum-class.md)

## Sources

- Edward M. McCreight and Albert R. Meyer, "Classes of Computable Functions Defined by Bounds on Computation: Preliminary Report", Proceedings of the First Annual ACM Symposium on Theory of Computing (STOC '69), 1969.
- Piergiorgio Odifreddi, "Classical Recursion Theory, Volume II", North-Holland, 1999, Theorem VII.3.7.
