# LONG CHOICE and the class PLC of polynomial long choice for iterated pigeonhole arguments

**LONG CHOICE.** The universe is $U=\{0,1\}^n$. The input is a sequence of $n-1$ circuits $P_0,\dots,P_{n-2}$ of size $\mathrm{poly}(n)$, where $P_i$ takes $(i+2)n$ input bits and outputs one bit, i.e. is a predicate on $i+2$ objects. A solution is a sequence of $n+1$ distinct objects $a_0,\dots,a_n$ such that for every $i\in\{0,\dots,n-2\}$ the value $P_i(a_0,\dots,a_i,a_j)$ is the same for all $j>i$. **PLC** is the class of total search problems polynomial-time reducible to LONG CHOICE. UNARY LONG CHOICE restricts every $P_i$ to depend only on its last argument, and BINARY LONG CHOICE restricts $P_i$ to depend only on $a_i$ and its last argument.

The definition abstracts the proof of Ramsey's theorem: choose $a_0$ arbitrarily, split the remaining objects by the value of $P_0(a_0,\cdot)$, keep the majority side, choose $a_1$ from it, and so on.

## Depends on

- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)
- [Finite Ramsey theorem for pairs](../../../../Combinatorics/ramsey-theory/structural-ramsey/ramsey-two-uniform.md)

## Sources

- Amol Pasarkar, Christos Papadimitriou and Mihalis Yannakakis, "Extremal Combinatorics, Iterated Pigeonhole Arguments and Generalizations of PPP", ITCS (2023), arXiv:2209.07625.
