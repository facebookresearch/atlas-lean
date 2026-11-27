# MCSP is not hard under local reductions

Although SAT and most NP-complete problems are complete under reductions that compute each output bit in polylogarithmic time, no reduction computing each output bit in time $n^{\delta}$ with $\delta<1/2$ reduces even PARITY to MCSP. So MCSP is unconditionally not NP-hard under such local reductions.

**Local reductions.** For $t:\mathbb{N}\to\mathbb{N}$, an algorithm $R$ is a $\mathrm{TIME}(t(n))$ reduction from $L$ to $L'$ if there is a constant $c\ge1$ such that for every $x$: $R(x,i)$ has random access to $x$ and runs in time $O(t(|x|))$ for all $i\in\{0,1\}^{\lceil 2c\log_2|x|\rceil}$; there is $\ell_x\le|x|^c+c$ with $R(x,i)\in\{0,1\}$ for $i\le\ell_x$ and $R(x,i)=\star$ for $i>\ell_x$; and $x\in L$ iff $R(x,1)\cdots R(x,\ell_x)\in L'$. A randomized version also takes $O(t(|x|))$ random bits $r$ and must be correct with probability at least $1-p$ for a constant $p<1/2$.

**Theorem (Murray–Williams).**

1. For every $\delta<1/2$ there is no $\mathrm{TIME}(n^{\delta})$ reduction from PARITY to MCSP; hence MCSP is not $\mathrm{AC}^0[2]$-hard under $\mathrm{TIME}(n^{\delta})$ reductions.
2. For every $\delta<1/5$ there is no $\mathrm{TIME}(n^{\delta})$ randomized reduction from PARITY to MCSP.

By contrast, SAT, Vertex Cover, Independent Set, Hamiltonian Path and 3-Coloring are NP-complete under $\mathrm{TIME}(\mathrm{poly}(\log n))$ reductions.

## Expansion

MCSP instances list whole truth tables, and a local reduction prints each bit of its output from little information, so the output truth tables have small circuits, and the size parameter is small too or the instance is trivially yes. First make the reduction natural: answer "no" to every bit query made while computing the size parameter, and pad the PARITY instance with zeros placed to agree with those answers. Then the produced instances can be solved by searching small circuits, and this search, combined with the reduction, would give depth-three circuits of size $2^{\tilde O(n^{\delta})}$ for PARITY (depth five in the randomized case), contradicting Håstad's bound that depth-$d$ circuits for PARITY need size $2^{\Omega(n^{1/(d-1)})}$; this is where $\delta<1/2$ and $\delta<1/5$ come from.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Parity](../../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)
- [AC0(m): constant-depth circuits with MOD gates](../../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)

## Proof depends on

- [Depth-d circuit size of parity](../../lower-bounds-for-ac0-circuits/depth-d-circuit-size-of-parity.md)

## Sources

- Cody D. Murray, R. Ryan Williams, "On the (Non) NP-Hardness of Computing Circuit Complexity", *Theory of Computing* 13(4), 2017, https://doi.org/10.4086/toc.2017.v013a004 (Definitions 1.1 and 1.4, Proposition 1.2, Theorems 1.3 and 1.5, Theorem 2.1, Section 3).
