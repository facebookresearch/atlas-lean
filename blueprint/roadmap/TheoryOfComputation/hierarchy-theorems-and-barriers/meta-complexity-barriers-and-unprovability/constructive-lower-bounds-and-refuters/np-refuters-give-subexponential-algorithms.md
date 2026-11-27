# Uniform refuters against co-nondeterministic circuits put NP in subexponential time

If some NP language has a uniform $2^{O(n)}$-time algorithm that, given any co-nondeterministic circuit of size $2^{n^\delta}$, outputs an input where the circuit is wrong, then every NP language is decidable in time $2^{n^\varepsilon}$ for every $\varepsilon > 0$. Constructive lower bounds of this kind therefore imply upper bounds.

Let $L \in \mathsf{NP}$ and $\delta > 0$. Suppose there is an algorithm $R(1^n, D)$ such that, for every co-nondeterministic circuit $D$ on $n$ input variables and of size at most $2^{n^\delta}$, $R(1^n, D)$ runs in time $2^{O(n)}$ and outputs $w \in \{0,1\}^n$ with $D(w) \ne L(w)$. Then for every $L' \in \mathsf{NP}$ and every constant $\varepsilon > 0$, $L' \in \mathsf{DTIME}[2^{n^{\varepsilon}}]$.

## Proof sketch

Let $L \in \mathsf{NTIME}[n^d]$, let $L'$ be decided by a nondeterministic machine in time $n^{c'}$, and choose a small enough constant $\gamma > 0$ depending on $d$ and $\varepsilon$. On input $x$ of length $n$, build a co-nondeterministic circuit $E'$ of size $n^{2c'}$ for the complement of $L'$ and the circuit $D_x(y)$ on $m = n^\gamma$ inputs that ignores $y$ and outputs $E'(x)$; its size $n^{2c'} = m^{2c'/\gamma}$ is at most $2^{m^\delta}$ for large $m$. Compute $w = R(1^m, D_x)$ in time $2^{O(n^\gamma)}$ and output $L(w)$ by brute force in time $2^{O(n^{\gamma d})} \le 2^{n^\varepsilon}$. Since $L(w) = 1 - D_x(w) = 1 - E'(x) = L'(x)$, the answer is correct. The proof only needs the refuter on circuits of size $n^{\alpha(n)}$ for some $\alpha(n) \to \infty$, as Chen, Li and Oliveira remark; Oliveira's survey states the lemma with size $n^{\log n}$. This is the simplest instance of the phenomenon behind unprovability results in $\mathsf{PV}$: a provable lower bound must be constructive, and constructive lower bounds yield algorithms.

## Depends on

- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [Deterministic time classes on multi-tape machines](../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

None.

## Sources

- Lijie Chen, Jiatu Li and Igor C. Oliveira, "On the Unprovability of Circuit Size Bounds in Intuitionistic $\mathsf{S}^1_2$", *Logical Methods in Computer Science* 21(3), 2025, 26:1–26:20, DOI 10.46298/lmcs-21(3:26)2025, arXiv:2404.11841v5 (Lemma 3.1, Section 3, with its proof and footnote 7).
- Igor C. Oliveira, "SIGACT News Complexity Theory Column 124: Meta-Mathematics of Computational Complexity Theory", *ACM SIGACT News* 56(1), 2025, DOI 10.1145/3726856.3726862, arXiv:2504.04416v1 (Lemma 5.7, Section 5.2.1, as background).
