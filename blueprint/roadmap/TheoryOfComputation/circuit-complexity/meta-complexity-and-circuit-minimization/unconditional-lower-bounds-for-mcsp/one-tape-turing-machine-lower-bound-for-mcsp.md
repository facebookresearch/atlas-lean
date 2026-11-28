# One-tape Turing machine lower bound for MCSP

A randomized one-tape Turing machine with a separate one-way input tape cannot compute $\mathrm{MCSP}[2^{\mu n}]$ in time $N^{1.99}$ for some constant $\mu<1$, nearly matching the best lower bounds known for this model.

Let $\mathrm{BPTIME}_1[t(N)]$ be the class of languages decided, with error at most $1/3$, by a two-sided-error randomized Turing machine with a one-way read-only input tape and one two-way read/write work tape running in time $t(N)$ on inputs of length $N$.

**Theorem (Cheraghchi–Hirahara–Myrisiotis–Yoshida).**

1. There is a constant $0<\mu<1$ such that $\mathrm{MCSP}[2^{\mu n}]\notin\mathrm{BPTIME}_1[N^{1.99}]$, where $N=2^n$.
2. For every oracle $O$ and every constant $1/2<\mu<1$ there is a constant $\mu'>0$ such that $\mathrm{MCSP}[2^{\mu n}]$ on truth tables of size $N$ is not in $\mathrm{BPTIME}_1^{O}[N^{1+\mu'}]$ by machines whose oracle queries all have length $N^{o(1)}$.

By contrast, a hardness magnification theorem implicit in McKay, Murray and Williams gives a constant $\mu_1>0$ such that $\mathrm{MCSP}[2^{\mu_1 n}]\notin\mathrm{DTIME}_1[N^{1.01}]$ would imply $\mathrm{P}\ne\mathrm{NP}$; item 1 has the much larger running time but needs a threshold exponent $\mu$ close to $1$. Item 2 shows that magnification proofs via near-linear-time oracle algorithms with short queries cannot reach thresholds $2^{\mu n}$ with $\mu>1/2$.

## Expansion

A pseudorandom generator whose outputs are truth tables of circuit size at most $s(n)$ and which fools a class $\mathcal{C}$ shows that $\mathrm{MCSP}[s]\notin\mathcal{C}$, since MCSP would accept every output and reject most uniform strings. Local generators of Viola, and generators for combinatorial rectangles and read-once branching programs of Forbes and Kelley, fool time-bounded one-tape machines (Lemma 20 and Theorem 21; Lemma 22 folds short oracle queries and fixed coins into the states of a deterministic machine) and have each output bit computable from a short part of the seed, which bounds the circuit size of their outputs.


Known unstated proof prerequisites needed before this node is ready for formalization:

- Viola's simulation of time-bounded one-tape Turing machines by read-once branching programs (Cheraghchi et al. Lemma 20)
- Forbes–Kelley pseudorandom generator for read-once branching programs (Cheraghchi et al. Theorem 21)

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Shannon: most Boolean functions need exponential circuits](../../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Sources

- Mahdi Cheraghchi, Shuichi Hirahara, Dimitrios Myrisiotis, Yuichi Yoshida, "One-Tape Turing Machine and Branching Program Lower Bounds for MCSP", *Theory of Computing Systems*, 2022, https://doi.org/10.1007/s00224-022-10113-9; theorem numbers from the conference version, *Symposium on Theoretical Aspects of Computer Science (STACS)*, 2021, https://doi.org/10.4230/LIPIcs.STACS.2021.23 (Theorems 1 to 3 and 16, Lemmas 14 and 15).
