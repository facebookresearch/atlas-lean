# Nondeterministic branching program lower bound for MCSP

Every nondeterministic, co-nondeterministic or parity branching program computing MCSP on $N$-bit truth tables has size at least $N^{1.5-o(1)}$. These are the first nontrivial bounds for MCSP against these models.

**Theorem (Cheraghchi–Hirahara–Myrisiotis–Yoshida).** The size of any nondeterministic, co-nondeterministic, or parity branching program computing MCSP is at least $N^{1.5-o(1)}$, where $N=2^n$ is the truth-table length.

Here size is the number of labeled edges. A nondeterministic program may have vertices of any outdegree, edges leaving one vertex that query different variables, and unlabeled edges; a computation that reaches a vertex with no edge consistent with the input rejects. Such a program accepts if some computation consistent with the input reaches the accepting sink; a co-nondeterministic program accepts if every computation consistent with the input does; a parity program accepts if the number of source-to-accepting-sink paths consistent with the input is odd.

Nečiporuk's method, which gives the corresponding bound for MKTP, does not apply directly to MCSP because the relation between circuit size and KT complexity is too loose; the proof instead uses pseudorandomness.

## Expansion

The pseudorandom generator of Impagliazzo, Meka and Zuckerman, analyzed for these models, has seed length $s^{2/3+o(1)}$ and fools nondeterministic, co-nondeterministic and parity branching programs of size $s$. Its outputs are truth tables of small circuit complexity, so a small program for MCSP would accept all of them while rejecting most uniformly random truth tables, which have large circuit complexity. Balancing the seed length against $N$ gives the size bound $N^{1.5-o(1)}$.


Expanding this node to full proof readiness requires planned proof-prerequisite pages for:

- Impagliazzo–Meka–Zuckerman pseudorandom generator for nondeterministic and parity branching programs (Cheraghchi et al., proof of Theorem 5)

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)

## Proof depends on

- [Shannon: most Boolean functions need exponential circuits](../../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Sources

- Mahdi Cheraghchi, Shuichi Hirahara, Dimitrios Myrisiotis, Yuichi Yoshida, "One-Tape Turing Machine and Branching Program Lower Bounds for MCSP", *Theory of Computing Systems*, 2022, https://doi.org/10.1007/s00224-022-10113-9; theorem numbers from the conference version, *Symposium on Theoretical Aspects of Computer Science (STACS)*, 2021, https://doi.org/10.4230/LIPIcs.STACS.2021.23 (Section 2.4, Theorem 5, Section 1.1.2).
