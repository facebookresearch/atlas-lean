# Rectangle-DAGs (dag-like communication protocols)

Let $S \subseteq \mathcal{X} \times \mathcal{Y} \times \mathcal{O}$ be a total two-party search problem. A **rectangle-DAG** for $S$ is a directed acyclic graph of out-degree at most $2$ in which each node $v$ is labeled by a combinatorial rectangle $R_v \subseteq \mathcal{X} \times \mathcal{Y}$ such that: the root is labeled $\mathcal{X} \times \mathcal{Y}$; each non-sink $v$ with children $u, w$ satisfies $R_v \subseteq R_u \cup R_w$; and each sink $v$ is labeled by an output $o_v$ with $R_v \times \{o_v\} \subseteq S$. Its **size** is the number of nodes. Tree-like rectangle-DAGs are ordinary protocols; general rectangle-DAGs model the communication content of monotone circuits and of dag-like proofs.

## Depends on

- [Communication cost of a protocol](../deterministic-communication-protocols/depth.md)

## Sources

- A. A. Razborov, "Unprovability of lower bounds on circuit size in certain fragments of bounded arithmetic", Izvestiya Mathematics 59 (1995) 205-227.
- D. Sokolov, "Dag-like communication and its applications", CSR (2017).
- P. Pudlák, "On extracting computations from propositional proofs", FSTTCS (2010).
- A. Garg, M. Göös, P. Kamath, D. Sokolov, "Monotone circuit lower bounds from resolution", STOC (2018); Theory of Computing 16 (2020).
