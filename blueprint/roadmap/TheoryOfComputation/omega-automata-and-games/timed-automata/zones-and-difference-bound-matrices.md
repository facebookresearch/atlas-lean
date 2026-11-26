# Zones and difference-bound matrices

Let $C = \{x_1, \dots, x_m\}$ be a set of clocks, as for [timed automata](timed-buchi-automata.md). A *zone* is a set of clock valuations in $\mathbb{R}_{\ge 0}^C$ defined by a clock
constraint; zones are convex. Adding a clock $x_0$ that is always $0$, a *difference-bound matrix* (DBM) is a $(m+1) \times (m+1)$ matrix $M$ with entries
in $\{\le, <\} \times \mathbb{Z}$, and it represents the zone of valuations $v$ with $v(x_i) - v(x_j) \prec_{i,j} M_{i,j}$ for all $i, j$, where $v(x_0) = 0$. The
*basic operations* are intersection, the time successors $\mathrm{Post}_{\ge 0}(Z) = \{v : \exists t \ge 0.\ v - t \in Z\}$, the time predecessors
$\mathrm{Pre}_{\ge 0}(Z)$, the reset $\mathrm{Reset}_R(Z)$ and its inverse $\mathrm{Unreset}_R(Z)$; together they compute the successors and predecessors of a set of valuations by an edge.

Each basic operation maps a DBM to a DBM and is computed in time $O(n^3)$ for an $n \times n$ DBM, by editing entries and running the Floyd–Warshall
all-pairs shortest-path algorithm, which also brings a DBM to a canonical form that is unique for its zone. The complement of a zone given by an
$n \times n$ DBM is a union (federation) of at most $n(n - 1)$ zones.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 11 (N. Markey and O. Sankur, "Timed games"): Section 11.2, the definitions of zones and difference-bound matrices with Example 11.4, the operations $\mathrm{Post}_{\ge 0}$, $\mathrm{Pre}_{\ge 0}$, $\mathrm{Reset}_R$ and $\mathrm{Unreset}_R$, Theorem 11.1 (complexity of basic operations on DBMs) and Theorem 11.2 (complement of DBMs).
