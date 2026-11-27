# Zones and difference-bound matrices

Let $C = \{x_1, \dots, x_m\}$ be a finite set of clocks. An *atomic clock constraint* is $k \preceq x \preceq' l$ or $k \preceq x - y \preceq' l$ with $x, y \in C$,
$k, l \in \mathbb{Z} \cup \{-\infty, +\infty\}$ and $\preceq, \preceq' \in \{<, \le\}$, and a *clock constraint* is a conjunction of atomic clock constraints. Unlike the clock
constraints of [timed automata](timed-buchi-automata.md), these have no negation, integer bounds only, and may bound differences of clocks. A *zone* is a set of
clock valuations in $\mathbb{R}_{\ge 0}^C$ defined by such a clock constraint; zones are convex. Adding a clock $x_0$ that is always $0$, a *difference-bound matrix*
(DBM) is a $(m+1) \times (m+1)$ matrix $M$ with entries in $(\{\le, <\} \times \mathbb{Z}) \cup \{(<, +\infty)\}$, and it represents the zone of valuations $v$ with
$v(x_i) - v(x_j) \prec_{i,j} M_{i,j}$ for all $i, j$, where $v(x_0) = 0$ and the entry $(<, +\infty)$ imposes no constraint; it is needed, for example, for the unbounded
time successors of a nonempty zone. The
*basic operations* are intersection, the time successors $\mathrm{Post}_{\ge 0}(Z) = \{v : \exists t \ge 0.\ v - t \in Z\}$, the time predecessors
$\mathrm{Pre}_{\ge 0}(Z)$, the reset $\mathrm{Reset}_R(Z)$ and its inverse $\mathrm{Unreset}_R(Z)$; together they compute the successors and predecessors of a set of valuations by an edge.

Each basic operation maps a DBM to a DBM and is computed in time $O(n^3)$ for an $n \times n$ DBM, by editing entries and running the Floyd–Warshall
all-pairs shortest-path algorithm, which also brings a DBM to a canonical form: intersect each diagonal entry with $(\le, 0)$ and add the implicit bounds $0 - x_i \le 0$, then close; if the closure has
a diagonal entry below $(\le, 0)$ the zone is empty and the DBM is mapped to one empty representative, and otherwise the closure, with its diagonal set to $(\le, 0)$,
is unique for its nonempty zone. The complement of a zone given by an $n \times n$ DBM with diagonal $(\le, 0)$ is a union (federation) of at most $n(n - 1)$ zones for $n \ge 2$.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 11 (N. Markey and O. Sankur, "Timed games"): Section 11.2, the definitions of zones and difference-bound matrices with Example 11.4, the operations $\mathrm{Post}_{\ge 0}$, $\mathrm{Pre}_{\ge 0}$, $\mathrm{Reset}_R$ and $\mathrm{Unreset}_R$, Theorem 11.1 (complexity of basic operations on DBMs) and Theorem 11.2 (complement of DBMs).
