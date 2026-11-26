# Difference logic and negative cycles

Let $F$ be a conjunction of atoms $x - y \le c$ with variables $x, y$ and constants $c \in \mathbb Q$ (difference logic over the rationals), or $c \in \mathbb Z$ with integer-valued variables; a variable $x_0$ fixed to $0$ may be used to express bounds $x \le c$ as $x - x_0 \le c$. Let $G$ be the weighted directed graph whose vertices are the variables of $F$, with an edge from $x$ to $y$ of weight $c$ for each atom $x - y \le c$. Then $F$ is unsatisfiable if and only if $G$ has a cycle of negative total weight. This can be checked in time $O(|V| \cdot |E|)$ with the Bellman–Ford algorithm, run from an added vertex with an edge of weight $0$ to every vertex.

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 1.8, difference logic and the negative-cycle criterion with the Bellman–Ford bound, pp. 20–21.
