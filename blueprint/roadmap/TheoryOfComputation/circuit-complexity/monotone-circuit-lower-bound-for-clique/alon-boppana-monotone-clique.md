# Alon–Boppana: monotone circuits for clique need exponential size

There are $c > 0$ and $n_0$ such that for every $n \ge n_0$, with $s = \lfloor (n/(8\log_2 n))^{2/3} \rfloor$, every well-formed monotone circuit (input, and, or gates) on $n^2$ adjacency bits that computes [$\mathrm{CLIQUE}(n, s)$](clique-of-size.md) has at least $\exp(c\,(n/\log_2 n)^{1/3})$ gates.

Alon and Boppana obtained this by choosing different approximating lattices in Razborov's method. Their bound counts gates of fan-in two. Inputs here are themselves gates of the list, so a gate refers to at most $g$ distinct earlier gates, and a circuit with $g$ gates of any fan-in has a fan-in-two equivalent with at most $g^2$ gates, which only changes $c$.

## Background

- [Razborov: monotone circuits for clique need superpolynomial size](razborov-monotone-clique.md): the original bound $n^{\Omega(\log n)}$ for cliques of size about $(\log n)/4$.

## Sources

- N. Alon and R. B. Boppana, "The monotone circuit complexity of Boolean functions", Combinatorica 7 (1987), 1-22, Section 1 (statement; logarithms base 2) and Section 3.
