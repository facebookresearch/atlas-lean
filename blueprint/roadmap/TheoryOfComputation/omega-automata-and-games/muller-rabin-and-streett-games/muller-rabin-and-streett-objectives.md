# Muller, Rabin and Streett objectives

Fix a finite set $C = \{1, \dots, d\}$ of *colors*, and for an infinite sequence $\rho \in C^\omega$ let $\mathrm{Inf}(\rho)$ be the set of
colors occurring infinitely often in $\rho$. In a game whose arena colors its vertices or edges by $C$, an objective on $C^\omega$
is the condition satisfied by the plays whose sequence of colors lies in it.

- For a family $\mathcal{F} \subseteq 2^C$, the *Muller objective* is $\mathrm{Muller}(\mathcal{F}) = \{\rho \in C^\omega : \mathrm{Inf}(\rho) \in \mathcal{F}\}$. Its
  complement is $\mathrm{Muller}(2^C \setminus \mathcal{F})$.
- For pairs $(R_1, G_1), \dots, (R_k, G_k)$ of subsets of $C$, the *Streett objective* is the set of $\rho$ such that for every $i$,
  if $R_i \cap \mathrm{Inf}(\rho) \ne \emptyset$ then $G_i \cap \mathrm{Inf}(\rho) \ne \emptyset$ (every request made infinitely often is answered
  infinitely often), and the *Rabin objective* is its complement: some $i$ has $R_i \cap \mathrm{Inf}(\rho) \ne \emptyset$ and
  $G_i \cap \mathrm{Inf}(\rho) = \emptyset$.
- The *parity objective* is the set of $\rho$ in which the largest color occurring infinitely often is even.

A family $\mathcal{F}$ is closed under union if and only if $\mathrm{Muller}(\mathcal{F})$ is a Streett objective; consequently
$\mathrm{Muller}(\mathcal{F})$ is a Rabin objective if and only if $2^C \setminus \mathcal{F}$ is closed under union.

## Depends on

- [Arenas, strategies and memory structures](arenas-strategies-and-memory-structures.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 3 (N. Fijalkow and F. Horn, "Regular games"): Section 3.1, the definitions of Muller, Streett and Rabin objectives and Lemma 3.1 (Streett objectives as the Muller objectives with $\mathcal{F}$ closed under union).
- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 1 (N. Fijalkow, "Introduction"): the definition of the parity objective in Section 1.3.
