# Semidirect and wreath products of transformation semigroups

A *transformation semigroup* $(P, S)$ is a semigroup $S$ acting faithfully on a set $P$. Given a left action $(t, s) \mapsto t \cdot s$ of a semigroup $T$ on a semigroup
$S$ (written additively) by endomorphisms, the *semidirect product* $S * T$ is $S \times T$ with $(s, t)(s', t') = (s + t \cdot s', tt')$. The *wreath product* of transformation
semigroups $X = (P, S)$ and $Y = (Q, T)$ is $X \circ Y = (P \times Q, W)$, where $W$ consists of the pairs $(f, t)$ of a function $f : Q \to S$ and $t \in T$, acting by
$(p, q) \cdot (f, t) = (p + q \cdot f,\ q \cdot t)$, where the action of $S$ on $P$ is written $p + s$ and $q \cdot f$ stands for $f(q)$, with product $(f, t)(f', t') = (g, tt')$ where $q \cdot g = q \cdot f + (q \cdot t) \cdot f'$; the action is faithful. The wreath product $S \circ T$ of
semigroups is the semigroup of $(S^1, S) \circ (T^1, T)$; every semidirect product of $S$ and $T$ is a subsemigroup of $S \circ T$. In automata terms the wreath product
is the cascade of two automata.

## Sources

- J.-É. Pin, *Mathematical Foundations of Automata Theory*, lecture notes, version of March 24, 2025, <https://www.irif.fr/~jep/PDF/MPRI/MPRI.pdf>: Chapter XVIII, Section 1 (semidirect product) and Section 2 (wreath product, the action (2.1), its faithfulness and the product on $W$, and Proposition XVIII.2.1).
